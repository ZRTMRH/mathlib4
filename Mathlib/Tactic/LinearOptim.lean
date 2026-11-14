/-
Copyright (c) 2025 Runtian Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuli Chen, Robert Y. Lewis, Heather Macbeth, Siqing Zhang, Runtian Zhou
-/
module

public import Mathlib.Lean.Quote
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Optimize

/-!
# Linear Optimization Tactics

This file implements `maximize` and `minimize` tactics that find upper and lower
bounds for linear expressions given linear constraints using the simplex algorithm.
The tactics accept expressions in linearly ordered fields only. The bounds are optimal with respect
to the facts that `linarith` uses: the hypotheses after `linarith`'s preprocessing, in which
nonlinear terms such as `x * y` are treated as atoms.

## Main declarations

* `maximize` - Finds an upper bound for a linear expression
* `minimize` - Finds a lower bound for a linear expression
* `parseLinarithStructure` - Turns the hypotheses into the comparisons that `linarith` uses
* `preprocessLinearOptim` - Converts constraints to matrix for simplex
* `computeOptimalBound` - Core function computing optimal bounds

## Implementation

The `maximize` and `minimize` tactics work by:
1. Parsing the linear constraints and target expression using `parseLinarithStructure`
2. Converting them to matrix form suitable for the simplex algorithm via `preprocessLinearOptim`
3. Finding the optimal solution using `computeOptimalBound` which calls `simplexOptimalBound`
4. Suggesting a `have` statement with the computed bound that can be proved with `linarith`

The tactics handle the duality between maximization and minimization by transforming
`minimize e` into `maximize -e` and then negating the result. The implementation uses
a dummy variable trick to extract scaling factors introduced by the preprocessing pipeline.
-/

public meta section

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta
open Mathlib.Tactic.Linarith Mathlib.Tactic.Linarith.SimplexAlgorithm
open Qq

namespace Mathlib.Tactic.LinearOptim

section Preprocessing

/-- Turns the hypotheses in the local context, together with a dummy hypothesis `H`, into the
linear comparisons that `linarith` would use.

The caller creates the dummy hypothesis `H : e < z`, where `z` is a fresh variable, to capture how
the expression `e` is transformed. Preprocessing turns it into `e - z < 0`, which `cancelDenoms`
may scale to `k*e - k*z < 0`; the coefficient `-k` of `z` gives the scaling factor `k`.

The comparison coming from `H` is the only one that mentions `z`, so `z` is a variable that occurs
in it and in no other comparison. Any other such variable is a part of `e` that no hypothesis
constrains, so no bound on `e` follows from the hypotheses (in which nonlinear terms such as
`x * y` are atoms): either `e` is unbounded or the hypotheses are inconsistent. In that case this
function returns `none`, and the caller tells the two apart.

Otherwise it returns `some (comps, maxVar, goalScalingFactor) : List Comp × ℕ × ℤ` where:
- `comps` are the comparisons with the dummy variable removed: first the comparison `-1 < 0` added
  by `getLinearCombinations`, last the one coming from `H`
- `maxVar` is the maximum variable index (after removing the dummy variable)
- `goalScalingFactor` is the extracted scaling factor `k` -/
def parseLinarithStructure (ty H : Expr) (z : FVarId)
    (cfg : TransparencyMode := .reducible) : MetaM (Option (List Comp × ℕ × ℤ)) := do
  let hyps := H :: (← getLocalHyps).toList
  -- Preprocess with the preprocessors that `linarith` uses in its default configuration (see
  -- `Linarith.runLinarith`), so that the bound is computed from the same facts that `linarith`
  -- later uses to prove it. In particular, this adds the facts `0 ≤ (n : K)` for the casts of
  -- natural numbers. The preprocessors need a goal, and it has to live in the current context,
  -- which contains `z`.
  let pps := Linarith.splitConjunctions.globalize.branching :: Linarith.defaultPreprocessors
  let g ← mkFreshExprMVar (mkConst ``False)
  let [(_, es)] ← Linarith.preprocess pps g.mvarId! hyps
    | throwError "linear optimization: internal error: preprocessing did not give exactly one case"
  -- As in `linarith`, compare the types up to definitional equality: `ty` may be an assigned
  -- metavariable, e.g. after `refine fun x => ?_`.
  let hypSet ← es.filterM fun h => do isDefEq ty (← typeOfIneqProof h)
  let (comps, maxVar, inputs) ← getLinearCombinations cfg hypSet
  -- Find the comparison coming from `H`: its hypothesis is the only one mentioning `z`.
  let mentionsZ ← hypSet.mapM fun h => return (← instantiateMVars (← inferType h)).containsFVar z
  let some hIdx := mentionsZ.idxOf? true
    | throwError "linear optimization: internal error: the dummy hypothesis was lost"
  let some goalPos := inputs.findIdx? (·.2 == some hIdx)
    | throwError "linear optimization: internal error: the dummy hypothesis has no linear form"
  let goalComp := comps[goalPos]!
  let others := comps.eraseIdx goalPos
  -- The variables of `goalComp` that occur in no other comparison.
  match goalComp.coeffs.filter fun (v, _) => others.all fun c => !c.coeffs.any (·.1 == v) with
  | [(zIdx, negScalingFactor)] =>
    if 0 ≤ negScalingFactor then
      throwError "linear optimization: internal error: scaling factor {-negScalingFactor}"
    -- Remove `z`, renumbering the variables after it.
    let removeZ (c : Comp) : Comp :=
      { c with coeffs := c.coeffs.filterMap fun (v, a) =>
          if v == zIdx then none else some (if zIdx < v then v - 1 else v, a) }
    return some ((others ++ [goalComp]).map removeZ, maxVar - 1, -negScalingFactor)
  | [] => throwError "linear optimization: internal error: the dummy variable occurs elsewhere"
  | _ => return none

end Preprocessing


section MatrixPreprocessing

/-- Converts linear constraints into a matrix suitable for the simplex algorithm.

This function takes the parsed constraints from `parseLinarithStructure` and builds
a matrix for `simplexOptimalBound`. The matrix has dimensions `(maxVar + 1) × (rr.length + 1)`.

The function reorders and transforms coefficients:
- The objective function `rH` goes to the last column with negated coefficients
- The last comparison of `rr`, which is the comparison `-1 < 0`, goes to the first column
- The other comparisons keep their relative positions

This specific ordering prepares the matrix for the simplex algorithm's expected format. -/
def preprocessLinearOptim (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType]
    (rH : Linarith.Comp) (rr : List Linarith.Comp) (maxVar : ℕ) :
    matType (maxVar + 1) (rr.length + 1) :=
  let hyps := rr ++ [rH]
  let values : List (ℕ × ℕ × ℚ) :=
    hyps.foldlIdx (init := []) fun idx cur comp =>
    if idx == rr.length then
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx, c * -1)
    else if idx == rr.length - 1 then
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, 0, c)
    else
      cur ++ comp.coeffs.map fun (var, c) =>
        (var, idx + 1, c)
  ofValues values


end MatrixPreprocessing

section BoundComputation

/-- Whether `linarith` can prove `False` from the hypotheses in the context of `g`, together with
the facts that its preprocessing derives from the expression `e`, such as `0 ≤ (n : K)` for the
casts of natural numbers in `e`. These facts are also used to compute the bound on `e`. -/
def hypothesesInconsistent (g : MVarId) (e : Expr) : MetaM Bool := g.withContext do
  let goal ← mkFreshExprMVar (mkConst ``False)
  succeeds <| Linarith.linarith false [← mkEqRefl e] {} goal.mvarId!

/-- Compute the optimal bound (upper bound for maximization, lower bound for minimization).

This function implements the core optimization logic, using the duality principle:
- For maximization: directly find max(e) using the simplex algorithm
- For minimization: find min(e) by computing max(-e) and negating the result

The function creates a dummy variable `z` and hypothesis `target < z` to capture
scaling factors from preprocessing. After running the simplex algorithm, it adjusts
the result by the scaling factor to get the actual bound.

The duality transformation `min(e) = -max(-e)` allows us to handle both maximize
and minimize with a single simplex implementation.

Returns the optimal bound as a rational number, or an error if the problem is
unbounded or infeasible. -/
def computeOptimalBound (e_exp : Expr) (isMaximize : Bool) (g : MVarId) :
    MetaM (Except LinearOptimException Rat) := g.withContext do
  let ⟨u, ty, e_exp⟩ ← inferTypeQ' e_exp
  -- The bound is the optimum of a linear program over `ℚ`, which is the optimum over `ty` only
  -- when `ty` is a linearly ordered field: over `ℤ`, for instance, it need not be an integer.
  let notField := m!"{if isMaximize then "maximize" else "minimize"} only works over linearly \
    ordered fields, such as ℚ and ℝ, but {e_exp} has type {ty}."
  let _i ← try synthInstanceQ q(Field $ty) catch _ => throwError notField
  let _i ← try synthInstanceQ q(LinearOrder $ty) catch _ => throwError notField
  let _i ← try synthInstanceQ q(IsStrictOrderedRing $ty) catch _ => throwError notField
  assumeInstancesCommute
  -- To find max(e), we run the pipeline on `e`.
  -- To find min(e), we run the pipeline on `-e` and use the identity min(e) = -max(-e).
  let target_exp := if isMaximize then e_exp else q(-$e_exp)
  -- No bound follows from the hypotheses: either the expression is unbounded or the hypotheses are
  -- inconsistent. Tell the two apart with `linarith`.
  let unboundedOrInconsistent : MetaM (Except LinearOptimException Rat) := do
    return .error (if ← hypothesesInconsistent g e_exp then .inconsistent else .unbounded)
  -- The dummy hypothesis is always `< z` (for a new dummy variable `z`) to ensure the scaling
  -- factor `k` is positive and that the Comp object represents `k*E`.
  withLocalDecl .anonymous .default ty fun (z : Q($ty)) ↦ do
  let H := q(show $target_exp < $z from sorry)
  let some (comps, maxVar, scalingFactor) ← parseLinarithStructure ty H z.fvarId!
    | unboundedOrInconsistent
  let rH :: rr := comps.reverse | failure
  let A := preprocessLinearOptim DenseMatrix rH rr maxVar
  match ← simplexOptimalBound A with
  | .ok r_opt =>
    let k_q : ℚ := scalingFactor
    -- This derivation is based on the solver pipeline.
    -- The pipeline takes a Comp for `k*E` and returns `r_opt = min(-(k*E))`.
    -- This can be solved to show that `max(E) = (- r_opt) / k`.
    let max_of_target := (- r_opt) / k_q
    if isMaximize then
      -- The target was `e`, so we have found `max(e)`.
      return Except.ok max_of_target
    else
      -- The target was `-e`. We found `max(-e)`.
      -- So we return `-max(-e)` to get `min(e)`.
      return Except.ok (-max_of_target)
  | .error .unbounded => unboundedOrInconsistent
  | .error e => return Except.error e


end BoundComputation


section TacticImplementation

/-- Runs `maximize e` (if `isMaximize`) or `minimize e`, naming the new hypothesis `h` if given:
computes the optimal bound, suggests a `have` stating it, and runs that `have`. The bound is
strict if `linarith` can prove the strict version. -/
def runLinearOptim (isMaximize : Bool) (e : Term) (h : Option Ident) : TacticM Unit :=
  withMainContext do
  let noBound (reason : String) : MessageData :=
    if isMaximize then m!"maximize: an upper bound cannot be produced for {e}.\n    {reason}"
    else m!"minimize: a lower bound cannot be produced for {e}.\n    {reason}"
  let inconsistent := noBound "The constraints may be inconsistent."
  -- Without error recovery, so that an error in the expression is the only error reported.
  let eExpr ← withoutRecover <| elabTerm e none
  if eExpr.hasExprMVar then
    throwError "{if isMaximize then "maximize" else "minimize"}: the expression {e} contains holes"
  match ← computeOptimalBound eExpr isMaximize (← getMainGoal) with
  | .error .inconsistent => throwError inconsistent
  | .error .unbounded => throwError noBound "The expression may be unbounded."
  | .ok bound =>
    -- The statement of the bound: `e < bound` or `e ≤ bound` for `maximize`, and `bound < e` or
    -- `bound ≤ e` for `minimize`.
    let statement (strict : Bool) : TacticM Term :=
      match isMaximize, strict with
      | true, true => `($e < $(quote bound))
      | true, false => `($e ≤ $(quote bound))
      | false, true => `($(quote bound) < $e)
      | false, false => `($(quote bound) ≤ $e)
    -- Check whether `linarith` proves the strict version of the bound.
    let canProveStrict ← succeeds do
      let strictGoal ← mkFreshExprMVar (← elabTerm (← statement true) none)
      Linarith.linarith false [] {} strictGoal.mvarId!
    -- Inconsistent hypotheses prove every bound, and in particular a strict one.
    if canProveStrict then
      if ← hypothesesInconsistent (← getMainGoal) eExpr then
        throwError inconsistent
    let t ← statement canProveStrict
    -- Suggest the `have`, and run it. Without a name, the suggestion is `have : t := ...`, which
    -- introduces `this` when it is pasted into the proof; when we run it ourselves, `this` has to
    -- be written explicitly, as the name introduced by `have :` in a quotation is inaccessible.
    let (suggestion, tac) ← match h with
      | some v => do
        let tac ← `(tactic| have $v : $t := by linarith)
        pure (tac, tac)
      | none => do
        pure (← `(tactic| have : $t := by linarith),
          ← `(tactic| have $(mkIdent `this) : $t := by linarith))
    Meta.Tactic.TryThis.addSuggestion (← getRef) suggestion
    evalTactic tac

/--
`maximize e` finds the best upper bound `q` on `e` that `linarith` can prove from the hypotheses.
It suggests `have : e ≤ q := by linarith`, or `have : e < q := by linarith` when `linarith` can
prove the strict bound, and adds that hypothesis to the context. `maximize e with h` names the new
hypothesis `h`; otherwise it is called `this`.

```lean
example (x y : ℝ) (h₁ : 3 * x + y < 4) (h₂ : x < 2) : True := by
  maximize 4 * x + y with h
  -- Try this: have h : 4 * x + y < 6 := by linarith
  trivial
```

The expression must have values in a linearly ordered field `K`, such as `ℚ` or `ℝ`. The bound is
computed from the facts that `linarith` uses:
* the hypotheses `a = b`, `a ≤ b`, `a < b`, `a ≥ b` and `a > b` between terms of type `K`, after
  conjunctions are split and negated inequalities are flipped (`¬ 1 < x` is used as `x ≤ 1`).
  Hypotheses `a ≠ b` are not used, and neither are hypotheses in other types: `n ≤ 3` in `ℕ` does
  not bound `(n : ℚ)`;
* the facts `0 ≤ (n : K)` for the casts of natural numbers that occur in these hypotheses and in
  `e`, except inside a division: `(n : ℚ) / 2` alone does not give `0 ≤ (n : ℚ)`;
* if `Mathlib.Tactic.Linarith.NNRealPreprocessor` is imported (as by `import Mathlib`) and `K` is
  `ℝ`, the hypotheses in `ℝ≥0`, read in `ℝ`, and the facts `0 ≤ (x : ℝ)` for the casts of
  `x : ℝ≥0`.

Only the linear structure is used. Products and powers by numerals are multiplied out and divisions
by numerals are cleared. What remains are atoms, such as `x`, `Real.pi`, `f x`, `(n : ℚ)` or
`x / y`, and products of atoms, such as `x * y` or `x ^ 2`. Each atom and each such product is one
more unknown, unrelated to the terms it contains. So from `x * y ≤ 2` and `y ≤ 3` the bound on
`(x + 1) * y` is `5`, but `-3 ≤ x ≤ 3` gives no bound on `x ^ 2`; and a cast `(n : ℚ)` is not known
to be an integer: from `(n : ℚ) ≤ 7 / 2` the bound is `7 / 2`, not `3`.

`maximize` fails with "The constraints may be inconsistent." if `linarith` can prove `False` from
the hypotheses (hypotheses in every type count here), since then every bound holds, and with
"The expression may be unbounded." if the facts above give no upper bound on `e`.

See also `minimize`.
-/
syntax (name := maximize) "maximize " term (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| maximize $e $[with $h]?) => runLinearOptim true e h

/--
`minimize e` finds the best lower bound `q` on `e` that `linarith` can prove from the hypotheses.
It suggests `have : q ≤ e := by linarith`, or `have : q < e := by linarith` when `linarith` can
prove the strict bound, and adds that hypothesis to the context. `minimize e with h` names the new
hypothesis `h`; otherwise it is called `this`.

```lean
example (x y : ℝ) (h₁ : -4 < 3 * x + y) (h₂ : -2 < x) : True := by
  minimize 4 * x + y with h
  -- Try this: have h : -6 < 4 * x + y := by linarith
  trivial
```

`minimize` accepts the same expressions and uses the same facts as `maximize` (see its
documentation). It fails with the same two messages: when `linarith` finds the hypotheses
contradictory, or when the facts give no lower bound on `e`.
-/
syntax (name := minimize) "minimize " term (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| minimize $e $[with $h]?) => runLinearOptim false e h

end TacticImplementation

end Mathlib.Tactic.LinearOptim
