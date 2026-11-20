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
* `Problem.toMatrix` - Converts constraints to matrix for simplex
* `computeOptimalBound` - Core function computing optimal bounds

## Implementation

The `maximize` and `minimize` tactics work by:
1. Parsing the linear constraints and target expression using `parseLinarithStructure`
2. Converting them to matrix form suitable for the simplex algorithm via `Problem.toMatrix`
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

/-- The linear program behind `maximize e`, in the linear forms of `linarith`. Variable `0` is the
constant term. -/
structure Problem where
  /-- The comparison `-1 < 0`, which `linarith` adds to the hypotheses. -/
  negOne : Comp
  /-- The other comparisons coming from the hypotheses, in the order of the hypotheses. -/
  hyps : List Comp
  /-- The comparison `k * e < 0` coming from the dummy hypothesis `e < z`, with `z` removed. -/
  objective : Comp
  /-- The largest variable index. -/
  maxVar : ℕ
  /-- The positive factor `k` by which `linarith`'s preprocessing scales `e`. -/
  scale : ℕ

/-- Turns the hypotheses in the local context, which contains a dummy hypothesis `H`, into the
linear comparisons that `linarith` would use.

The caller adds the dummy hypothesis `H : e < z`, where `z` is a fresh variable, to the context
to capture how the expression `e` is transformed. Preprocessing turns it into `e - z < 0`, which
`cancelDenoms` may scale to `k*e - k*z < 0`; the coefficient `-k` of `z` gives the scaling factor
`k`.

The comparison coming from `H` is the only one that mentions `z`, so `z` is a variable that occurs
in it and in no other comparison. Any other such variable is a part of `e` that no hypothesis
constrains, so no bound on `e` follows from the hypotheses (in which nonlinear terms such as
`x * y` are atoms): either `e` is unbounded or the hypotheses are inconsistent. In that case this
function returns `none`, and the caller tells the two apart. Otherwise it returns the problem,
with `z` removed from the comparisons. -/
def parseLinarithStructure (ty : Expr) (z : FVarId) : MetaM (Option Problem) := do
  let hyps := (← getLocalHyps).toList
  -- Preprocess as `linarith` does in its default configuration (see `Linarith.runLinarith`), so
  -- that the bound is computed from the same facts that `linarith` later uses to prove it. In
  -- particular, this adds the facts `0 ≤ (n : K)` for the casts of natural numbers. The
  -- preprocessors need a goal, and it has to live in the current context, which contains `z`.
  let cfg : LinarithConfig := {}
  let pps :=
    (if cfg.splitHypotheses then [Linarith.splitConjunctions.globalize.branching] else []) ++
      (if cfg.splitNe then [Linarith.removeNe] else []) ++ cfg.preprocessors
  let g ← mkFreshExprMVar (mkConst ``False)
  let [(_, es)] ← Linarith.preprocess pps g.mvarId! hyps
    | throwError "linear optimization: internal error: preprocessing did not give exactly one case"
  -- As in `linarith`, compare the types up to definitional equality: `ty` may be an assigned
  -- metavariable, e.g. after `refine fun x => ?_`.
  let hypSet ← es.filterM fun h => do isDefEq ty (← typeOfIneqProof h)
  -- The linear forms, as `Linarith.proveFalseByLinarith` computes them: the comparison `-1 < 0`
  -- first, then the hypotheses in reverse order, each equality followed by its negation and each
  -- tagged with the index of its hypothesis in `hypSet`.
  let h :: _ := hypSet | throwError "linear optimization: internal error: no hypotheses"
  let tagged := (← addNegEqProofsIdx hypSet.zipIdx).reverse
  let negOneLtZero ← mkNegOneLtZeroProof (← typeOfIneqProof h)
  let (comps, maxVar) ← linearFormsAndMaxVar cfg.transparency (negOneLtZero :: tagged.map (·.1))
  let negOne :: comps := comps
    | throwError "linear optimization: internal error: no linear forms"
  -- Find the comparison coming from `H`: its hypothesis is the only one mentioning `z`.
  let mentionsZ ← hypSet.mapM fun h => return (← instantiateMVars (← inferType h)).containsFVar z
  let some hIdx := mentionsZ.idxOf? true
    | throwError "linear optimization: internal error: the dummy hypothesis was lost"
  let some goalPos := tagged.findIdx? (·.2 == hIdx)
    | throwError "linear optimization: internal error: the dummy hypothesis has no linear form"
  let goalComp := comps[goalPos]!
  let others := comps.eraseIdx goalPos
  -- The variables of `goalComp` that occur in no other comparison.
  let onlyInGoal := goalComp.coeffs.filter fun (v, _) =>
    (negOne :: others).all fun c => !c.coeffs.any (·.1 == v)
  match onlyInGoal with
  | [(zIdx, negScale)] =>
    if 0 ≤ negScale then
      throwError "linear optimization: internal error: scaling factor {-negScale}"
    -- Remove `z`, renumbering the variables after it.
    let removeZ (c : Comp) : Comp :=
      { c with coeffs := c.coeffs.filterMap fun (v, a) =>
          if v == zIdx then none else some (if zIdx < v then v - 1 else v, a) }
    return some
      { negOne := removeZ negOne
        hyps := (others.map removeZ).reverse
        objective := removeZ goalComp
        maxVar := maxVar - 1
        scale := (-negScale).toNat }
  | [] => throwError "linear optimization: internal error: the dummy variable occurs elsewhere"
  | _ => return none

end Preprocessing


section MatrixPreprocessing

/-- The matrix of `p` for `simplexOptimalBound`. Row `i` holds the coefficients of variable `i`;
column `0` is the comparison `-1 < 0`, the next columns are the hypotheses, and the last column is
the negated objective. -/
def Problem.toMatrix (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType] (p : Problem) :
    matType (p.maxVar + 1) (p.hyps.length + 2) :=
  let column (j : ℕ) (sign : ℚ) (c : Comp) : List (ℕ × ℕ × ℚ) :=
    c.coeffs.map fun (v, a) => (v, j, sign * a)
  ofValues <| column 0 1 p.negOne ++ (p.hyps.zipIdx.flatMap fun (c, j) => column (j + 1) 1 c) ++
    column (p.hyps.length + 1) (-1) p.objective


end MatrixPreprocessing

section BoundComputation

/-- Why `maximize` or `minimize` produces no bound. -/
inductive NoBound
  /-- The hypotheses are inconsistent, so that every bound holds. -/
  | inconsistent : NoBound
  /-- No bound follows from the hypotheses. -/
  | unbounded : NoBound

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
    MetaM (Except NoBound Rat) := g.withContext do
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
  let unboundedOrInconsistent : MetaM (Except NoBound Rat) := do
    return .error (if ← hypothesesInconsistent g e_exp then .inconsistent else .unbounded)
  -- The dummy hypothesis is always `< z` (for a new dummy variable `z`) to ensure the scaling
  -- factor `k` is positive and that the Comp object represents `k*E`.
  withLocalDeclDQ `z ty fun z ↦ withLocalDeclDQ `H q($target_exp < $z) fun _ ↦ do
  let some p ← parseLinarithStructure ty z.fvarId! | unboundedOrInconsistent
  match ← simplexOptimalBound (p.toMatrix DenseMatrix) with
  | .ok r_opt =>
    let k_q : ℚ := p.scale
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
  -- The program is the dual of the problem of bounding `e`: when it is infeasible, no bound on `e`
  -- follows from the hypotheses, and when it is unbounded, the hypotheses are inconsistent.
  | .error .infeasible => unboundedOrInconsistent
  | .error .unbounded => return .error .inconsistent


end BoundComputation


section TacticImplementation

/-- Runs `maximize e` (if `isMaximize`) or `minimize e`, naming the new hypothesis `h` if given:
computes the optimal bound, suggests a `have` stating it, and adds the hypothesis with the proof
found by `linarith`. The bound is strict if `linarith` can prove the strict version. -/
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
    -- The bound, as an expression of the type of `e`. Only the numeral is elaborated, not `e`.
    let q ← elabTermEnsuringType (quote bound : Term) (← inferType eExpr)
    -- The statement of the bound: `e < q` or `e ≤ q` for `maximize`, and `q < e` or `q ≤ e` for
    -- `minimize`.
    let statement (strict : Bool) : MetaM Expr :=
      let (a, b) := if isMaximize then (eExpr, q) else (q, eExpr)
      mkAppM (if strict then ``LT.lt else ``LE.le) #[a, b]
    let prove (t : Expr) : MetaM Expr := do
      let g ← mkFreshExprMVar t
      Linarith.linarith false [] {} g.mvarId!
      instantiateMVars g
    -- The bound is strict if `linarith` proves the strict version. Inconsistent hypotheses prove
    -- every bound, and in particular a strict one.
    let strictStatement ← statement true
    let (strict, t, proof) ← match ← observing? (prove strictStatement) with
      | some proof =>
        if ← hypothesesInconsistent (← getMainGoal) eExpr then throwError inconsistent
        pure (true, strictStatement, proof)
      | none => do
        let t ← statement false
        pure (false, t, ← prove t)
    -- Suggest the `have`, stated with the syntax of `e` as written by the user.
    let tStx ← match isMaximize, strict with
      | true, true => `($e < $(quote bound))
      | true, false => `($e ≤ $(quote bound))
      | false, true => `($(quote bound) < $e)
      | false, false => `($(quote bound) ≤ $e)
    let suggestion ← match h with
      | some v => `(tactic| have $v : $tStx := by linarith)
      | none => `(tactic| have : $tStx := by linarith)
    Meta.Tactic.TryThis.addSuggestion (← getRef) suggestion
    -- Add the hypothesis with the statement and proof found above. Without a name, it is `this`,
    -- written explicitly: the name introduced by `have :` in a quotation is inaccessible.
    let name := h.getD (mkIdent `this)
    evalTactic (← `(tactic| have $name : $(← Term.exprToSyntax t) := $(← Term.exprToSyntax proof)))

/--
`maximize e` finds the least upper bound `q` for `e` given the linear constraints produced by
`linarith` preprocessing. It adds `this : e ≤ q`, using `e < q` if `linarith` can prove the strict
bound, and suggests the corresponding `have ... := by linarith`. Use `maximize e with h` to name
the hypothesis `h`.

```lean
example (x y : ℚ) (h₁ : 3 * x + y < 4) (h₂ : x < 2) : 4 * x + y < 6 := by
  maximize 4 * x + y with h
  exact h
```

The expression must take values in a linearly ordered field such as `ℚ` or `ℝ`. After expansion,
`linarith` treats nonlinear terms such as `x ^ 2` as independent variables, so bounds on `x` alone
give no bound on `x ^ 2`. A bound stated in `ℕ` also gives no constraint on an expression in `ℚ`,
though `linarith` can use the nonnegativity of a natural number cast to `ℚ`.

`maximize` fails with "The constraints may be inconsistent." if `linarith` can prove `False` from
the linear constraints or from hypotheses in other types (then every bound holds), and otherwise
with "The expression may be unbounded." if the linear constraints give no upper bound on `e`.

See also `minimize`.
-/
syntax (name := maximize) "maximize " term (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| maximize $e $[with $h]?) => runLinearOptim true e h

/--
`minimize e` finds the greatest lower bound `q` for `e` using the same linear constraints as
`maximize`. It adds `this : q ≤ e`, using `q < e` if `linarith` can prove the strict bound, and
suggests the corresponding `have ... := by linarith`. Use `minimize e with h` to name the
hypothesis `h`.

```lean
example (x y : ℚ) (h₁ : 4 ≤ 3 * x + y) (h₂ : 2 ≤ x) : 6 ≤ 4 * x + y := by
  minimize 4 * x + y
  exact this
```

See `maximize` for supported expressions and failure messages.
-/
syntax (name := minimize) "minimize " term (" with " ident)? : tactic

elab_rules : tactic
  | `(tactic| minimize $e $[with $h]?) => runLinearOptim false e h

end TacticImplementation

end Mathlib.Tactic.LinearOptim
