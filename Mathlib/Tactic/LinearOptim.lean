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
# The `maximize` and `minimize` tactics

`maximize e` finds the least upper bound on a linear expression `e` that follows from the
hypotheses as `linarith` sees them: after `linarith`'s preprocessing, with nonlinear terms such as
`x * y` treated as atoms. It suggests `have : e ≤ q := by linarith`, or `e < q` when the strict
bound holds, and adds that hypothesis. `minimize e` does the same for lower bounds. The expression
must take values in a linearly ordered field, such as `ℚ` or `ℝ`.

## Main declarations

* `maximize`, `minimize`: the tactics.
* `Problem`, `parseLinarithStructure`: the linear problem, read off from the hypotheses as
  `linarith` preprocesses them.
* `computeOptimalBound`: the optimal bound, computed with `simplexOptimalBound`.

## Implementation notes

The preprocessing of `linarith` may scale the expression, for instance to clear denominators. To
see how, a dummy hypothesis `e < z`, with `z` a fresh variable, is preprocessed together with the
other hypotheses (`parseLinarithStructure`). The bound is read off from the optimal value of the
dual linear program, whose variables are the coefficients of a nonnegative combination of the
hypotheses (`computeOptimalBound`); `simplexOptimalBound` solves it. For `minimize e`, the bound is
minus the bound for `maximize (-e)`. The simplex algorithm is only an oracle: the new hypothesis is
proved by `linarith`, which also decides whether the strict bound holds. The tactic fails if the
hypotheses are inconsistent.
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
  /-- The comparisons of the other facts that `linarith`'s preprocessing gives in the type of `e`,
  in order, each equality `s = 0` followed by `-s = 0`. -/
  hyps : List Comp
  /-- The comparison `k * e < 0` coming from the dummy hypothesis `e < z`, with `z` removed. -/
  objective : Comp
  /-- The largest variable index. -/
  maxVar : ℕ
  /-- The positive factor `k` by which `linarith`'s preprocessing scales `e`. -/
  scale : ℕ

/-- Turns the hypotheses in the local context, which must contain a dummy hypothesis `H`, into the
linear comparisons that `linarith` would use.

The caller adds the dummy hypothesis `H : e < z`, where `z` is a fresh variable, to the context
to capture how the expression `e` is transformed. Preprocessing turns it into `e - z < 0`, which
`cancelDenoms` may scale to `k*e - k*z < 0`; the coefficient `-k` of `z` gives the scaling factor
`k`.

The comparison coming from `H` is the only one that mentions `z`, so `z` is a variable that occurs
in it and in no other comparison. Any other such variable is a part of `e` that no hypothesis
constrains (nonlinear terms such as `x * y` being atoms), so the hypotheses give no bound on `e`
unless they are inconsistent. In that case this function returns `none`, and the caller tells the
two cases apart. Otherwise it returns the problem, with `z` removed from the comparisons. -/
def parseLinarithStructure (ty : Expr) (z : FVarId) : MetaM (Option Problem) := do
  let hyps := (← getLocalHyps).toList
  -- Preprocess as `linarith` does in its default configuration, with the preprocessors listed as
  -- in `Linarith.runLinarith`, so that the bound is computed from the same facts that `linarith`
  -- later uses to prove it. In particular, this adds the facts `0 ≤ (n : K)` for the casts of
  -- natural numbers. The preprocessors need a goal in the current context, which contains `z` and
  -- `H`.
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
  -- first, then the hypotheses in reverse order, with the negation of each equality next to it,
  -- each tagged with the index of its hypothesis in `hypSet`.
  let first :: _ := hypSet | throwError "linear optimization: internal error: no hypotheses"
  let tagged := (← addNegEqProofsIdx hypSet.zipIdx).reverse
  let negOneLtZero ← mkNegOneLtZeroProof (← typeOfIneqProof first)
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
  /-- No bound follows from the facts that `linarith` uses, which are consistent. -/
  | unbounded : NoBound

/-- Whether `linarith` can prove `False` from the hypotheses in the context of `g`, together with
the facts that its preprocessing derives from the expression `e`, such as `0 ≤ (n : K)` for the
casts of natural numbers in `e`. These facts are also used to compute the bound on `e`. -/
def hypothesesInconsistent (g : MVarId) (e : Expr) : MetaM Bool := g.withContext do
  let goal ← mkFreshExprMVar (mkConst ``False)
  succeeds <| Linarith.linarith false [← mkEqRefl e] {} goal.mvarId!

/-- The optimal bound on `e`, or why there is none: the least upper bound on `e` if `isMaximize`,
and otherwise the greatest lower bound, which is minus the least upper bound on `-e`. Throws an
error if `e` does not take values in a linearly ordered field.

Let `t` be `e` or `-e`, and `k * t < 0` the comparison coming from the dummy hypothesis. A solution
of the linear program of `Problem.toMatrix` consists of multipliers `yⱼ ≥ 0` of the comparisons
`Lⱼ R 0` of `Problem.hyps`, where `R` is one of `<`, `≤` and `=`, and of the coefficient `y` of
`-1 < 0`, of any sign, such that `∑ⱼ yⱼ * Lⱼ = k * t + y`. As `∑ⱼ yⱼ * Lⱼ ≤ 0`, this gives
`k * t ≤ -y` (strict hypotheses are treated as non-strict here). The simplex algorithm maximizes
`y`, and the bound on `t` is `-max y / k`. -/
def computeOptimalBound (e : Expr) (isMaximize : Bool) (g : MVarId) :
    MetaM (Except NoBound ℚ) := g.withContext do
  let ⟨u, ty, e⟩ ← inferTypeQ' e
  -- The bound is the optimum of a linear program over `ℚ`, which is the optimum over `ty` only
  -- when `ty` is a linearly ordered field: over `ℤ`, for instance, it need not be an integer.
  let notField := m!"{if isMaximize then "maximize" else "minimize"} only works over linearly \
    ordered fields, such as ℚ and ℝ, but {e} has type {ty}."
  let some _ ← synthInstanceQ? q(Field $ty) | throwError notField
  let some _ ← synthInstanceQ? q(LinearOrder $ty) | throwError notField
  let some _ ← synthInstanceQ? q(IsStrictOrderedRing $ty) | throwError notField
  let t := if isMaximize then e else q(-$e)
  -- The hypotheses give no bound on `t` unless they are inconsistent: tell the two cases apart
  -- with `linarith`.
  let unboundedOrInconsistent : MetaM (Except NoBound ℚ) := do
    return .error (if ← hypothesesInconsistent g e then .inconsistent else .unbounded)
  withLocalDeclDQ `z ty fun z ↦ withLocalDeclDQ `H q($t < $z) fun _ ↦ do
  let some p ← parseLinarithStructure ty z.fvarId! | unboundedOrInconsistent
  match ← simplexOptimalBound (p.toMatrix DenseMatrix) with
  | .ok y =>
    let bound := -y / p.scale
    return .ok (if isMaximize then bound else -bound)
  -- When the program is infeasible, the non-strict versions of the hypotheses give no bound on `t`,
  -- and neither do the hypotheses unless they are inconsistent. When it is unbounded, some
  -- `∑ⱼ yⱼ * Lⱼ` is a positive constant, so the hypotheses are inconsistent.
  | .error NoOptimum.infeasible => unboundedOrInconsistent
  | .error NoOptimum.unbounded => return .error NoBound.inconsistent

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
the hypothesis `h`. The goal is not used: unlike `linarith`, `maximize` does not add its negation.

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
