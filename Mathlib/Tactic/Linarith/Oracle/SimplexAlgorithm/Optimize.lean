/-
Copyright (c) 2026 Runtian Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuli Chen, Robert Y. Lewis, Heather Macbeth, Siqing Zhang, Runtian Zhou
-/
module

public meta import Lean.Meta.Basic
public import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Gauss
public import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.SimplexAlgorithm

/-!
# Linear optimization with the `linarith` simplex oracle

`simplexOptimalBound` computes the optimal value of a linear program, reusing the Gaussian
elimination and the pivot operation of the `linarith` oracle. It is used by the `maximize` and
`minimize` tactics.

## Algorithm sketch

1. `Gauss.getTableau` splits the variables into basic and free ones. Unlike in `stateLP`, nothing
  guarantees that the resulting basic solution is feasible.

2. If it is not, *phase 1* introduces an artificial variable `a ≥ 0`, added to every constraint row,
  and minimizes it (`phase1Tableau`). One pivot makes the start feasible; the problem is feasible
  exactly when the minimum of `a` is `0`. The artificial variable is then driven out of the basis
  and removed (`removeArtificial`).

3. *Phase 2* maximizes the objective from the feasible tableau.

Both phases pivot by Bland's rule (`runOptimLoop`), which guarantees termination.
-/

public meta section

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm

/-- Why `simplexOptimalBound` produces no bound, stated for the problem of the `maximize` tactic. -/
inductive LinearOptimException
  /-- The hypotheses may be inconsistent. -/
  | inconsistent : LinearOptimException
  /-- The expression may be unbounded. -/
  | unbounded : LinearOptimException

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/--
Maximizes the variable in row `objRow` of the tableau, keeping the variables in rows
`firstRow, firstRow + 1, ...` nonnegative; rows before `firstRow` are not sign-constrained.
The tableau must be feasible on entry. Pivots by Bland's rule: the entering variable is the one
with smallest index among those that increase the objective, and ties in the ratio test are broken
by smallest index.

Returns `true` when an optimum is reached and `false` when the objective is unbounded.
-/
def runOptimLoop (objRow firstRow : Nat) : SimplexAlgorithmM matType Bool := do
  repeat
    Lean.Core.checkSystem decl_name%.toString
    let t ← get
    let lastIdx := t.free.size - 1
    let mut enterIdx? : Option Nat := none
    for j in [:lastIdx] do
      if t.mat[(objRow, j)]! > 0 && enterIdx?.all (t.free[j]! < t.free[·]!) then
        enterIdx? := some j
    let some enterIdx := enterIdx? | return true
    let mut exitIdx? : Option Nat := none
    let mut minRatio : Rat := 0
    for i in [firstRow:t.basic.size] do
      let coef := t.mat[(i, enterIdx)]!
      if coef < 0 then
        let ratio := -t.mat[(i, lastIdx)]! / coef
        let better (e : Nat) := ratio < minRatio || (ratio == minRatio && t.basic[i]! < t.basic[e]!)
        if exitIdx?.all better then
          exitIdx? := some i
          minRatio := ratio
    let some exitIdx := exitIdx? | return false
    doPivotOperation exitIdx enterIdx
  return true

/-- Deletes the given rows and columns of the tableau, together with their variables. -/
def Tableau.drop (t : Tableau matType) (rows cols : List Nat) : Tableau matType :=
  let shift (l : List Nat) (k : Nat) : Nat := k - l.countP (· < k)
  let basic := (t.basic.zipIdx.filter fun (_, i) => i ∉ rows).map (·.1)
  let free := (t.free.zipIdx.filter fun (_, j) => j ∉ cols).map (·.1)
  let vals := getValues t.mat |>.filterMap fun (i, j, v) =>
    if i ∈ rows || j ∈ cols then none else some (shift rows i, shift cols j, v)
  ⟨basic, free, ofValues vals⟩

/--
Extends a tableau whose rows `1, 2, ...` are constraint rows with an artificial free variable
`artVar`, inserted just before the constant column and added to every constraint row, and with a
new row `0` for the phase 1 objective `phase1Var = -artVar`. The original rows move down by one.
-/
def phase1Tableau (t : Tableau matType) (phase1Var artVar : Nat) : Tableau matType :=
  let lastIdx := t.free.size - 1
  let basic := #[phase1Var] ++ t.basic
  let free := t.free.pop ++ #[artVar, t.free[lastIdx]!]
  let shifted := getValues t.mat |>.map fun (i, j, v) =>
    (i + 1, if j == lastIdx then lastIdx + 1 else j, v)
  let artCoeffs := (List.range' 2 (t.basic.size - 1)).map fun i => (i, lastIdx, (1 : Rat))
  ⟨basic, free, ofValues ((0, lastIdx, -1) :: artCoeffs ++ shifted)⟩

/--
Given a phase 1 tableau whose objective (row `0`) has reached `0`, removes the phase 1 objective
row and the artificial variable `artVar`. If `artVar` is still basic its value is `0`, so it can be
pivoted out against any free variable with nonzero coefficient without changing the basic solution.
Such a variable exists because `artVar` started out free; dropping the row is only a fallback.
-/
def removeArtificial (artVar : Nat) : SimplexAlgorithmM matType Unit := do
  let t ← get
  let lastIdx := t.free.size - 1
  if let some r := t.basic.idxOf? artVar then
    match (List.range lastIdx).find? fun j => t.mat[(r, j)]! != 0 with
    | some j => doPivotOperation r j
    | none =>
      set (t.drop [0, r] [])
      return
  let t ← get
  set (t.drop [0] [t.free.idxOf artVar])

/--
Returns the optimal value of the linear program encoded by the matrix `A`, as built by
`Mathlib.Tactic.LinearOptim.preprocessLinearOptim`.

The variables are the columns of `A`, and each row `(a₀, …, aₘ)` is the equation
`a₀ x₀ + ⋯ + aₘ xₘ = 0`. The column `x₀` has a single nonzero entry `-1` in row `0`, so row `0`
defines the objective `x₀`, which is maximized. The last column `xₘ` is the constant `1`, and all
other variables are nonnegative.

The `maximize` tactic encodes the *dual* of its problem: the variables `x₁, …, xₘ₋₁` are the
multipliers of the hypotheses. Hence an infeasible program means that no bound follows from the
hypotheses (reported as `LinearOptimException.unbounded`), and an unbounded program means that the
hypotheses are inconsistent (reported as `LinearOptimException.inconsistent`).
-/
def simplexOptimalBound {n m : Nat} (A : matType n m) :
    Lean.Meta.MetaM (Except LinearOptimException Rat) := do
  let t ← Gauss.getTableau A
  -- The objective `x₀` is basic in row `0`, since column `0` is nonzero only in row `0`.
  unless t.basic[0]? == some 0 do
    throwError "simplexOptimalBound: the objective column is not basic"
  -- If the constant column is basic, its row reads `0 = 1`: the program is infeasible.
  if t.basic.contains (m - 1) then
    return .error .unbounded
  let lastIdx := t.free.size - 1
  -- The constraint row with the most negative value, if the basic solution is infeasible.
  let value (i : Nat) : Rat := t.mat[(i, lastIdx)]!
  let mut worst? : Option Nat := none
  for i in [1:t.basic.size] do
    if value i < 0 && worst?.all (value i < value ·) then
      worst? := some i
  let mut t := t
  if let some worst := worst? then
    let artVar := m
    -- Phase 1: entering `artVar` in the worst row makes every constraint row nonnegative.
    let phase1 : SimplexAlgorithmM matType Bool := do
      doPivotOperation (worst + 1) lastIdx
      runOptimLoop 0 2
    let (res, t1) ← phase1.run (phase1Tableau t (m + 1) artVar)
    unless res matches .ok true do
      throwError "simplexOptimalBound: phase 1 did not reach an optimum"
    if t1.mat[(0, t1.free.size - 1)]! < 0 then
      return .error .unbounded
    t := (← (removeArtificial artVar).run t1).2
  -- Phase 2.
  let (res, t2) ← (runOptimLoop 0 1).run t
  match res with
  | .ok true => return .ok t2.mat[(0, t2.free.size - 1)]!
  | .ok false => return .error .inconsistent
  | .error _ => throwError "simplexOptimalBound: phase 2 failed"

end Mathlib.Tactic.Linarith.SimplexAlgorithm
