module

import Mathlib.Tactic.Linarith.NNRealPreprocessor
import Mathlib.Tactic.LinearOptim

/-! # Tests for the `maximize` and `minimize` tactics -/

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ### Linear combinations -/

/--
info: Try this:
  [apply] have H : 4 * x + y < 6 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y with H
  trivial

/--
info: Try this:
  [apply] have H : x + 5 * y + 2 * z < 28 / 9 := by linarith
-/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + z < 7) (h2 : x + 3 * y + 4 * z < 2)
    (h3 : x + 10 * y + z < 1) : True := by
  maximize x + 5 * y + 2 * z with H
  trivial

/--
info: Try this:
  [apply] have T : -x - 5 * y - 2 * z < -18 / 5 := by linarith
-/
#guard_msgs in
example (x y z : ℚ) (h1 : x + y + 2 * z > 7) (h2 : x + 3 * y + 4 * z > 2)
    (h3 : x + 10 * y + z > 1) : True := by
  maximize -x - 5 * y - 2 * z with T
  trivial

/--
info: Try this:
  [apply] have H : -157 / 21 < -x - 7 * y := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : -2 * x - y > -10) (h2 : -x - 11 * y > -9) :
    ∃ z : ℚ, z > -157 / 20 ∧ z ≤ -x - 7 * y := by
  minimize -x - 7 * y with H
  exact ⟨-157 / 21, by linarith, by linarith [H]⟩

/--
info: Try this:
  [apply] have H : x - y < 0 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h : x < y) : True := by
  maximize x - y with H
  trivial

/--
info: Try this:
  [apply] have H : (1 / 2) * ε + (1 / 3) * ε < 5 := by linarith
-/
#guard_msgs in
example (ε : ℚ) (h1 : 0 < ε) (h2 : ε < 6) : True := by
  maximize (1 / 2) * ε + (1 / 3) * ε with H
  trivial

/--
info: Try this:
  [apply] have H : -5 < 4 * x + y + 1 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y > -4) (h2 : x > -2) : True := by
  minimize 4 * x + y + 1 with H
  trivial

/--
info: Try this:
  [apply] have H : x / 2 + 1 < 4 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 10) (h2 : y > 4) : True := by
  maximize x / 2 + 1 with H
  trivial

/-! ### Strict and attained bounds

The bound is strict exactly when `linarith` proves the strict inequality, that is, when the bound
is not reached in the linear problem. A strict hypothesis alone does not make it strict: with
`0 < x` and `x ≤ 10`, the bound `x ≤ 10` is reached at `x = 10`.
-/

/--
info: Try this:
  [apply] have H : x ≤ 10 := by linarith
-/
#guard_msgs in
example (x : ℚ) (h1 : 0 < x) (h2 : x ≤ 10) : True := by
  maximize x with H
  trivial

/--
info: Try this:
  [apply] have H : x + y < 5 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : x + y < 5) (h2 : x ≤ 3) : True := by
  maximize x + y with H
  trivial

/--
info: Try this:
  [apply] have H : x < 6 := by linarith
-/
#guard_msgs in
example (x : ℚ) (h1 : x < 10) (h2 : x > 0) (h3 : x < 6) : True := by
  maximize x with H
  trivial

/--
info: Try this:
  [apply] have H : x + 2 * y ≤ 7 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : x ≤ 3) (h2 : y ≤ 2) : True := by
  maximize x + 2 * y with H
  trivial

/--
info: Try this:
  [apply] have H : -1 ≤ x + 2 * y := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : x ≥ -3) (h2 : y ≥ 1) : True := by
  minimize x + 2 * y with H
  trivial

/-! ### Unbounded expressions and inconsistent hypotheses -/

/-- error: minimize: a lower bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h1 : x < 0) : True := by
  minimize x with H
  trivial

/-- error: maximize: an upper bound cannot be produced for 5 * x + 3 * y.
    The expression may be unbounded. -/
#guard_msgs in
example (x y : ℚ) (h1 : 3 * x + y ≤ 7) (h2 : x < 6) : True := by
  maximize 5 * x + 3 * y with H
  trivial

/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x : ℚ) (h2 : x > 0) (h1 : x < -5) : True := by
  maximize x with H
  trivial

/-- error: minimize: a lower bound cannot be produced for x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x : ℚ) (h2 : x < 0) (h1 : x > 5) : True := by
  minimize x with H
  trivial

/-- error: maximize: an upper bound cannot be produced for y.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 7) : True := by
  maximize y with H
  trivial

/-- error: maximize: an upper bound cannot be produced for -y.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h2 : x < 0) (h1 : x > 7) : True := by
  maximize -y with H
  trivial

/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h2 : y < 0) (h1 : y > 7) : True := by
  maximize x with H
  trivial

/-- error: maximize: an upper bound cannot be produced for x + y.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x y : ℚ) (h1 : x > 0) (h2 : y <= 5) (h3 : y > 9) : True := by
  maximize x + y
  trivial

-- Inconsistent hypotheses in another type are reported too.
/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (k : ℤ) (h1 : k < 0) (h2 : 0 < k) (x : ℚ) (hx : x ≤ 1) : True := by
  maximize x
  trivial

-- The goal is not used: from its negation `x ≤ 5`, `linarith` would get the bound `x ≤ 5`.
/-- error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded. -/
#guard_msgs in
example (x : ℚ) (h : 0 ≤ x) : 5 < x := by
  maximize x

/-! ### Naming the new hypothesis -/

/--
info: Try this:
  [apply] have : 5 < x := by linarith
-/
#guard_msgs in
example (x : ℚ) (h : x > 5) : True := by
  minimize x
  trivial

/--
info: Try this:
  [apply] have : x < 5 := by linarith
---
info: Try this:
  [apply] have : y < 3 := by linarith
---
info: Try this:
  [apply] have : x + y < 8 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : x < 5) (h2 : y < 3) : True := by
  maximize x
  maximize y
  maximize x + y
  trivial

/--
info: Try this:
  [apply] have : x < 8 := by linarith
---
info: Try this:
  [apply] have min_y : 3 < y := by linarith
---
info: Try this:
  [apply] have min_sum : 5 < x + y := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h1 : x < 8) (h2 : y > 3) (h3 : x > 2) : True := by
  maximize x                      -- anonymous
  minimize y with min_y           -- named
  minimize x + y with min_sum     -- named
  trivial

/-! ### The type of the expression -/

/--
info: Try this:
  [apply] have H : x + y < 5 := by linarith
-/
#guard_msgs in
example {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) (h1 : x + y < 5) (h2 : x < 3) : True := by
  maximize x + y with H
  trivial

-- Over `ℤ` the optimum of the rational problem need not be an integer, so `ℤ` is rejected.
/-- error: maximize only works over linearly ordered fields, such as ℚ and ℝ, but x has type ℤ. -/
#guard_msgs in
example (x : ℤ) (h : 2 * x ≤ 7) : True := by
  maximize x
  trivial

/-- error: minimize only works over linearly ordered fields, such as ℚ and ℝ, but x has type ℕ. -/
#guard_msgs in
example (x : ℕ) (h : x ≤ 3) : True := by
  minimize x
  trivial

-- `ℝ≥0` is only a semifield.
/-- error: maximize only works over linearly ordered fields, such as ℚ and ℝ, but a has type ℝ≥0. -/
#guard_msgs in
open NNReal in
example (a : ℝ≥0) (h : a ≤ 3) : True := by
  maximize a
  trivial

-- The order must make the field an ordered field.
/-- error: maximize only works over linearly ordered fields, such as ℚ and ℝ, but x has type K. -/
#guard_msgs in
example {K : Type*} [Field K] [LinearOrder K] (x : K) (h : x ≤ 3) : True := by
  maximize x
  trivial

-- Any linearly ordered field works.
/--
info: Try this:
  [apply] have : x ≤ 10 := by linarith
-/
#guard_msgs in
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (x y : K)
    (h0 : -2 * x + 3 * y ≤ 7) (h2 : x + y ≤ 5) (h3 : x ≤ 10) : True := by
  maximize x
  trivial

/-! ### Hypothesis order and strict infeasibility -/

-- The result must not depend on the order of the hypotheses: the simplex algorithm needs a
-- feasible starting point, which Gaussian elimination alone provides only for some orders.

/--
info: Try this:
  [apply] have : x ≤ 10 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h0 : -2 * x + 3 * y ≤ 7) (h2 : x + y ≤ 5) (h3 : x ≤ 10) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 10 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h0 : -2 * x + 3 * y ≤ 7) (h3 : x ≤ 10) (h2 : x + y ≤ 5) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 10 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h2 : x + y ≤ 5) (h0 : -2 * x + 3 * y ≤ 7) (h3 : x ≤ 10) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 10 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h2 : x + y ≤ 5) (h3 : x ≤ 10) (h0 : -2 * x + 3 * y ≤ 7) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 10 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h3 : x ≤ 10) (h0 : -2 * x + 3 * y ≤ 7) (h2 : x + y ≤ 5) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 10 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h3 : x ≤ 10) (h2 : x + y ≤ 5) (h0 : -2 * x + 3 * y ≤ 7) : True := by
  maximize x
  trivial

-- A problem on which starting phase 1 of the simplex algorithm from another row than the one with
-- the most negative value gives a wrong bound.
/--
info: Try this:
  [apply] have : -3 * x + 3 * y - 2 * z < 427 / 33 := by linarith
-/
#guard_msgs in
example (x y z : ℚ) (h0 : x + 3 * y ≤ 5) (h1 : x - y + z ≤ 1) (h2 : -2 * x - 3 * z < 1)
    (h3 : -x - 3 * y + 2 * z ≤ 0) (h4 : -3 * x - 2 * y + 2 * z < 6) : True := by
  maximize -3 * x + 3 * y - 2 * z
  trivial

-- Hypotheses inconsistent only because of a strict inequality: `x < -2` and `x ≥ -2`.
/-- error: minimize: a lower bound cannot be produced for -2 * x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x : ℚ) (h1 : -x > 2) (h2 : x ≥ -2) : True := by
  minimize -2 * x
  trivial

/-- error: maximize: an upper bound cannot be produced for x.
    The constraints may be inconsistent. -/
#guard_msgs in
example (x : ℚ) (h1 : x < 0) (h2 : x > 0) : True := by
  maximize x
  trivial

/-! ### Variables introduced inside the proof -/

/--
info: Try this:
  [apply] have : x ≤ 2 := by linarith
-/
#guard_msgs in
example : ∀ x : ℚ, x ≤ 2 → True := by
  intro x hx
  maximize x
  trivial

-- The inner `x` shadows the outer one, and the bound is about the inner `x`.
/--
info: Try this:
  [apply] have : x ≤ 5 := by linarith
-/
#guard_msgs in
example (x : ℚ) (h : x ≤ 1) : ∀ x : ℚ, x ≤ 5 → True := by
  intro x hx
  maximize x
  trivial

/--
info: Try this:
  [apply] have : 1 ≤ x := by linarith
-/
#guard_msgs in
example (h : ∃ x : ℚ, 1 ≤ x ∧ x ≤ 3) : True := by
  obtain ⟨x, hx1, hx2⟩ := h
  minimize x
  trivial

/-! ### The same preprocessing as `linarith` -/

-- Casts of natural numbers are nonnegative.
/--
info: Try this:
  [apply] have : x ≤ 0 := by linarith
-/
#guard_msgs in
example (x : ℚ) (n : ℕ) (h : x ≤ -(n : ℚ)) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 5 := by linarith
-/
#guard_msgs in
example (x : ℚ) (n : ℕ) (h : x ≤ 5 - (n : ℚ)) (h2 : x ≤ 10) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 4 := by linarith
-/
#guard_msgs in
example (m n : ℕ) (x : ℚ) (h : x ≤ 4 - (m : ℚ) - 2 * (n : ℚ)) : True := by
  maximize x
  trivial

-- The cast may occur only in the expression.
/--
info: Try this:
  [apply] have : 0 ≤ (n : ℚ) := by linarith
-/
#guard_msgs in
example (n : ℕ) : True := by
  minimize (n : ℚ)
  trivial

-- That `n` is a natural number is not used beyond `0 ≤ (n : ℚ)`.
/--
info: Try this:
  [apply] have : (n : ℚ) ≤ 7 / 2 := by linarith
-/
#guard_msgs in
example (n : ℕ) (h : (n : ℚ) ≤ 7 / 2) : True := by
  maximize (n : ℚ)
  trivial

-- Casts of integers can be negative.
/--
error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded.
-/
#guard_msgs in
example (x : ℚ) (k : ℤ) (h : x ≤ -(k : ℚ)) : True := by
  maximize x
  trivial

-- Conjunctions are split.
/--
info: Try this:
  [apply] have : x + y ≤ 5 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h : x ≤ 2 ∧ y ≤ 3) : True := by
  maximize x + y
  trivial

-- A cast next to another variable, in the expression or in a hypothesis.
/--
info: Try this:
  [apply] have : 1 ≤ x + (n : ℚ) := by linarith
-/
#guard_msgs in
example (n : ℕ) (x : ℚ) (h : 1 ≤ x) : True := by
  minimize x + (n : ℚ)
  trivial

/--
info: Try this:
  [apply] have : x - (n : ℚ) ≤ 3 := by linarith
-/
#guard_msgs in
example (n : ℕ) (x : ℚ) (h : x ≤ 3) : True := by
  maximize x - (n : ℚ)
  trivial

/--
info: Try this:
  [apply] have : x ≤ 4 := by linarith
-/
#guard_msgs in
example (n : ℕ) (x : ℚ) (h : x + (n : ℚ) ≤ 4) : True := by
  maximize x
  trivial

-- A cast that cancels out of the expression.
/--
info: Try this:
  [apply] have : 2 * x + (m : ℚ) / 3 - (m : ℚ) / 3 ≤ 8 := by linarith
-/
#guard_msgs in
example (n m : ℕ) (x : ℚ) (h : x + (n : ℚ) ≤ 4) (h2 : 0 ≤ x) : True := by
  maximize 2 * x + (m : ℚ) / 3 - (m : ℚ) / 3
  trivial

-- Conjunctions are split also when nested, and negations inside them are pushed.
/--
info: Try this:
  [apply] have : x + y + z ≤ 6 := by linarith
-/
#guard_msgs in
example (x y z : ℚ) (h : x ≤ 1 ∧ (y ≤ 2 ∧ z ≤ 3)) : True := by
  maximize x + y + z
  trivial

/--
info: Try this:
  [apply] have : x + y ≤ 3 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (h : ¬ 1 < x ∧ y ≤ 2) : True := by
  maximize x + y
  trivial

-- As for `linarith`, hypotheses about natural numbers are not used for an expression in `ℚ`.
/--
error: maximize: an upper bound cannot be produced for (n : ℚ).
    The expression may be unbounded.
-/
#guard_msgs in
example (n : ℕ) (h : n ≤ 3) : True := by
  maximize (n : ℚ)
  trivial

-- With `Mathlib.Tactic.Linarith.NNRealPreprocessor`, hypotheses in `ℝ≥0` are used.
/--
info: Try this:
  [apply] have : x ≤ 3 := by linarith
-/
#guard_msgs in
open NNReal in
example (a : ℝ≥0) (x : ℝ) (h : x ≤ (a : ℝ)) (ha : a ≤ 3) : True := by
  maximize x
  trivial

-- The fact `0 ≤ (n : ℚ)`, which makes the hypotheses inconsistent, comes from the expression.
/--
error: maximize: an upper bound cannot be produced for (n : ℚ) + x.
    The constraints may be inconsistent.
-/
#guard_msgs in
example (n : ℕ) (x : ℚ) (h : (n : ℚ) / 2 < -1) : True := by
  maximize (n : ℚ) + x
  trivial

-- The same when the hypotheses are inconsistent only because of a strict inequality.
/--
error: maximize: an upper bound cannot be produced for (n : ℚ) + x.
    The constraints may be inconsistent.
-/
#guard_msgs in
example (n : ℕ) (x : ℚ) (h : (n : ℚ) / 2 < 0) (hx : x ≤ 1) : True := by
  maximize (n : ℚ) + x
  trivial

/-! ### Variables of the expression that no hypothesis mentions -/

/--
error: maximize: an upper bound cannot be produced for y.
    The expression may be unbounded.
-/
#guard_msgs in
example (x y : ℚ) (h : x ≤ 3) : True := by
  maximize y
  trivial

/--
error: minimize: a lower bound cannot be produced for x + y.
    The expression may be unbounded.
-/
#guard_msgs in
example (x y : ℚ) (h : x ≤ 3) (h' : 0 ≤ x) : True := by
  minimize x + y
  trivial

/--
error: maximize: an upper bound cannot be produced for y.
    The constraints may be inconsistent.
-/
#guard_msgs in
example (x y : ℚ) (h : x ≤ 3) (h' : 4 ≤ x) : True := by
  maximize y
  trivial

-- A fraction in the expression changes the scaling factor.
/--
info: Try this:
  [apply] have : x / 3 + y / 2 ≤ 7 / 6 := by linarith
-/
#guard_msgs in
example (x y : ℚ) (hy : y ≤ 1) (hx : x ≤ 2) : True := by
  maximize x / 3 + y / 2
  trivial

/-! ### Elaboration of the expression -/

-- The types of the variables may be assigned metavariables.
/--
info: Try this:
  [apply] have : x ≤ 2 := by linarith
-/
#guard_msgs in
example : ∀ x : ℚ, x ≤ 2 → True := by
  refine fun x hx => ?_
  maximize x
  trivial

/--
info: Try this:
  [apply] have : y ≤ 3 := by linarith
-/
#guard_msgs in
example (x : ℚ) (hx : x ≤ 2) : True := by
  let y := x + 1
  maximize y
  trivial

-- Without a name, the new hypothesis is `this`.
/--
info: Try this:
  [apply] have : x ≤ 2 := by linarith
-/
#guard_msgs in
example (x : ℚ) (hx : x ≤ 2) : x ≤ 2 := by
  maximize x
  exact this

/--
error: maximize: the expression x + _ contains holes
-/
#guard_msgs in
example (x : ℚ) (hx : x ≤ 2) : True := by
  maximize x + _
  trivial

@[deprecated "use `id`" (since := "2026-01-01")] abbrev oldId (q : ℚ) : ℚ := q

-- The expression is elaborated once, so a deprecated constant in it gives one warning.
/--
warning: `oldId` has been deprecated: use `id`
---
info: Try this:
  [apply] have : oldId x < 2 := by linarith
-/
#guard_msgs in
example (x : ℚ) (h : x < 2) : True := by
  maximize oldId x
  trivial

-- An error in the expression is reported once.
/--
error: Unknown identifier `undefinedThing`
-/
#guard_msgs in
example (x : ℚ) (hx : x ≤ 1) : True := by
  maximize x + undefinedThing
  trivial

/-! ### Expressions in `ℝ` -/

/--
info: Try this:
  [apply] have : x + 2 * y ≤ 6 := by linarith
-/
#guard_msgs in
example (x y : ℝ) (h1 : x + y ≤ 3) (h2 : x ≤ 1) (h3 : 0 ≤ x) : True := by
  maximize x + 2 * y
  trivial

-- The bound is strict when it is not reached.
/--
info: Try this:
  [apply] have : 4 * x + y < 6 := by linarith
-/
#guard_msgs in
example (x y : ℝ) (h1 : 3 * x + y < 4) (h2 : x < 2) : True := by
  maximize 4 * x + y
  trivial

/--
info: Try this:
  [apply] have : 3 / 2 ≤ x := by linarith
-/
#guard_msgs in
example (x : ℝ) (h : 3 ≤ 2 * x) : True := by
  minimize x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 2 := by linarith
-/
#guard_msgs in
example (x : ℝ) (h : 0.5 * x ≤ 1) : True := by
  maximize x
  trivial

/--
info: Try this:
  [apply] have : 0.5 * x ≤ 3 / 2 := by linarith
-/
#guard_msgs in
example (x : ℝ) (h : x ≤ 3) : True := by
  maximize 0.5 * x
  trivial

/--
info: Try this:
  [apply] have : x ≤ 2 := by linarith
-/
#guard_msgs in
example (x y : ℝ) (h : x + y = 3) (hy : 1 ≤ y) : True := by
  maximize x
  trivial

-- Casts of natural numbers are nonnegative.
/--
info: Try this:
  [apply] have : x ≤ 1 / 2 := by linarith
-/
#guard_msgs in
example (n : ℕ) (x : ℝ) (h : x + n ≤ 1 / 2) : True := by
  maximize x
  trivial

/--
error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded.
-/
#guard_msgs in
example (x : ℝ) (h : 0 < x) : True := by
  maximize x
  trivial

-- Terms other than variables and numerals, such as `f 0`, are treated as unknowns.
/--
info: Try this:
  [apply] have : x ≤ 4 := by linarith
-/
#guard_msgs in
example (f : ℝ → ℝ) (x : ℝ) (h : x ≤ f 0) (hf : f 0 ≤ 4) : True := by
  maximize x
  trivial

-- `f 0 * x` is a single unknown, unrelated to `x`, so no bound on `x` is found, although
-- `x ≤ 1` follows from the hypotheses.
/--
error: maximize: an upper bound cannot be produced for x.
    The expression may be unbounded.
-/
#guard_msgs in
example (f : ℝ → ℝ) (x : ℝ) (h : f 0 * x ≤ 1) (hf : 1 ≤ f 0) : True := by
  maximize x
  trivial

-- Likewise, `x * y` is a single unknown.
/--
info: Try this:
  [apply] have : x * y + x ≤ 3 := by linarith
-/
#guard_msgs in
example (x y : ℝ) (h : x * y ≤ 2) (hx : x ≤ 1) : True := by
  maximize x * y + x
  trivial

-- So is `x ^ 2`: the bound is `3`, although `x ^ 2 ≤ 3` is not the best bound over `ℝ`.
/--
info: Try this:
  [apply] have : x ^ 2 ≤ 3 := by linarith
-/
#guard_msgs in
example (x : ℝ) (h : x ^ 2 + x ≤ 4) (hx : 1 ≤ x) : True := by
  maximize x ^ 2
  trivial

-- The new hypothesis can be named and used.
/--
info: Try this:
  [apply] have h : x ≤ 1 := by linarith
-/
#guard_msgs in
example (x : ℝ) (hx : x ≤ 1) : x ≤ 1 := by
  maximize x with h
  exact h
