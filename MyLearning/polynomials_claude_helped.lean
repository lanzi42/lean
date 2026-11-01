-- 1. Imports always come first
-- Optional: import tactics like `ring` or `linarith`
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# My derivates
This module contains theorems regarding derivates.
-/

open Polynomial
variable {R : Type*} [CommRing R]
-- 2. Compiler or linter options (if any)
--set_option linter.unusedVariables false
--set_option linter.style.whitespace false

-- 3. The Module Doc-string (Your file documentation goes here)

-- 4. start your program

noncomputable def eulerOp (p : R[X]) : R[X] := X * derivative p
noncomputable def opSeries : ℕ → R[X] → R[X]
  | 0     => id
  | n + 1 => eulerOp ∘ opSeries n

-- θ is additive over ℕ-scalars
theorem eulerOp_nsmul (m : ℕ) (p : R[X]) :
    eulerOp (m • p) = m • eulerOp p := by
   rw[eulerOp, derivative_smul, mul_smul_comm, ← eulerOp]


-- θ X^k = k • X^k  (true for all k : ℕ, including 0)
theorem eulerOp_monomial (k : ℕ) :
    eulerOp (X ^ k : R[X]) = k • (X ^ k : R[X]) := by
  unfold eulerOp
  rw [derivative_X_pow]
  cases k with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel, pow_succ, C_eq_natCast, nsmul_eq_mul]
    ring

-- θ^n X^k = k^n • X^k
theorem euler_monomial (n k : ℕ) :
    opSeries n (X ^ k : R[X]) = k ^ n • (X ^ k : R[X]) := by
  induction n with
  | zero => simp [opSeries]
  | succ n ih =>
    simp only [opSeries, Function.comp_apply]
    rw [ih, eulerOp_nsmul, eulerOp_monomial, smul_smul, pow_succ]
