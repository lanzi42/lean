-- 1. Imports always come first
-- Optional: import tactics like `ring` or `linarith`
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# My polynomials
This module contains theorems regarding basic operations on polynomials.
-/

open Polynomial
variable {R : Type*} [CommRing R]
-- 2. Compiler or linter options (if any)
--set_option linter.unusedVariables false
--set_option linter.style.whitespace false

-- 3. The Module Doc-string (Your file documentation goes here)


-- attempt to prove #44 from Problems and Theorems in Analysis  y Polya Vol. I
-- f(z d/dz)z^k = f(k) z^k, where f is a polynomial
-- 1. Define the base Euler operator
noncomputable def eulerOp (p : R[X]) : R[X] :=
  X * derivative p

-- 2. Define iteratively θ^n
noncomputable def opSeries (n : ℕ) : R[X] → R[X] :=
  match n with
  | 0     => id
  | mu + 1 => eulerOp ∘ opSeries mu

theorem euler_monomial (n k : ℕ) :
    opSeries n (X ^ k : R[X]) = k ^ n • (X ^ k : R[X]) := by
  induction n with
  | zero =>
    calc
      opSeries 0 (X ^ k : R[X])
          = id (X ^ k : R[X])                      := by rw [opSeries]
        _ = (X ^ k : R[X])                         := rfl
        _ = k ^ 0 • (X ^ k : R[X])                 := by rw [pow_zero, one_smul]
  | succ n ih =>
    calc
      opSeries (n + 1) (X ^ k : R[X])
          = (eulerOp ∘ opSeries n) (X ^ k : R[X])  := by rw [opSeries]
        _ = eulerOp (opSeries n (X ^ k : R[X]))    := rfl
        _ = eulerOp (k ^ n • (X ^ k : R[X]))       := by rw [ih]
        _ = X * derivative (k ^ n • (X ^ k : R[X])) := rfl
        _ = X * (k ^ n • derivative (X ^ k : R[X])) := by rw [derivative_smul]
        _ = X * (k ^ n • (C (k : R) * X ^ (k - 1))) := by rw [derivative_X_pow]
        _ = X * (k ^ n • (k • X ^ (k - 1)))         := by rw [C_eq_natCast, ← nsmul_eq_mul]
        _ = X * ((k ^ n * k) • X ^ (k - 1))         := by rw [smul_smul]
        _ = k ^ (n + 1) • ( X * X ^ (k - 1))        := by rw [← pow_succ, mul_smul_comm]
        _ = k ^ (n + 1) • (X ^ k : R[X])            := by
           rcases Nat.eq_zero_or_pos k with h | h
           · -- k = 0: both sides are 0
             subst h
             simp
           · -- k > 0: same argument as before, with h in place of hk
             have hX : (X : R[X]) ^ k = X * X ^ (k - 1) := by
               rw [← pow_succ', Nat.sub_add_cancel h]
             rw [hX]


-- step 2, general case
-- Helper: Evaluate a polynomial f at the linear operator θ, then apply it to u
noncomputable def polyEulerOp (f : R[X]) (u : R[X]) : R[X] :=
  f.sum (fun n coeff => coeff • opSeries n u)

theorem polyEulerOp_monomial (f : R[X]) (k : ℕ) :
    polyEulerOp f (X ^ k : R[X]) = f.eval (k : R) • (X ^ k : R[X]) := by
  unfold polyEulerOp
  rw [Polynomial.eval_eq_sum, Polynomial.sum, Polynomial.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [euler_monomial, ← Nat.cast_smul_eq_nsmul R, smul_smul, Nat.cast_pow]
