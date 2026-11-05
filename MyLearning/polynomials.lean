-- 1. Imports always come first
-- Optional: import tactics like `ring` or `linarith`
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# My polynomials
This module contains theorems regarding basic operations on polynomials.
-/

-- for the purpose of learning only, not for publication
set_option pp.explicit true

open Polynomial
variable {R : Type*} [CommRing R]
-- 2. Compiler or linter options (if any)
--set_option linter.unusedVariables false
--set_option linter.style.whitespace false


-- 3. The Module Doc-string (Your file documentation goes here)

-- some simple facts
example (x : R) (n : ℕ) (h : x * (x ^ n) = 1) : x^ (n + 1) = 1 := by
  rw [← pow_succ'] at h
  trivial

example (x : R) (n : ℕ) (h : (x ^ n) * x = 1) : x^ (n + 1) = 1 := by
  rw [mul_comm, ← pow_succ'] at h
  trivial

example (r : R) (u v : ℕ) : (r * u) • v  = r * (u * v) := by  simp [mul_assoc]

example (r : R) (u v : R) : (r * u) • v  = r * (u * v) := by  simp [mul_assoc]

example (f : R[X]) (u v : R) :  u • (v • f) = (u * v) • f := by rw [mul_smul]

example (f : R[X]) (a : ℕ) (b : R) :  b • (a • f) = (b * a : R) • f := by
   rw [← Nat.cast_smul_eq_nsmul R a f, smul_smul]


-- attempt to prove #44 from Problems and Theorems in Analysis  y Polya Vol. I
-- f(z d/dz)z^k = f(k) z^k, where f is a polynomial
-- 1. Define the base Euler operator
noncomputable def eulerOp (p : R[X]) : R[X] :=
  X * derivative p

-- scalar multiplcation
theorem eulerOp_smul (m : R) (p : R[X]) :
    eulerOp (m • p) = m • eulerOp p := by
   rw[eulerOp, derivative_smul, mul_smul_comm, ← eulerOp]

-- 2. Define iteratively θ^n
noncomputable def opSeries (n : ℕ) : R[X] → R[X] :=
  match n with
  | 0     => id
  | mu + 1 => eulerOp ∘ opSeries mu


theorem euler_monomial (n k : ℕ) :
    opSeries n (X ^ k : R[X]) = k ^ n  • (X ^ k : R[X])  := by
  induction n with
  | zero =>
    calc
      opSeries 0 (X ^ k )  = (id  X ^ k)    := by dsimp[opSeries]
        _ = (X ^ k : R[X])                  := rfl
        _ = k ^ 0 • (X ^ k : R[X])          := by rw [pow_zero, one_smul]
        _ = k ^ 0  • (X ^ k : R[X])         := by simp
  | succ n ih =>
    calc
      opSeries (n + 1) (X ^ k : R[X])
          = (eulerOp ∘ opSeries n) (X ^ k : R[X])  := by rw [opSeries]
        _ = eulerOp (opSeries n (X ^ k : R[X]))    := rfl
        _ = eulerOp (k ^ n • (X ^ k : R[X]))       := by simp [ih]
        _ = X * derivative (k ^ n • (X ^ k : R[X])) := rfl
        _ = X * (k ^ n • derivative (X ^ k : R[X])) := by rw [derivative_smul]
        _ = X * (k ^ n • (C (k : R) * X ^ (k - 1))) := by rw [derivative_X_pow]
        _ = X * (k ^ n • (k • X ^ (k - 1)))         := by rw [C_eq_natCast, ← nsmul_eq_mul]
        _ = X * ((k ^ n * k) • X ^ (k - 1))         := by rw [smul_smul]
        _ = (k ^ (n + 1)) • (X * X ^ (k - 1))       := by rw [← pow_succ, mul_smul_comm]
        _ = k ^ (n + 1) • (X ^ k : R[X]) := by
          rcases Nat.eq_zero_or_pos k with h | h
          · subst h
            simp
          · have hX : (X : R[X]) ^ k = X * X ^ (k - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel h]
            rw [hX]



-- step 2, general case
-- Helper: Evaluate a polynomial f at the linear operator θ, then apply it to u
noncomputable def polyEulerOp (f : R[X]) (u : R[X]) : R[X] :=
  f.sum (fun n coeff => coeff • opSeries n u)


lemma polyEulerOp_add (f g : R[X]) (u : R[X]) :
    polyEulerOp (f + g) u = polyEulerOp f u + polyEulerOp g u := by
  dsimp [polyEulerOp]
  rw [Polynomial.sum_add_index]
  · intro n
    exact zero_smul R (opSeries n u)
  · intro n b₁ b₂
    exact add_smul b₁ b₂ (opSeries n u)

theorem polyEulerOp_monomial (f : R[X]) (k : ℕ) :
    polyEulerOp f (X ^ k : R[X]) = (f.eval (k) : R) • (X ^ k : R[X]) := by
  induction f using Polynomial.induction_on' with
  | monomial n r  =>
    calc
      polyEulerOp (monomial n r) (X ^ k : R[X]) = r • (opSeries n (X ^ k)) := by simp [polyEulerOp]
      _ = r • ((k ^ n : ℕ)• X ^ k : R[X])  := by rw [euler_monomial]
      _ = (r * k ^ n : R) • (X ^ k : R[X])  := by
         simp [← Nat.cast_smul_eq_nsmul R (k ^ n) (X ^ k), smul_smul]
      _ = ((Polynomial.monomial n r).eval (k : R)) • (X ^ k : R[X]) := by
         rw [Polynomial.eval_monomial]
        -- case 1: f is a single monomial: rX^n
  | add p q hp hq =>
    calc
      polyEulerOp (p + q) (X ^k : R[X]) =
        polyEulerOp p (X ^ k : R[X]) + polyEulerOp q (X ^ k : R[X]) := by rw[polyEulerOp_add]
      _ = (p.eval (k) : R) • (X ^ k : R[X]) + (q.eval (k) : R) • (X^ k : R[X]) := by rw[hp, hq]
      _ = ((p.eval (k) : R) + (q.eval (k) : R)) • (X ^ k : R[X]) := by rw[← add_smul]
      _ = ((p + q).eval (k) : R) • (X ^ k : R[X]) := by rw[← eval_add]
