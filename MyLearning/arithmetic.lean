-- 1. Imports always come first
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith   -- For linear arithmetic tactics


-- 2. Compiler or linter options (if any)
-- set_option linter.unusedVariables false

-- 3. The Module Doc-string (Your file documentation goes here)
/-!
# My Natural Numbers Games
This module contains theorems regarding basic operations on `Nat`.
-/

#check 2 + 2

-- 4. Open commands and the rest of your code
open Nat

-- multiplication is associative
example (a b c : ℕ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- zero_add
example (n : ℕ) : 0 + n = n := by
  induction n with
  | zero =>
    rw[add_zero]
  | succ n ih =>
  -- ih: 0 + n = n
  -- need to prove 0 + (succ n) = succ n
  -- add_succ: a + succ (b) = succ (a + b)
    rw[add_succ]
    rw[ih]


-- an example of showing how to deal with ∨
example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h with
  | inl h1 =>
    right
    exact h1
  | inr h2 =>
    left
    exact h2


-- m even implies m * n even
-- even means m = k + k
-- proof by showing m * n = k * n + k * n
example : ∀ m n : Nat, Even m → Even (m * n) := by
  intro m n ⟨k, hk⟩
  rw [hk, add_mul]
  use k * n

-- structured calculation
example (a b c : ℕ) : (a + b) + c = (a + c) + b := by
  calc
    (a + b) + c = a + (b + c) := by rw [add_assoc]
    _           = a + (c + b) := by rw [add_comm b c]
    _           = (a + c) + b := by rw [←add_assoc]


-- try on my own
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  calc
    2 * y = 2 * (x + 7) := by rw[h]

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  repeat rw[add_zero]



example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]


example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith


#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h
