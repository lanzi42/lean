-- 1. Imports always come first
import Mathlib.Algebra.Group.Basic
-- Optional: import tactics like `ring` or `linarith`
import Mathlib.Tactic

-- 2. Compiler or linter options (if any)
-- set_option linter.unusedVariables false

-- 3. The Module Doc-string (Your file documentation goes here)
/-!
# My Real Numbers Theory
This module contains theorems regarding basic operations on `Nat`.
-/


example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x
