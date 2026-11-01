-- 1. Imports always come first
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

-- 2. Compiler or linter options (if any)
-- set_option linter.unusedVariables false

-- 3. The Module Doc-string (Your file documentation goes here)
/-!
# My Real Numbers Theory
This module contains theorems regarding basic operations on `Nat`.
-/

open Real

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  --apply? -- this asks Lean 4 to provide an approach
           -- it can be used multiple times, until you get a solution
  --sorry
  refine tsub_le_tsub_left ?_ c
  exact exp_le_exp.mpr h
