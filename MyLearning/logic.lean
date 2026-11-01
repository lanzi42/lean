-- 1. Imports always come first
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith   -- For linear arithmetic tactics

-- 2. Compiler or linter options (if any)
-- set_option linter.unusedVariables false

-- 3. The Module Doc-string (Your file documentation goes here)
/-!
# Formal logic
This module contains theorems regarding logic
-/

example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := by
  constructor
  case left =>
    exact show p from H_p
  case right =>
    exact show q from H_q


example (P : Prop) : ¬ ¬ P → P := by
  intro hnnP           -- ¬ ¬ P
  by_contra hnP        -- Goal becomes `False`, context gets `hnP : ¬ P`
  exact hnnP hnP       -- Derive False and finish proof


theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  contrapose           --Goal is now P → ¬R
  intro (h3 : P)
  have h4 : Q := h1 h3
  change ¬R
  exact h2 h4

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

#check m + 0
#check b1
#check b1 || b2
