import Mathlib.Data.Real.Basic

/-

 # Defintiion 3.6 Compact interval in ℝ

-/


/-- A closed and bounded interval in ℝ is called a compact set in ℝ. -/
def IsCompactIntervalSet (s : Set ℝ) : Prop :=
  ∃ a b : ℝ, s = Set.Icc a b
