import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Real.Basic

/-

# Theorem 3.9 Probability measure on R is uniquely determined by Stieltjes measure function

-/

open MeasureTheory Set

/-  ## Theorem 3.9

This theorem is Mathlib's API `MeasureTheory.Measure.ext_of_Iic P Q h`.
-/
theorem thm_3_9 (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  (h : ∀ x : ℝ, P (Iic x) = Q (Iic x)) :
  P = Q := by
    apply_rules [ MeasureTheory.Measure.ext_of_Iic, h ]
