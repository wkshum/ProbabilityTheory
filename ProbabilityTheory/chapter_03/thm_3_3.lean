import ProbabilityTheory.chapter_03.def_3_5
-- import Mathlib.Tactic

/-

 # Theorem 3.3 Lebesgue-Stieltjes measure on ℝ

-/

open MeasureTheory Set ENNReal

/--
  ## Theorem 3.3
  We can consturct Lebesgue-Stieltjes measure on ℝ using Stieltjes measure function
  The proof below is an application of Mathlib's API `toStieltjesFunction`
-/
theorem temp_blala (F : StieltjesMeasureFunction) :
    ∃! μ : Measure ℝ, ∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (F b - F a) := by
  refine ⟨F.toStieltjesFunction.measure, ?_, ?_⟩
  · intro a b
    simp [StieltjesMeasureFunction.toStieltjesFunction]
  · intro ν hν
    symm
    apply Measure.ext_of_Ioc F.toStieltjesFunction.measure ν
    intro a b hab
    rw [hν a b]
    simp [StieltjesMeasureFunction.toStieltjesFunction]
