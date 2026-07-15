import Mathlib.Tactic
import ProbabilityTheory.chapter_05.def_5_2

/--
   ## Theorem 5.2

   Given random variables X and Y are independent,
   f(X) and g(Y) are independent for any measurable functions f and g

-/
theorem thm_5_2 {Ω β γ β' γ' : Type _}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace β'] [MeasurableSpace γ']
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ)
    (f : β → β') (g : γ → γ')
    (hXY : def_5_2 μ X Y) (hf : Measurable f) (hg : Measurable g) :
    def_5_2 μ (f ∘ X) (g ∘ Y) := by
  have hxy : ProbabilityTheory.IndepFun X Y μ := by
    simpa [def_5_2] using hXY
  simpa [def_5_2, Function.comp] using (ProbabilityTheory.IndepFun.comp (hfg := hxy) hf hg)
