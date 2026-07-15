import Mathlib.Probability.Independence.Basic

/--
  ## Definition 5.1 Independence of events

  We use the definition in Mathlib
-/
def def_5_1 {Ω : Type _} [MeasurableSpace Ω]
  (μ : MeasureTheory.Measure Ω) (A B : Set Ω) : Prop :=
  ProbabilityTheory.IndepSet A B μ


/--
For measurable events in a probability space, Mathlib's `IndepSet` definition is
 equivalent to the usual product formula
`P (A ∩ B) = P A * P B`.
-/
example {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    def_5_1 μ A B ↔ μ (A ∩ B) = μ A * μ B := by
  simpa [def_5_1] using
    (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hA hB μ)
