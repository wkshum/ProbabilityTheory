import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic

/--

  ## Definition 5.9 Independence of a sequence of collections of sets
-/


def def_5_9 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ
