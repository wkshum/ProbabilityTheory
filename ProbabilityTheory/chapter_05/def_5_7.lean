import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic

/--

 ## Definition 5.7 Independence of finitely many collection of sets

-/


def def_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (F : Fin n → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ
