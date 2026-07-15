import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic

/--

  # Definition 5.8 Independence of finitely many collection of sets

-/


def def_5_8 {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (X : Fin n → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ
