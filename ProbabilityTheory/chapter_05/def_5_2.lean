import ProbabilityTheory.chapter_05.def_5_1

/-

  # Definition 5.2 Independence of random variables

-/

def def_5_2 {Ω β γ : Type _}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ) : Prop :=
  ProbabilityTheory.IndepFun X Y μ
