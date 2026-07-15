import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic


/--
  ## Definition 5.10 part 1
  Independence of finitely many random variables

-/

def def_5_10 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : ℕ → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ

/--
  ## Definition 5.10 part 2
  Independence of a sequence of random variables

-/

def def_5_10_randomVariables {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : MeasureTheory.Measure Ω) (X : ℕ → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ
