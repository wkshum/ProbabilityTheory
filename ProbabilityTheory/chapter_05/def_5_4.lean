import Mathlib.Tactic
import ProbabilityTheory.chapter_05.def_5_1

/-

  # Definition 5.4   Independence of two collection of subsets

-/


def def_5_4 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F₁ F₂ : Set (Set Ω)) : Prop :=
  ProbabilityTheory.IndepSets F₁ F₂ μ
