import ProbabilityTheory.chapter_03.def_3_1
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!   # Definition 3.3   Sigma-Finite Pre-measure

This module defines the concept of a σ-finite pre-measure on a field of sets,
as per the provided definition.
-/

open Set ENNReal Function

/--
# Definition 3.3:
A pre-measure μ₀ defined on F₀ is said to be σ-finite if we can find at most
countably many sets Ωᵢ ∈ F₀, for i = 1, 2, 3, ..., such that ⋃ᵢ Ωᵢ = Ω,
and μ₀(Ωᵢ) < ∞ for all i.
-/
def IsSigmaFinite {Ω : Type*}
    {F₀ : FieldOfSets Ω}
    (μ : Premeasure F₀) : Prop :=
  ∃ (A : ℕ → Set Ω) (hA : ∀ i, A i ∈ F₀.carrier),
    (⋃ i, A i = univ) ∧ (∀ i, μ.μ₀ ⟨A i, hA i⟩ < ∞)
