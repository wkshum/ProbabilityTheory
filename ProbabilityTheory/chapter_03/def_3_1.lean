import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Pre-measure on a Field of Sets

This module defines a "field of sets" (also known as an algebra of sets) and the concept
of a "pre-measure" defined on such a field, as per the provided definition.
-/

open Set ENNReal Function

/-- A field of sets (or algebra of sets) over a type `Ω` is a collection of subsets
containing the empty set and closed under complementation and finite unions. -/
structure FieldOfSets (Ω : Type*) where
  carrier : Set (Set Ω)
  empty_mem : ∅ ∈ carrier
  compl_mem : ∀ s ∈ carrier, sᶜ ∈ carrier
  union_mem : ∀ s t, s ∈ carrier → t ∈ carrier → s ∪ t ∈ carrier



/--  # Definition 3.1

A pre-measure μ₀ defined on a field F₀ is a set function from F₀ to [0, ∞]
satisfying the conditions of being null at empty and countably additive for
disjoint unions that remain within the field. -/
structure Premeasure {Ω : Type*} (F₀ : FieldOfSets Ω) where
  /-- The set function mapping sets in the field to the extended non-negative reals. -/
  μ₀ : {s : Set Ω // s ∈ F₀.carrier} → ℝ≥0∞

  /-- Condition 1: The measure of the empty set is 0. -/
  map_empty : μ₀ ⟨∅, F₀.empty_mem⟩ = 0

  /-- Condition 2: Sigma-additivity on the field. If a sequence of mutually disjoint
  sets in the field has its union also in the field, then the measure of the union
  is the sum of the measures. -/
  sigma_additive :
    ∀ (A : ℕ → Set Ω) (hA : ∀ i, A i ∈ F₀.carrier)
    (hU : (⋃ i, A i) ∈ F₀.carrier),
    Pairwise (Disjoint on A) →
    μ₀ ⟨⋃ i, A i, hU⟩ = ∑' i, μ₀ ⟨A i, hA i⟩
