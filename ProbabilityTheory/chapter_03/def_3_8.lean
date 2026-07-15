import Mathlib.MeasureTheory.Measure.MeasureSpace

open scoped ENNReal

/--  # Definition 3.8 Finite Additive and Sigma-subadditive

(i) A set function μ on a field F₀ is said to be finitely additive if for any finite
collection of disjoint sets A₁, A₂, ..., Aₙ in F₀, we have
μ(⋃ Aᵢ) = ∑ μ(Aᵢ).
-/
def IsFinitelyAdditive {α : Type _} (F₀ : Set (Set α)) (μ : Set α → ℝ≥0∞) : Prop :=
  ∀ {n : ℕ} (A : Fin n → Set α),
    (∀ i, A i ∈ F₀) →
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
    μ (Set.iUnion A) = Finset.sum (Finset.univ : Finset (Fin n)) (fun i => μ (A i))

/--
(ii) A set function μ on a field F₀ is called σ-subadditive if for any countable
collection (Aᵢ) of sets in F₀ such that ⋃ Aᵢ ∈ F₀, we have
μ(⋃ Aᵢ) ≤ ∑' μ(Aᵢ).
-/
def IsSigmaSubadditive {α : Type _} (F₀ : Set (Set α)) (μ : Set α → ℝ≥0∞) : Prop :=
  ∀ (A : ℕ → Set α),
    (∀ i, A i ∈ F₀) →
    (Set.iUnion A ∈ F₀) →
    μ (Set.iUnion A) ≤ ∑' i, μ (A i)
