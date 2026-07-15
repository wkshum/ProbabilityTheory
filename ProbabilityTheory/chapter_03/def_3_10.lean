import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.PiSystem

/-

 # Definition 3.10  Lambda system and Pi system

-/

open Set

variable {Ω : Type*}


/-- A π-system on `Ω` in the standard sense: a nonempty collection of sets
closed under binary intersections.

 This definition is the same as the definition of pi system in wikipeida.
-/
def PiSystem {Ω : Type*} (P : Set (Set Ω)) : Prop :=
  P.Nonempty ∧ ∀ ⦃A⦄, A ∈ P → ∀ ⦃B⦄, B ∈ P → A ∩ B ∈ P


/-- A λ-system in Ω is a set system ℒ that satisfies the following conditions:
(i) Ω ∈ ℒ.
(ii) If A ∈ ℒ, then Ω \ A ∈ ℒ.
(iii) If Aᵢ is a sequence of mutually disjoint sets in ℒ, then their union is in ℒ. -/
structure LambdaSystem (L : Set (Set Ω)) : Prop where
  /-- (i) The universe Ω is in ℒ. -/
  univ_mem : univ ∈ L
  /-- (ii) If A is in ℒ, its complement (Ω \ A) is in ℒ. -/
  compl_mem : ∀ {A}, A ∈ L → Aᶜ ∈ L
  /-- (iii) If Aᵢ is a sequence of mutually disjoint sets in ℒ, their union is in ℒ. -/
  iUnion_mem : ∀ {f : ℕ → Set Ω}, Pairwise (fun i j => Disjoint (f i) (f j))
    → (∀ i, f i ∈ L) → (⋃ i, f i) ∈ L

/-- Subject to containing the empty set, the standard definition of a π-system is
 equivalent to Mathlib's `IsPiSystem`.

 The extra hypothesis is necessary: unlike `PiSystem`, Mathlib's `IsPiSystem`
 only demands closure when the intersection is nonempty. -/
theorem piSystem_iff_isPiSystem {Ω : Type*} {P : Set (Set Ω)} (empty_mem : ∅ ∈ P) :
    PiSystem P ↔ IsPiSystem P := by
  constructor
  · intro h A hA B hB _
    exact h.2 hA hB
  · intro h
    constructor
    · exact ⟨∅, empty_mem⟩
    · intro A hA B hB
      by_cases hAB : (A ∩ B).Nonempty
      · exact h A hA B hB hAB
      · rw [Set.not_nonempty_iff_eq_empty.mp hAB]
        exact empty_mem



/-- A set family is a custom λ-system exactly when it is the underlying family
 of a Mathlib `DynkinSystem`. -/
theorem lambdaSystem_iff_exists_dynkinSystem {L : Set (Set Ω)} :
    LambdaSystem L ↔
      ∃ d : MeasurableSpace.DynkinSystem Ω, ∀ A : Set Ω, d.Has A ↔ A ∈ L := by
  constructor
  · intro h
    refine ⟨{
      Has := fun A ↦ A ∈ L
      has_empty := by simpa using h.compl_mem h.univ_mem
      has_compl := h.compl_mem
      has_iUnion_nat := h.iUnion_mem
    }, fun _ ↦ Iff.rfl⟩
  · rintro ⟨d, hd⟩
    constructor
    · exact (hd _).mp d.has_univ
    · intro A hA
      exact (hd _).mp (d.has_compl ((hd _).mpr hA))
    · intro f hf hL
      apply (hd _).mp
      exact d.has_iUnion_nat (fun i j hij ↦ by simpa using hf hij) (fun i ↦ (hd _).mpr (hL i))
