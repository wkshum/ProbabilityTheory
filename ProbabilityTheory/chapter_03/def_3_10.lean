import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic


/-

 # Definition 3.10  Lambda system and Pi system

-/

open Set

variable {Ω : Type*}

/-- A π-system in Ω is a set system 𝒫 that is closed under intersection. -/
def PiSystem (P : Set (Set Ω)) : Prop :=
  ∀ ⦃A⦄, A ∈ P → ∀ ⦃B⦄, B ∈ P → A ∩ B ∈ P

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
  iUnion_mem : ∀ {f : ℕ → Set Ω}, Pairwise (fun i j => Disjoint (f i) (f j)) → (∀ i, f i ∈ L) → (⋃ i, f i) ∈ L
