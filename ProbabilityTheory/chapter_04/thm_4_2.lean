import Mathlib.Data.Set.Lattice

/-!  # Theorem 4.2
 Formalization of Preimage Properties

This file formalizes the following properties of the
inverse image:
1. f⁻¹(Aᶜ) = (f⁻¹(A))ᶜ
2. f⁻¹(⋂ Aᵢ) = ⋂ f⁻¹(Aᵢ) and f⁻¹(⋃ Aᵢ) = ⋃ f⁻¹(Aᵢ)
3. If h = g ∘ f, then h⁻¹(B) = f⁻¹(g⁻¹(B))

-/

open Set

universe u v w

variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

/--  ## Theorem 4.2 part 1
The preimage of the complement of a set is the complement of the preimage.
f⁻¹(Aᶜ) = (f⁻¹(A))ᶜ
-/
theorem preimage_compl_distrib : f ⁻¹' (Aᶜ) = (f ⁻¹' A)ᶜ :=
  -- In Lean 4, x ∈ f ⁻¹' Aᶜ is definitionally (f x ∉ A),
  -- and x ∈ (f ⁻¹' A)ᶜ is also definitionally ¬(f x ∈ A).
  rfl

/-- ## Theorem 4.2 part 2a
The preimage of the intersection of a collection is the intersection of the preimages.
f⁻¹(⋂ᵢ Aᵢ) = ⋂ᵢ f⁻¹(Aᵢ)
-/
theorem preimage_iInter_distrib : f ⁻¹' (⋂ i, Ai i) = ⋂ i, f ⁻¹' (Ai i) := by
  ext x
  -- x ∈ f ⁻¹' (⋂ i, Ai i) ↔ f x ∈ ⋂ i, Ai i ↔ ∀ i, f x ∈ Ai i
  -- x ∈ ⋂ i, f ⁻¹' (Ai i) ↔ ∀ i, x ∈ f ⁻¹' (Ai i) ↔ ∀ i, f x ∈ Ai i
  simp only [mem_preimage, mem_iInter]

/-- ## Theorem 4.2 part 2b
The preimage of the union of a collection is the union of the preimages.
f⁻¹(⋃ᵢ Aᵢ) = ⋃ᵢ f⁻¹(Aᵢ)
-/
theorem preimage_iUnion_distrib : f ⁻¹' (⋃ i, Ai i) = ⋃ i, f ⁻¹' (Ai i) := by
  ext x
  -- x ∈ f ⁻¹' (⋃ i, Ai i) ↔ f x ∈ ⋃ i, Ai i ↔ ∃ i, f x ∈ Ai i
  -- x ∈ ⋃ i, f ⁻¹' (Ai i) ↔ ∃ i, x ∈ f ⁻¹' (Ai i) ↔ ∃ i, f x ∈ Ai i
  simp only [mem_preimage, mem_iUnion]

/-- ## Theorem 4.2 part 3
If h = g ∘ f, then h⁻¹(B) = f⁻¹(g⁻¹(B)) for any subset B of the codomain of g.
-/
theorem preimage_comp_distrib (h : Ω → Ω'') (hw : h = g ∘ f) :
    h ⁻¹' B = f ⁻¹' (g ⁻¹' B) := by
  rw [hw]
  -- (g ∘ f) ⁻¹' B is definitionally equal to f ⁻¹' (g ⁻¹' B)
  rfl
