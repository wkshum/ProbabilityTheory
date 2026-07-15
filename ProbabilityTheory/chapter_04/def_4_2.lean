import Mathlib.MeasureTheory.MeasurableSpace.Basic

open Set

/-- ## Definition 4.2 (F,G)-Measurable function

Definition: A function f from a measurable space (Ω, F) to a measurable space (Ω', G)
is called (F, G)-measurable if f⁻¹(B) is F-measurable for all B ∈ G.

In Lean, the measurable space (the σ-algebra) is represented by the `MeasurableSpace`
typeclass. The property of a set belonging to that σ-algebra is `MeasurableSet`.
-/
def IsMeasurable {Ω Ω' : Type*} (F : MeasurableSpace Ω) (G : MeasurableSpace Ω')
    (f : Ω → Ω') : Prop :=
  ∀ B : Set Ω', @MeasurableSet Ω' G B → @MeasurableSet Ω F (f ⁻¹' B)

/-
Note: This is the explicit version of Mathlib's built-in `Measurable` predicate.
Mathlib's `Measurable f` uses typeclass inference to find F and G:
`def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop`
-/
