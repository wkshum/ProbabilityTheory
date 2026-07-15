import ProbabilityTheory.chapter_03.def_3_10
import Mathlib.MeasureTheory.PiSystem

/-
  # Theorem 3.7 (π-λ Theorem)
  If L is a λ-system containing a π-system P, then σ(P) ⊆ L.
-/

open MeasurableSpace

/--

  ## Theorem 3.7 pi-lambda theorem

-/
theorem thm_3_7 {α : Type*} {P : Set (Set α)} {L : DynkinSystem α}
  (hP : IsPiSystem P) (hPL : ∀ s ∈ P, L.Has s) :
  ∀ s, @MeasurableSet α (generateFrom P) s → L.Has s := by
  intro s hs
  have h := DynkinSystem.generateFrom_eq hP
  rw [h] at hs
  change (DynkinSystem.generate P).Has s at hs
  have key : DynkinSystem.generate P ≤ L := DynkinSystem.generate_le L hPL
  exact (DynkinSystem.le_def.mp key) s hs
