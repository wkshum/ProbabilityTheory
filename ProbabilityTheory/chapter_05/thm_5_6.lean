import Mathlib.Tactic
import ProbabilityTheory.chapter_05.def_5_5to10

/-

## Theorem 5.6

-/


theorem thm_5_6 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) (i : Fin n) (hA : def_5_5 μ A) :
    def_5_5 μ (Function.update A i ((A i)ᶜ)) := by
  let B : Fin n → Set Ω := Function.update A i ((A i)ᶜ)
  have hIndep :
      ProbabilityTheory.iIndep (fun k : Fin n => MeasurableSpace.generateFrom {A k}) μ :=
    (ProbabilityTheory.iIndepSet_iff_iIndep (s := A) (μ := μ)).1 hA
  have hle :
      ∀ j : Fin n, MeasurableSpace.generateFrom {B j} ≤ MeasurableSpace.generateFrom {A j} := by
    intro j
    apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    by_cases hji : j = i
    · subst j
      simpa [B] using
        (MeasurableSpace.measurableSet_generateFrom
          (show A i ∈ ({A i} : Set (Set Ω)) by simp)).compl
    · simpa [B, hji] using
        (MeasurableSpace.measurableSet_generateFrom (show A j ∈ ({A j} : Set (Set Ω)) by simp))
  exact
    (ProbabilityTheory.iIndepSet_iff_iIndep
      (s := B) (μ := μ)).2
      (ProbabilityTheory.iIndep_of_iIndep_of_le hIndep hle)
