import Mathlib.Tactic
import ProbabilityTheory.chapter_05.def_5_5to10

/-
  ## Theorem 5.7  Mutual indepedence of finitely many events
  expressed in terms of sigmal-algebras
-/
theorem thm_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) :
    def_5_5 μ A ↔ ProbabilityTheory.iIndep (fun k : Fin n => MeasurableSpace.generateFrom {A k}) μ := by
  simpa [def_5_5] using (ProbabilityTheory.iIndepSet_iff_iIndep (s := A) (μ := μ))
