import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import ProbabilityTheory.chapter_03.def_3_10

/--  ## Theorem 5.5
  Helper lemma for Theorem 5.4
-/
theorem thm_5_5 {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (C : Set (Set ℝ)) (hpi : IsPiSystem C)
    (hgen : borel ℝ = MeasurableSpace.generateFrom C)
    (hindep : ∀ A B, A ∈ C → B ∈ C → ProbabilityTheory.IndepSet (X ⁻¹' A) (Y ⁻¹' B) μ) :
    ProbabilityTheory.IndepFun X Y μ := by
  let πX : Set (Set Ω) := Set.preimage X '' C
  let πY : Set (Set Ω) := Set.preimage Y '' C
  have hC_meas : ∀ A, A ∈ C → MeasurableSet A := by
    intro A hA
    have : @MeasurableSet ℝ (borel ℝ) A := by
      rw [hgen]
      exact MeasurableSpace.measurableSet_generateFrom hA
    simpa using this
  have hπX_meas : ∀ s ∈ πX, MeasurableSet s := by
    intro s hs
    rcases hs with ⟨A, hA, rfl⟩
    exact hX (hC_meas A hA)
  have hπY_meas : ∀ t ∈ πY, MeasurableSet t := by
    intro t ht
    rcases ht with ⟨B, hB, rfl⟩
    exact hY (hC_meas B hB)
  have hπX_pi : IsPiSystem πX := by
      convert hpi.comap X
      exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 => a_1) fun ⦃a⦄ a_1 => a_1)
  have hπY_pi : IsPiSystem πY := by
      convert hpi.comap Y
      exact Eq.symm (Set.Subset.antisymm (fun ⦃a⦄ a_1 => a_1) fun ⦃a⦄ a_1 => a_1)
  have hπ_indep : ProbabilityTheory.IndepSets πX πY μ := by
    rw [ProbabilityTheory.IndepSets_iff]
    intro s t hs ht
    rcases hs with ⟨A, hA, rfl⟩
    rcases ht with ⟨B, hB, rfl⟩
    exact
      (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
        (hπX_meas _ ⟨A, hA, rfl⟩)
        (hπY_meas _ ⟨B, hB, rfl⟩)
        (μ := μ)).1 (hindep A B hA hB)
  have hπX_gen : MeasurableSpace.comap X (borel ℝ) = MeasurableSpace.generateFrom πX := by
    rw [hgen, MeasurableSpace.comap_generateFrom]
  have hπY_gen : MeasurableSpace.comap Y (borel ℝ) = MeasurableSpace.generateFrom πY := by
    rw [hgen, MeasurableSpace.comap_generateFrom]
  have hIndep :
      ProbabilityTheory.Indep (MeasurableSpace.comap X (borel ℝ)) (MeasurableSpace.comap Y (borel ℝ)) μ := by
    rw [hπX_gen, hπY_gen]
    exact ProbabilityTheory.IndepSets.indep' hπX_meas hπY_meas hπX_pi hπY_pi hπ_indep
  exact (ProbabilityTheory.IndepFun_iff_Indep X Y μ).2 hIndep
