import ToyApollo.Output.thm_7_8

open Finset BigOperators
open MeasureTheory Set
open Topology

noncomputable section

/-!
Half-open finite bridge support for Chapter 7.

The project finite Riemann-Stieltjes sums use increments `F x_{i+1} - F x_i`,
which match the Stieltjes measure of half-open cells `Ioc x_i x_{i+1}`.
This file proves the finite LS/RS bridge on `Ioc a b` without requiring a
left-endpoint atom hypothesis. Closed interval consumers can combine this with
`thm_7_9_endpoint_support`.
-/

lemma thm_7_8_partition_Ioc_subset_Ioc {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n) :
    Ioc (P.pts i) (P.pts (i + 1)) ⊆ Ioc a b := by
  intro x hx
  constructor
  · have hleft : a ≤ P.pts i :=
      (DarbouxRS.partition_pts_mem_Icc_core P (Nat.le_of_lt hi)).1
    exact lt_of_le_of_lt hleft hx.1
  · exact le_trans hx.2
      (DarbouxRS.partition_pts_mem_Icc_core P (Nat.succ_le_of_lt hi)).2

theorem thm_7_8_integral_indicator_const_partition_cell_Ioc
    (F : StieltjesFunction ℝ) {a b c : ℝ} (P : DarbouxRS.Partition a b)
    {i : ℕ} (hi : i < P.n) :
    ∫ x in Ioc a b,
        (Ioc (P.pts i) (P.pts (i + 1))).indicator
          (fun _ : ℝ => c) x ∂F.measure =
      c * (F (P.pts (i + 1)) - F (P.pts i)) := by
  rw [integral_indicator measurableSet_Ioc]
  rw [integral_const]
  rw [Measure.real_def]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter]
  rw [Measure.restrict_apply measurableSet_Ioc]
  have hcell_subset :
      Ioc (P.pts i) (P.pts (i + 1)) ⊆ Ioc a b :=
    thm_7_8_partition_Ioc_subset_Ioc P hi
  have hcell_inter :
      Ioc (P.pts i) (P.pts (i + 1)) ∩ Ioc a b =
        Ioc (P.pts i) (P.pts (i + 1)) := by
    exact inter_eq_self_of_subset_left hcell_subset
  rw [hcell_inter]
  rw [F.measure_Ioc (P.pts i) (P.pts (i + 1))]
  have hnonneg :
      0 ≤ F (P.pts (i + 1)) - F (P.pts i) :=
    sub_nonneg.mpr (F.mono (le_of_lt (P.strict_mono i hi)))
  rw [ENNReal.toReal_ofReal hnonneg]
  rw [smul_eq_mul]
  ring

theorem thm_7_8_integral_partitionCellStep_Ioc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) :
    ∫ x in Ioc a b, thm_7_8_partitionCellStep P v x ∂F.measure =
      ∑ i ∈ Finset.range P.n, v i * (F (P.pts (i + 1)) - F (P.pts i)) := by
  unfold thm_7_8_partitionCellStep
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt : i < P.n := Finset.mem_range.mp hi
    simpa using
      thm_7_8_integral_indicator_const_partition_cell_Ioc
        (F := F) (P := P) (c := v i) hi_lt
  · intro i hi
    have hi_lt : i < P.n := Finset.mem_range.mp hi
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hfinite : IsFiniteMeasure
        ((F.measure.restrict (Ioc a b)).restrict
          (Ioc (P.pts i) (P.pts (i + 1)))) := by
      rw [isFiniteMeasure_restrict]
      rw [Measure.restrict_apply measurableSet_Ioc]
      have hcell_subset :
          Ioc (P.pts i) (P.pts (i + 1)) ⊆ Ioc a b :=
        thm_7_8_partition_Ioc_subset_Ioc P hi_lt
      have hcell_inter :
          Ioc (P.pts i) (P.pts (i + 1)) ∩ Ioc a b =
            Ioc (P.pts i) (P.pts (i + 1)) := by
        exact inter_eq_self_of_subset_left hcell_subset
      rw [hcell_inter]
      rw [F.measure_Ioc (P.pts i) (P.pts (i + 1))]
      exact ENNReal.ofReal_ne_top
    letI := hfinite
    exact integrable_const (v i)

theorem thm_7_8_integrable_partitionCellStep_Ioc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) :
    IntegrableOn (thm_7_8_partitionCellStep P v) (Ioc a b) F.measure := by
  unfold thm_7_8_partitionCellStep
  exact integrable_finset_sum (Finset.range P.n) (μ := F.measure.restrict (Ioc a b))
    (fun i hi => by
      have hi_lt : i < P.n := Finset.mem_range.mp hi
      rw [integrable_indicator_iff measurableSet_Ioc]
      have hfinite : IsFiniteMeasure
          ((F.measure.restrict (Ioc a b)).restrict
            (Ioc (P.pts i) (P.pts (i + 1)))) := by
        rw [isFiniteMeasure_restrict]
        rw [Measure.restrict_apply measurableSet_Ioc]
        have hcell_subset :
            Ioc (P.pts i) (P.pts (i + 1)) ⊆ Ioc a b :=
          thm_7_8_partition_Ioc_subset_Ioc P hi_lt
        have hcell_inter :
            Ioc (P.pts i) (P.pts (i + 1)) ∩ Ioc a b =
              Ioc (P.pts i) (P.pts (i + 1)) := by
          exact inter_eq_self_of_subset_left hcell_subset
        rw [hcell_inter]
        rw [F.measure_Ioc (P.pts i) (P.pts (i + 1))]
        exact ENNReal.ofReal_ne_top
      letI := hfinite
      exact integrable_const (v i))

theorem thm_7_8_integral_lowerCellStep_Ioc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) :
    ∫ x in Ioc a b,
        thm_7_8_partitionCellStep P (fun i => DarbouxRS.lowerStep P g i) x
        ∂F.measure =
      DarbouxRS.lowerSum P g F := by
  rw [thm_7_8_integral_partitionCellStep_Ioc]
  unfold DarbouxRS.lowerSum
  rfl

theorem thm_7_8_integral_upperCellStep_Ioc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) :
    ∫ x in Ioc a b,
        thm_7_8_partitionCellStep P (fun i => DarbouxRS.upperStep P g i) x
        ∂F.measure =
      DarbouxRS.upperSum P g F := by
  rw [thm_7_8_integral_partitionCellStep_Ioc]
  unfold DarbouxRS.upperSum
  rfl

theorem thm_7_8_lowerCellStep_le_on_Ioc
    {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) (hBelow : BddBelow (g '' Icc a b)) :
    ∀ x ∈ Ioc a b,
      thm_7_8_partitionCellStep P (fun i => DarbouxRS.lowerStep P g i) x ≤ g x := by
  intro x hxIoc
  have hxIcc : x ∈ Icc a b := Ioc_subset_Icc_self hxIoc
  have hxne : x ≠ a := by exact ne_of_gt hxIoc.1
  rcases thm_7_8_partition_Ioc_cover_Icc_of_ne_left P hxIcc hxne with
    ⟨i, hi, hxcell⟩
  rw [thm_7_8_partitionCellStep_eq_of_mem_Ioc
    (P := P) (v := fun i => DarbouxRS.lowerStep P g i) hi hxcell]
  exact thm_7_8_lowerStep_le_of_mem_Ioc P hBelow hi hxcell

theorem thm_7_8_le_upperCellStep_on_Ioc
    {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) (hAbove : BddAbove (g '' Icc a b)) :
    ∀ x ∈ Ioc a b,
      g x ≤ thm_7_8_partitionCellStep P (fun i => DarbouxRS.upperStep P g i) x := by
  intro x hxIoc
  have hxIcc : x ∈ Icc a b := Ioc_subset_Icc_self hxIoc
  have hxne : x ≠ a := by exact ne_of_gt hxIoc.1
  rcases thm_7_8_partition_Ioc_cover_Icc_of_ne_left P hxIcc hxne with
    ⟨i, hi, hxcell⟩
  rw [thm_7_8_partitionCellStep_eq_of_mem_Ioc
    (P := P) (v := fun i => DarbouxRS.upperStep P g i) hi hxcell]
  exact thm_7_8_le_upperStep_of_mem_Ioc P hAbove hi hxcell

theorem thm_7_8_cellStep_integral_sandwich_Ioc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ)
    (hLower : ∀ x ∈ Ioc a b,
      thm_7_8_partitionCellStep P (fun i => DarbouxRS.lowerStep P g i) x ≤ g x)
    (hUpper : ∀ x ∈ Ioc a b,
      g x ≤ thm_7_8_partitionCellStep P (fun i => DarbouxRS.upperStep P g i) x)
    (hgInt : IntegrableOn g (Ioc a b) F.measure) :
    DarbouxRS.lowerSum P g F ≤ ∫ x in Ioc a b, g x ∂F.measure ∧
      ∫ x in Ioc a b, g x ∂F.measure ≤ DarbouxRS.upperSum P g F := by
  constructor
  · rw [← thm_7_8_integral_lowerCellStep_Ioc (F := F) (P := P) (g := g)]
    exact setIntegral_mono_on
      (thm_7_8_integrable_partitionCellStep_Ioc
        (F := F) (P := P) (v := fun i => DarbouxRS.lowerStep P g i))
      hgInt measurableSet_Ioc hLower
  · rw [← thm_7_8_integral_upperCellStep_Ioc (F := F) (P := P) (g := g)]
    exact setIntegral_mono_on hgInt
      (thm_7_8_integrable_partitionCellStep_Ioc
        (F := F) (P := P) (v := fun i => DarbouxRS.upperStep P g i))
      measurableSet_Ioc hUpper

theorem thm_7_8_ioc_bridge
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) :
    IntegrableOn g (Ioc a b) F.measure ∧
      ∃ hRS : RSIntegrable g F a b,
        ∫ x in Ioc a b, g x ∂F.measure = rsIntegral g F a b hRS := by
  have hgIntIcc : IntegrableOn g (Icc a b) F.measure :=
    thm_7_8_integrability F hg
  have hgIntIoc : IntegrableOn g (Ioc a b) F.measure :=
    hgIntIcc.mono_set Ioc_subset_Icc_self
  have hRS : RSIntegrable g F a b :=
    thm_7_8_rs_exists F hab hg
  have hAbove : BddAbove (g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  have hSqueeze : ∀ P : DarbouxRS.Partition a b,
      DarbouxRS.lowerSum P g F ≤ ∫ x in Ioc a b, g x ∂F.measure ∧
        ∫ x in Ioc a b, g x ∂F.measure ≤ DarbouxRS.upperSum P g F := by
    intro P
    exact thm_7_8_cellStep_integral_sandwich_Ioc F P g
      (thm_7_8_lowerCellStep_le_on_Ioc P g hBelow)
      (thm_7_8_le_upperCellStep_on_Ioc P g hAbove)
      hgIntIoc
  exact ⟨hgIntIoc, ⟨hRS, thm_7_8_common_limit_squeeze_rsIntegral F hRS hSqueeze⟩⟩
