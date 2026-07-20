import ToyApollo.Output.def_1_2

open Finset BigOperators
open MeasureTheory Set

noncomputable section

/-!
Local support for the Theorem 7.8 simple-function sandwich.

These lemmas expose the half-open cell calculations needed to compare
Lebesgue-Stieltjes integrals of partition step functions with
Riemann-Stieltjes lower and upper sums.
-/

/-- The Stieltjes measure of a half-open cell, as a real number, is the
corresponding increment of the Stieltjes function. -/
theorem thm_7_8_stieltjes_measure_Ioc_toReal
    (F : StieltjesFunction ℝ) {x y : ℝ} (hxy : x ≤ y) :
    (F.measure (Ioc x y)).toReal = F y - F x := by
  rw [F.measure_Ioc x y]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono hxy))

/-- Constant Bochner integrals over a half-open Stieltjes cell reduce to the
Stieltjes increment. -/
theorem thm_7_8_integral_const_Ioc_stieltjes
    (F : StieltjesFunction ℝ) {x y c : ℝ} (hxy : x ≤ y) :
    ∫ _ in Ioc x y, c ∂F.measure = c * (F y - F x) := by
  rw [integral_const]
  rw [Measure.real_def]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter]
  rw [F.measure_Ioc x y]
  have hnonneg : 0 ≤ F y - F x := sub_nonneg.mpr (F.mono hxy)
  rw [ENNReal.toReal_ofReal hnonneg]
  rw [smul_eq_mul]
  ring

/-- Constant integral over the half-open cell of a Definition 1.2 partition. -/
theorem thm_7_8_integral_const_partition_cell
    (F : StieltjesFunction ℝ) {a b c : ℝ} (P : DarbouxRS.Partition a b)
    {i : ℕ} (hi : i < P.n) :
    ∫ _ in Ioc (P.pts i) (P.pts (i + 1)), c ∂F.measure =
      c * (F (P.pts (i + 1)) - F (P.pts i)) := by
  exact thm_7_8_integral_const_Ioc_stieltjes F (le_of_lt (P.strict_mono i hi))

/-- The half-open-cell step function associated to a Definition 1.2 partition
and a list of cell values. -/
def thm_7_8_partitionCellStep {a b : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ∑ i ∈ Finset.range P.n,
    (Ioc (P.pts i) (P.pts (i + 1))).indicator (fun _ : ℝ => v i) x

/-- The source simple functions for Theorem 7.8 have a separate left endpoint
atom and half-open cells to the right. -/
def thm_7_8_partitionCellStepWithLeft {a b : ℝ} (P : DarbouxRS.Partition a b)
    (left : ℝ) (v : ℕ → ℝ) : ℝ → ℝ :=
  fun x => ({a} : Set ℝ).indicator (fun _ : ℝ => left) x +
    thm_7_8_partitionCellStep P v x

/-- Integral of a finite partition-cell step function over the Stieltjes
measure. -/
theorem thm_7_8_integral_partitionCellStep
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) :
    ∫ x, thm_7_8_partitionCellStep P v x ∂F.measure =
      ∑ i ∈ Finset.range P.n, v i * (F (P.pts (i + 1)) - F (P.pts i)) := by
  unfold thm_7_8_partitionCellStep
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt : i < P.n := Finset.mem_range.mp hi
    simpa using
      thm_7_8_integral_const_partition_cell (F := F) (P := P)
        (c := v i) hi_lt
  · intro i hi
    have hi_lt : i < P.n := Finset.mem_range.mp hi
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hfinite : IsFiniteMeasure
        (F.measure.restrict (Ioc (P.pts i) (P.pts (i + 1)))) := by
      rw [isFiniteMeasure_restrict]
      rw [F.measure_Ioc (P.pts i) (P.pts (i + 1))]
      exact ENNReal.ofReal_ne_top
    letI := hfinite
    exact integrable_const (v i)

/-- A half-open partition cell is contained in the parent closed interval. -/
lemma thm_7_8_partition_Ioc_subset_Icc {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n) :
    Ioc (P.pts i) (P.pts (i + 1)) ⊆ Icc a b := by
  intro x hx
  exact DarbouxRS.subinterval_subset_Icc_core P hi
    ⟨le_of_lt hx.1, hx.2⟩

/-- Every point of the closed interval except the left endpoint lies in a
unique right-closed partition cell. -/
lemma thm_7_8_partition_Ioc_cover_Icc_of_ne_left {a b : ℝ}
    (P : DarbouxRS.Partition a b) {x : ℝ} (hx : x ∈ Icc a b)
    (hxne : x ≠ a) :
    ∃ i, i < P.n ∧ x ∈ Ioc (P.pts i) (P.pts (i + 1)) := by
  classical
  let p : ℕ → Prop := fun j => j ≤ P.n ∧ x ≤ P.pts j
  have hp : ∃ j, p j := by
    refine ⟨P.n, le_rfl, ?_⟩
    simpa [p, P.pts_end] using hx.2
  let j := Nat.find hp
  have hj : p j := by
    simpa [j] using Nat.find_spec hp
  have hj_le : j ≤ P.n := hj.1
  have hx_le_j : x ≤ P.pts j := hj.2
  have hj_pos : 0 < j := by
    by_contra hnot
    have hzero : j = 0 := Nat.eq_zero_of_not_pos hnot
    have hxle_a : x ≤ a := by
      simpa [j, hzero, P.pts_start] using hx_le_j
    exact hxne (le_antisymm hxle_a hx.1)
  let i := j - 1
  have hi_succ : i + 1 = j := by
    dsimp [i]
    exact Nat.succ_pred_eq_of_pos hj_pos
  have hi_lt_j : i < j := by
    dsimp [i]
    exact Nat.sub_one_lt (Nat.ne_of_gt hj_pos)
  have hi_lt : i < P.n := lt_of_lt_of_le hi_lt_j hj_le
  refine ⟨i, hi_lt, ?_⟩
  have hnot_prev : ¬ x ≤ P.pts i := by
    intro hxprev
    have hip : p i := ⟨le_of_lt hi_lt, hxprev⟩
    exact (Nat.find_min hp (by simpa [j] using hi_lt_j)) hip
  constructor
  · exact lt_of_not_ge hnot_prev
  · simpa [hi_succ] using hx_le_j

lemma thm_7_8_partition_Ioc_disjoint_at {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i j : ℕ} (hi : i < P.n)
    (hj : j < P.n) (hji : j ≠ i) {x : ℝ}
    (hxi : x ∈ Ioc (P.pts i) (P.pts (i + 1))) :
    x ∉ Ioc (P.pts j) (P.pts (j + 1)) := by
  intro hxj
  rcases Nat.lt_or_gt_of_ne hji with hlt | hgt
  · have hs : j + 1 ≤ i := Nat.succ_le_of_lt hlt
    have hpts : P.pts (j + 1) ≤ P.pts i :=
      DarbouxRS.partition_pts_monotone_core P hs (Nat.le_of_lt hi)
    exact not_lt_of_ge (le_trans hxj.2 hpts) hxi.1
  · have hs : i + 1 ≤ j := Nat.succ_le_of_lt hgt
    have hpts : P.pts (i + 1) ≤ P.pts j :=
      DarbouxRS.partition_pts_monotone_core P hs (Nat.le_of_lt hj)
    exact not_lt_of_ge (le_trans hxi.2 hpts) hxj.1

lemma thm_7_8_partitionCellStep_eq_of_mem_Ioc {a b : ℝ}
    (P : DarbouxRS.Partition a b) (v : ℕ → ℝ) {i : ℕ} (hi : i < P.n)
    {x : ℝ} (hx : x ∈ Ioc (P.pts i) (P.pts (i + 1))) :
    thm_7_8_partitionCellStep P v x = v i := by
  unfold thm_7_8_partitionCellStep
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx (fun _ : ℝ => v i)
  · intro j hj hji
    have hj_lt : j < P.n := Finset.mem_range.mp hj
    have hnot : x ∉ Ioc (P.pts j) (P.pts (j + 1)) :=
      thm_7_8_partition_Ioc_disjoint_at P hi hj_lt hji hx
    exact Set.indicator_of_notMem hnot (fun _ : ℝ => v j)
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hi))

lemma thm_7_8_partitionCellStepWithLeft_eq_of_mem_Ioc {a b left : ℝ}
    (P : DarbouxRS.Partition a b) (v : ℕ → ℝ) {i : ℕ} (hi : i < P.n)
    {x : ℝ} (hxne : x ≠ a)
    (hx : x ∈ Ioc (P.pts i) (P.pts (i + 1))) :
    thm_7_8_partitionCellStepWithLeft P left v x = v i := by
  simp [thm_7_8_partitionCellStepWithLeft, hxne,
    thm_7_8_partitionCellStep_eq_of_mem_Ioc P v hi hx]

lemma thm_7_8_lowerStep_le_of_mem_Ioc
    {a b : ℝ} (P : DarbouxRS.Partition a b) {g : ℝ → ℝ}
    (hBelow : BddBelow (g '' Icc a b)) {i : ℕ} (hi : i < P.n)
    {x : ℝ} (hx : x ∈ Ioc (P.pts i) (P.pts (i + 1))) :
    DarbouxRS.lowerStep P g i ≤ g x := by
  unfold DarbouxRS.lowerStep
  refine csInf_le ?_ ?_
  · exact BddBelow.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hBelow
  · exact ⟨x, ⟨le_of_lt hx.1, hx.2⟩, rfl⟩

lemma thm_7_8_le_upperStep_of_mem_Ioc
    {a b : ℝ} (P : DarbouxRS.Partition a b) {g : ℝ → ℝ}
    (hAbove : BddAbove (g '' Icc a b)) {i : ℕ} (hi : i < P.n)
    {x : ℝ} (hx : x ∈ Ioc (P.pts i) (P.pts (i + 1))) :
    g x ≤ DarbouxRS.upperStep P g i := by
  unfold DarbouxRS.upperStep
  refine le_csSup ?_ ?_
  · exact BddAbove.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hAbove
  · exact ⟨x, ⟨le_of_lt hx.1, hx.2⟩, rfl⟩

theorem thm_7_8_lowerCellStepWithLeft_le_ae
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) (hAtom : F.measure {a} = 0)
    (hBelow : BddBelow (g '' Icc a b)) :
    ∀ᵐ x ∂F.measure, x ∈ Icc a b →
      thm_7_8_partitionCellStepWithLeft P (g a)
        (fun i => DarbouxRS.lowerStep P g i) x ≤ g x := by
  filter_upwards [compl_mem_ae_iff.2 hAtom] with x hxnot hxIcc
  have hxne : x ≠ a := by
    simpa using hxnot
  rcases thm_7_8_partition_Ioc_cover_Icc_of_ne_left P hxIcc hxne with
    ⟨i, hi, hxcell⟩
  rw [thm_7_8_partitionCellStepWithLeft_eq_of_mem_Ioc
    (P := P) (v := fun i => DarbouxRS.lowerStep P g i) hi hxne hxcell]
  exact thm_7_8_lowerStep_le_of_mem_Ioc P hBelow hi hxcell

theorem thm_7_8_le_upperCellStepWithLeft_ae
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) (hAtom : F.measure {a} = 0)
    (hAbove : BddAbove (g '' Icc a b)) :
    ∀ᵐ x ∂F.measure, x ∈ Icc a b →
      g x ≤ thm_7_8_partitionCellStepWithLeft P (g a)
        (fun i => DarbouxRS.upperStep P g i) x := by
  filter_upwards [compl_mem_ae_iff.2 hAtom] with x hxnot hxIcc
  have hxne : x ≠ a := by
    simpa using hxnot
  rcases thm_7_8_partition_Ioc_cover_Icc_of_ne_left P hxIcc hxne with
    ⟨i, hi, hxcell⟩
  rw [thm_7_8_partitionCellStepWithLeft_eq_of_mem_Ioc
    (P := P) (v := fun i => DarbouxRS.upperStep P g i) hi hxne hxcell]
  exact thm_7_8_le_upperStep_of_mem_Ioc P hAbove hi hxcell

/-- Constant indicator over a partition cell has the same integral on `[a,b]`
as on the whole line. -/
theorem thm_7_8_integral_indicator_const_partition_cell_Icc
    (F : StieltjesFunction ℝ) {a b c : ℝ} (P : DarbouxRS.Partition a b)
    {i : ℕ} (hi : i < P.n) :
    ∫ x in Icc a b,
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
      Ioc (P.pts i) (P.pts (i + 1)) ⊆ Icc a b :=
    thm_7_8_partition_Ioc_subset_Icc P hi
  have hcell_inter :
      Ioc (P.pts i) (P.pts (i + 1)) ∩ Icc a b =
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

/-- Integral of a finite partition-cell step function over `[a,b]`. -/
theorem thm_7_8_integral_partitionCellStep_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) :
    ∫ x in Icc a b, thm_7_8_partitionCellStep P v x ∂F.measure =
      ∑ i ∈ Finset.range P.n, v i * (F (P.pts (i + 1)) - F (P.pts i)) := by
  unfold thm_7_8_partitionCellStep
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt : i < P.n := Finset.mem_range.mp hi
    simpa using
      thm_7_8_integral_indicator_const_partition_cell_Icc
        (F := F) (P := P) (c := v i) hi_lt
  · intro i hi
    have hi_lt : i < P.n := Finset.mem_range.mp hi
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hfinite : IsFiniteMeasure
        ((F.measure.restrict (Icc a b)).restrict
          (Ioc (P.pts i) (P.pts (i + 1)))) := by
      rw [isFiniteMeasure_restrict]
      rw [Measure.restrict_apply measurableSet_Ioc]
      have hcell_subset :
          Ioc (P.pts i) (P.pts (i + 1)) ⊆ Icc a b :=
        thm_7_8_partition_Ioc_subset_Icc P hi_lt
      have hcell_inter :
          Ioc (P.pts i) (P.pts (i + 1)) ∩ Icc a b =
            Ioc (P.pts i) (P.pts (i + 1)) := by
        exact inter_eq_self_of_subset_left hcell_subset
      rw [hcell_inter]
      rw [F.measure_Ioc (P.pts i) (P.pts (i + 1))]
      exact ENNReal.ofReal_ne_top
    letI := hfinite
    exact integrable_const (v i)

/-- Partition-cell step functions are integrable on the parent closed
interval. -/
theorem thm_7_8_integrable_partitionCellStep_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) :
    IntegrableOn (thm_7_8_partitionCellStep P v) (Icc a b) F.measure := by
  unfold thm_7_8_partitionCellStep
  exact integrable_finset_sum (Finset.range P.n) (μ := F.measure.restrict (Icc a b))
    (fun i hi => by
      have hi_lt : i < P.n := Finset.mem_range.mp hi
      rw [integrable_indicator_iff measurableSet_Ioc]
      have hfinite : IsFiniteMeasure
          ((F.measure.restrict (Icc a b)).restrict
            (Ioc (P.pts i) (P.pts (i + 1)))) := by
        rw [isFiniteMeasure_restrict]
        rw [Measure.restrict_apply measurableSet_Ioc]
        have hcell_subset :
            Ioc (P.pts i) (P.pts (i + 1)) ⊆ Icc a b :=
          thm_7_8_partition_Ioc_subset_Icc P hi_lt
        have hcell_inter :
            Ioc (P.pts i) (P.pts (i + 1)) ∩ Icc a b =
              Ioc (P.pts i) (P.pts (i + 1)) := by
          exact inter_eq_self_of_subset_left hcell_subset
        rw [hcell_inter]
        rw [F.measure_Ioc (P.pts i) (P.pts (i + 1))]
        exact ENNReal.ofReal_ne_top
      letI := hfinite
      exact integrable_const (v i))

/-- If the left endpoint atom has zero Stieltjes measure, adding the `{a}`
simple-function component does not change the function a.e. on `[a,b]`. -/
theorem thm_7_8_partitionCellStepWithLeft_ae_eq_cellStep
    (F : StieltjesFunction ℝ) {a b left : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) (hAtom : F.measure {a} = 0) :
    thm_7_8_partitionCellStepWithLeft P left v =ᵐ[F.measure.restrict (Icc a b)]
      thm_7_8_partitionCellStep P v := by
  refine ae_restrict_of_ae ?_
  filter_upwards [compl_mem_ae_iff.2 hAtom] with x hx
  have hxne : x ≠ a := by simpa using hx
  simp [thm_7_8_partitionCellStepWithLeft, hxne]

/-- A source `{a}` plus half-open-cell simple function is integrable on
`[a,b]` when the left endpoint atom is zero. -/
theorem thm_7_8_integrable_partitionCellStepWithLeft_Icc
    (F : StieltjesFunction ℝ) {a b left : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) (hAtom : F.measure {a} = 0) :
    IntegrableOn (thm_7_8_partitionCellStepWithLeft P left v) (Icc a b) F.measure := by
  exact (thm_7_8_integrable_partitionCellStep_Icc F P v).congr_fun_ae
    (thm_7_8_partitionCellStepWithLeft_ae_eq_cellStep F P v hAtom).symm

/-- The interval integral of the source `{a}` plus half-open-cell simple
function is the Darboux-style cell sum when the left endpoint atom is zero. -/
theorem thm_7_8_integral_partitionCellStepWithLeft_Icc
    (F : StieltjesFunction ℝ) {a b left : ℝ} (P : DarbouxRS.Partition a b)
    (v : ℕ → ℝ) (hAtom : F.measure {a} = 0) :
    ∫ x in Icc a b, thm_7_8_partitionCellStepWithLeft P left v x ∂F.measure =
      ∑ i ∈ Finset.range P.n, v i * (F (P.pts (i + 1)) - F (P.pts i)) := by
  rw [integral_congr_ae
    (thm_7_8_partitionCellStepWithLeft_ae_eq_cellStep F P v hAtom)]
  exact thm_7_8_integral_partitionCellStep_Icc F P v

/-- The lower cell step integrates to the Definition 1.2 lower
Riemann-Stieltjes sum. -/
theorem thm_7_8_integral_lowerCellStep
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) :
    ∫ x, thm_7_8_partitionCellStep P (fun i => DarbouxRS.lowerStep P g i) x
        ∂F.measure =
      DarbouxRS.lowerSum P g F := by
  rw [thm_7_8_integral_partitionCellStep]
  unfold DarbouxRS.lowerSum
  rfl

/-- The lower cell step integrates over `[a,b]` to the Definition 1.2 lower
Riemann-Stieltjes sum. -/
theorem thm_7_8_integral_lowerCellStep_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) :
    ∫ x in Icc a b,
        thm_7_8_partitionCellStep P (fun i => DarbouxRS.lowerStep P g i) x
        ∂F.measure =
      DarbouxRS.lowerSum P g F := by
  rw [thm_7_8_integral_partitionCellStep_Icc]
  unfold DarbouxRS.lowerSum
  rfl

/-- The upper cell step integrates to the Definition 1.2 upper
Riemann-Stieltjes sum. -/
theorem thm_7_8_integral_upperCellStep
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) :
    ∫ x, thm_7_8_partitionCellStep P (fun i => DarbouxRS.upperStep P g i) x
        ∂F.measure =
      DarbouxRS.upperSum P g F := by
  rw [thm_7_8_integral_partitionCellStep]
  unfold DarbouxRS.upperSum
  rfl

/-- The upper cell step integrates over `[a,b]` to the Definition 1.2 upper
Riemann-Stieltjes sum. -/
theorem thm_7_8_integral_upperCellStep_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) :
    ∫ x in Icc a b,
        thm_7_8_partitionCellStep P (fun i => DarbouxRS.upperStep P g i) x
        ∂F.measure =
      DarbouxRS.upperSum P g F := by
  rw [thm_7_8_integral_partitionCellStep_Icc]
  unfold DarbouxRS.upperSum
  rfl

/-- The source lower simple function, including the `{a}` component, integrates
over `[a,b]` to the Definition 1.2 lower Riemann-Stieltjes sum. -/
theorem thm_7_8_integral_lowerCellStepWithLeft_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) (hAtom : F.measure {a} = 0) :
    ∫ x in Icc a b,
        thm_7_8_partitionCellStepWithLeft P (g a)
          (fun i => DarbouxRS.lowerStep P g i) x ∂F.measure =
      DarbouxRS.lowerSum P g F := by
  rw [thm_7_8_integral_partitionCellStepWithLeft_Icc (hAtom := hAtom)]
  unfold DarbouxRS.lowerSum
  rfl

/-- The source upper simple function, including the `{a}` component, integrates
over `[a,b]` to the Definition 1.2 upper Riemann-Stieltjes sum. -/
theorem thm_7_8_integral_upperCellStepWithLeft_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) (hAtom : F.measure {a} = 0) :
    ∫ x in Icc a b,
        thm_7_8_partitionCellStepWithLeft P (g a)
          (fun i => DarbouxRS.upperStep P g i) x ∂F.measure =
      DarbouxRS.upperSum P g F := by
  rw [thm_7_8_integral_partitionCellStepWithLeft_Icc (hAtom := hAtom)]
  unfold DarbouxRS.upperSum
  rfl

/-- Conditional simple-function sandwich over the interval: once the lower
and upper cell steps bound `g` pointwise on `[a,b]`, their integral identities
turn that pointwise sandwich into the corresponding Darboux-sum sandwich. -/
theorem thm_7_8_cellStep_integral_sandwich
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ)
    (hLower : ∀ x ∈ Icc a b,
      thm_7_8_partitionCellStep P (fun i => DarbouxRS.lowerStep P g i) x ≤ g x)
    (hUpper : ∀ x ∈ Icc a b,
      g x ≤ thm_7_8_partitionCellStep P (fun i => DarbouxRS.upperStep P g i) x)
    (hgInt : IntegrableOn g (Icc a b) F.measure) :
    DarbouxRS.lowerSum P g F ≤ ∫ x in Icc a b, g x ∂F.measure ∧
      ∫ x in Icc a b, g x ∂F.measure ≤ DarbouxRS.upperSum P g F := by
  constructor
  · rw [← thm_7_8_integral_lowerCellStep_Icc (F := F) (P := P) (g := g)]
    exact setIntegral_mono_on
      (thm_7_8_integrable_partitionCellStep_Icc
        (F := F) (P := P) (v := fun i => DarbouxRS.lowerStep P g i))
      hgInt measurableSet_Icc hLower
  · rw [← thm_7_8_integral_upperCellStep_Icc (F := F) (P := P) (g := g)]
    exact setIntegral_mono_on hgInt
      (thm_7_8_integrable_partitionCellStep_Icc
        (F := F) (P := P) (v := fun i => DarbouxRS.upperStep P g i))
      measurableSet_Icc hUpper

/-- Conditional source simple-function sandwich over the interval, with the
left endpoint atom handled internally and only an a.e. sandwich required. -/
theorem thm_7_8_cellStepWithLeft_integral_sandwich
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (g : ℝ → ℝ) (hAtom : F.measure {a} = 0)
    (hLower : ∀ᵐ x ∂F.measure, x ∈ Icc a b →
      thm_7_8_partitionCellStepWithLeft P (g a)
        (fun i => DarbouxRS.lowerStep P g i) x ≤ g x)
    (hUpper : ∀ᵐ x ∂F.measure, x ∈ Icc a b →
      g x ≤ thm_7_8_partitionCellStepWithLeft P (g a)
        (fun i => DarbouxRS.upperStep P g i) x)
    (hgInt : IntegrableOn g (Icc a b) F.measure) :
    DarbouxRS.lowerSum P g F ≤ ∫ x in Icc a b, g x ∂F.measure ∧
      ∫ x in Icc a b, g x ∂F.measure ≤ DarbouxRS.upperSum P g F := by
  constructor
  · rw [← thm_7_8_integral_lowerCellStepWithLeft_Icc
      (F := F) (P := P) (g := g) (hAtom := hAtom)]
    exact setIntegral_mono_on_ae
      (thm_7_8_integrable_partitionCellStepWithLeft_Icc
        (F := F) (P := P) (left := g a)
        (v := fun i => DarbouxRS.lowerStep P g i) hAtom)
      hgInt measurableSet_Icc hLower
  · rw [← thm_7_8_integral_upperCellStepWithLeft_Icc
      (F := F) (P := P) (g := g) (hAtom := hAtom)]
    exact setIntegral_mono_on_ae hgInt
      (thm_7_8_integrable_partitionCellStepWithLeft_Icc
        (F := F) (P := P) (left := g a)
        (v := fun i => DarbouxRS.upperStep P g i) hAtom)
      measurableSet_Icc hUpper

/-- If a fixed value is squeezed between every lower and upper
Riemann-Stieltjes sum and those sums have a common limit, then the fixed value
is that common limit. -/
theorem thm_7_8_common_limit_squeeze
    {a b : ℝ} {g alpha : ℝ → ℝ} {I L : ℝ}
    (hLimit : DarbouxRS.UpperLowerCommonLimit a b g alpha L)
    (hSqueeze : ∀ P : DarbouxRS.Partition a b,
      DarbouxRS.lowerSum P g alpha ≤ I ∧ I ≤ DarbouxRS.upperSum P g alpha) :
    I = L := by
  rcases hLimit with ⟨hs, hlim⟩
  rcases hs with ⟨hab, _hAbove, _hBelow, _hmono⟩
  refine eq_of_forall_dist_le ?_
  intro eps heps
  have hhalf_pos : 0 < eps / 2 := half_pos heps
  rcases hlim (eps / 2) hhalf_pos with ⟨δ, hδ, Hδ⟩
  rcases DarbouxRS.exists_partition_mesh_lt hab hδ with ⟨P, hPmesh⟩
  have hclose := Hδ P hPmesh
  have hsand := hSqueeze P
  have hlow_abs : |DarbouxRS.lowerSum P g alpha - L| < eps / 2 := hclose.2
  have hup_abs : |DarbouxRS.upperSum P g alpha - L| < eps / 2 := hclose.1
  have hlow_gt : L - eps / 2 < DarbouxRS.lowerSum P g alpha := by
    rw [abs_sub_lt_iff] at hlow_abs
    linarith
  have hup_lt : DarbouxRS.upperSum P g alpha < L + eps / 2 := by
    rw [abs_sub_lt_iff] at hup_abs
    linarith
  have hI_abs : |I - L| < eps := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hdist : dist I L < eps := by
    simpa [Real.dist_eq] using hI_abs
  exact le_of_lt hdist

/-- Specialization of the common-limit squeeze to the chosen Definition 1.2
Riemann-Stieltjes integral value. -/
theorem thm_7_8_common_limit_squeeze_rsIntegral
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hRS : RSIntegrable g F a b) {I : ℝ}
    (hSqueeze : ∀ P : DarbouxRS.Partition a b,
      DarbouxRS.lowerSum P g F ≤ I ∧ I ≤ DarbouxRS.upperSum P g F) :
    I = rsIntegral g F a b hRS := by
  exact thm_7_8_common_limit_squeeze
    (hLimit := rsIntegral_source_spec hRS) hSqueeze
