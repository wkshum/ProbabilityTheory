import Mathlib
import ToyApollo.Output.def_1_2

/-!
Prompt-pack-local scratch for `thm_1_4`.

This file targets the derivative tagged-sum bridge.  It is intentionally kept
out of `ToyApollo.Output` and out of `rs_stieltjes_bridge.lean`.
-/

open Set
open MeasureTheory
open scoped BigOperators

namespace Thm14SourceRouteLocal

noncomputable section

lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨w⟩
  exact w.source_limit.1.1

lemma taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    (P : DarbouxRS.Partition a b) (tags : ℕ → ℝ)
    (htags : DarbouxRS.tagsInPartition P tags) :
    DarbouxRS.lowerSum P f α ≤ DarbouxRS.taggedSum P tags f α ∧
      DarbouxRS.taggedSum P tags f α ≤ DarbouxRS.upperSum P f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  constructor
  · unfold DarbouxRS.lowerSum DarbouxRS.taggedSum
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hi : i < P.n := Finset.mem_range.mp hi_mem
    have hcellBelow : BddBelow (f '' DarbouxRS.subinterval P i) :=
      BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hBelow
    have hlow_le_tag : DarbouxRS.lowerStep P f i ≤ f (tags i) := by
      unfold DarbouxRS.lowerStep
      exact csInf_le hcellBelow ⟨tags i, htags i hi, rfl⟩
    have hinc_nonneg : 0 ≤ α (P.pts (i + 1)) - α (P.pts i) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩ hi
    exact mul_le_mul_of_nonneg_right hlow_le_tag hinc_nonneg
  · unfold DarbouxRS.taggedSum DarbouxRS.upperSum
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hi : i < P.n := Finset.mem_range.mp hi_mem
    have hcellAbove : BddAbove (f '' DarbouxRS.subinterval P i) :=
      BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hAbove
    have htag_le_up : f (tags i) ≤ DarbouxRS.upperStep P f i := by
      unfold DarbouxRS.upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i hi, rfl⟩
    have hinc_nonneg : 0 ≤ α (P.pts (i + 1)) - α (P.pts i) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩ hi
    exact mul_le_mul_of_nonneg_right htag_le_up hinc_nonneg

theorem taggedCommonLimit_of_upperLowerCommonLimit {f α : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f α L) :
    rsTaggedCommonLimit a b f α L := by
  rcases hUL with ⟨hs, hlim⟩
  refine ⟨hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := Hδ P hmesh
  have hbetween := taggedSum_between_lower_upper hs P tags htags
  have hlower_abs := abs_lt.mp hP.2
  have hupper_abs := abs_lt.mp hP.1
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

noncomputable def partitionOscillation {a b : ℝ}
    (P : DarbouxRS.Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) *
      (α (P.pts (i + 1)) - α (P.pts i))

lemma upperSum_sub_lowerSum_eq_partitionOscillation {f α : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b) :
    DarbouxRS.upperSum P f α - DarbouxRS.lowerSum P f α =
      partitionOscillation P f α := by
  unfold partitionOscillation DarbouxRS.upperSum DarbouxRS.lowerSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow {f : ℝ → ℝ} {a b : ℝ}
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C := by
  rcases hAbove with ⟨U, hU⟩
  rcases hBelow with ⟨L, hL⟩
  refine ⟨max |U| |L| + 1, ?_, ?_⟩
  · positivity
  · intro x hx
    have hxU : f x ≤ U := hU ⟨x, hx, rfl⟩
    have hxL : L ≤ f x := hL ⟨x, hx, rfl⟩
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hL_abs : -|L| ≤ L := neg_abs_le L
      have hC_abs : |L| ≤ max |U| |L| + 1 := by
        calc
          |L| ≤ max |U| |L| := le_max_right _ _
          _ ≤ max |U| |L| + 1 := by linarith
      linarith
    · have hU_abs : U ≤ |U| := le_abs_self U
      have hC_abs : |U| ≤ max |U| |L| + 1 := by
        calc
          |U| ≤ max |U| |L| := le_max_left _ _
          _ ≤ max |U| |L| + 1 := by linarith
      linarith

lemma upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
    {f : ℝ → ℝ} {a b eta : ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hosc :
      ∀ x, x ∈ DarbouxRS.subinterval P i →
      ∀ y, y ∈ DarbouxRS.subinterval P i → |f x - f y| ≤ eta) :
    DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i ≤ eta := by
  let cell := DarbouxRS.subinterval P i
  have hcell_nonempty : (f '' cell).Nonempty := by
    refine ⟨f (P.pts i), ?_⟩
    refine ⟨P.pts i, ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩
  have hcellAbove : BddAbove (f '' cell) :=
    BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hAbove
  have hcellBelow : BddBelow (f '' cell) :=
    BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hBelow
  have hsup_le :
      sSup (f '' cell) ≤ sInf (f '' cell) + eta := by
    refine csSup_le hcell_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle_inf : f x - eta ≤ sInf (f '' cell) := by
      refine le_csInf hcell_nonempty ?_
      rintro _ ⟨y, hy, rfl⟩
      have hxy : f x - f y ≤ eta := (abs_le.mp (hosc x hx y hy)).2
      linarith
    linarith
  unfold DarbouxRS.upperStep DarbouxRS.lowerStep
  linarith

lemma abs_sub_le_cell_length_of_mem_subinterval {a b x y : ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ}
    (hx : x ∈ DarbouxRS.subinterval P i)
    (hy : y ∈ DarbouxRS.subinterval P i) :
    |x - y| ≤ P.pts (i + 1) - P.pts i := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

lemma partition_length_le_mesh_core {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n) :
    P.pts (i + 1) - P.pts i ≤ P.mesh := by
  unfold DarbouxRS.Partition.mesh
  exact Finset.le_sup'
    (fun j => P.pts (j + 1) - P.pts j)
    (Finset.mem_range.mpr hi)

def ClosedIntervalDarbouxGapSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : DarbouxRS.Partition a b,
    P.mesh < δ →
      DarbouxRS.upperSum P f α - DarbouxRS.lowerSum P f α < eps

end

end Thm14SourceRouteLocal

namespace Thm14DerivativeTaggedScratch

noncomputable section

theorem sourceHypotheses_of_continuous_derivative_integrator {f α : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : Monotone α) :
    DarbouxRS.SourceHypotheses a b f α := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact (isCompact_Icc.image_of_continuousOn hf).bddAbove
  · exact (isCompact_Icc.image_of_continuousOn hf).bddBelow
  · exact hαmono.monotoneOn (Set.Icc a b)

theorem derivative_integrand_continuousOn {f α' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    ContinuousOn (fun x => f x * α' x) (Set.Icc a b) :=
  hf.mul hα'cont

theorem exists_pos_abs_bound_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C := by
  exact Thm14SourceRouteLocal.exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
    (isCompact_Icc.image_of_continuousOn hf).bddAbove
    (isCompact_Icc.image_of_continuousOn hf).bddBelow

theorem partition_length_sum {a b : ℝ} (P : DarbouxRS.Partition a b) :
    (∑ i ∈ Finset.range P.n, (P.pts (i + 1) - P.pts i)) = b - a := by
  have hIco := Finset.sum_Ico_sub (fun k => P.pts k) (Nat.zero_le P.n)
  simpa [P.pts_start, P.pts_end] using hIco

theorem tag_mem_Icc {a b : ℝ} (P : DarbouxRS.Partition a b)
    {tags : ℕ → ℝ} (htags : DarbouxRS.tagsInPartition P tags)
    {i : ℕ} (hi : i < P.n) :
    tags i ∈ Set.Icc a b :=
  DarbouxRS.tag_mem_Icc_of_tagsInPartition_core P htags hi

theorem exists_cell_deriv_eq_increment_slope {α α' : ℝ → ℝ} {a b u v : ℝ}
    (huv : u < v)
    (hsub : Set.Icc u v ⊆ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo u v, α' c = (α v - α u) / (v - u) := by
  refine exists_hasDerivAt_eq_slope α α' huv ?_ ?_
  · intro x hx
    exact (hderiv x (hsub hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact hderiv x (hsub (Set.Ioo_subset_Icc_self hx))

theorem exists_cell_increment_eq_deriv_mul_length {α α' : ℝ → ℝ} {a b u v : ℝ}
    (huv : u < v)
    (hsub : Set.Icc u v ⊆ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo u v, α v - α u = α' c * (v - u) := by
  rcases exists_cell_deriv_eq_increment_slope huv hsub hderiv with ⟨c, hc, hcslope⟩
  refine ⟨c, hc, ?_⟩
  rw [hcslope]
  exact (div_mul_cancel₀ (α v - α u) (sub_ne_zero.mpr huv.ne')).symm

theorem cell_mvt_point {α α' : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo (P.pts i) (P.pts (i + 1)),
      α (P.pts (i + 1)) - α (P.pts i) =
        α' c * (P.pts (i + 1) - P.pts i) := by
  exact exists_cell_increment_eq_deriv_mul_length
    (P.strict_mono i hi)
    (DarbouxRS.subinterval_subset_Icc_core P hi)
    hαderiv

noncomputable def cellMVTTag {α α' : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : ℕ) : ℝ :=
  if hi : i < P.n then
    Classical.choose (cell_mvt_point P hi hαderiv)
  else
    P.pts i

theorem cellMVTTag_mem_Ioo {α α' : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    {i : ℕ} (hi : i < P.n) :
    cellMVTTag P hαderiv i ∈ Set.Ioo (P.pts i) (P.pts (i + 1)) := by
  unfold cellMVTTag
  rw [dif_pos hi]
  exact (Classical.choose_spec (cell_mvt_point P hi hαderiv)).1

theorem cellMVTTag_increment_eq {α α' : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    {i : ℕ} (hi : i < P.n) :
    α (P.pts (i + 1)) - α (P.pts i) =
      α' (cellMVTTag P hαderiv i) * (P.pts (i + 1) - P.pts i) := by
  unfold cellMVTTag
  rw [dif_pos hi]
  exact (Classical.choose_spec (cell_mvt_point P hi hαderiv)).2

theorem cellMVTTag_mem_subinterval {α α' : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    {i : ℕ} (hi : i < P.n) :
    cellMVTTag P hαderiv i ∈ DarbouxRS.subinterval P i := by
  exact Set.Ioo_subset_Icc_self (cellMVTTag_mem_Ioo P hαderiv hi)

theorem cellMVTTag_mem_Icc {α α' : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    {i : ℕ} (hi : i < P.n) :
    cellMVTTag P hαderiv i ∈ Set.Icc a b :=
  DarbouxRS.subinterval_subset_Icc_core P hi
    (cellMVTTag_mem_subinterval P hαderiv hi)

theorem tag_mvt_distance_le_mesh {α α' : ℝ → ℝ} {a b : ℝ}
    (P : DarbouxRS.Partition a b) {tags : ℕ → ℝ}
    (htags : DarbouxRS.tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    {i : ℕ} (hi : i < P.n) :
    |cellMVTTag P hαderiv i - tags i| ≤ P.mesh := by
  have hcell :
      |cellMVTTag P hαderiv i - tags i| ≤ P.pts (i + 1) - P.pts i :=
    Thm14SourceRouteLocal.abs_sub_le_cell_length_of_mem_subinterval P
      (cellMVTTag_mem_subinterval P hαderiv hi)
      (htags i hi)
  exact le_trans hcell (Thm14SourceRouteLocal.partition_length_le_mesh_core P hi)

theorem taggedSum_derivative_identity_abs_le {f α α' : ℝ → ℝ} {a b C eta delta : ℝ}
    (P : DarbouxRS.Partition a b) (tags : ℕ → ℝ)
    (htags : DarbouxRS.tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < delta → |α' x - α' y| ≤ eta)
    (hmesh : P.mesh < delta)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C)
    (hC : 0 ≤ C) :
    |DarbouxRS.taggedSum P tags f α -
        DarbouxRS.taggedSum P tags (fun x => f x * α' x) (fun x => x)| ≤
      C * eta * (b - a) := by
  have hsum_rewrite :
      DarbouxRS.taggedSum P tags f α -
          DarbouxRS.taggedSum P tags (fun x => f x * α' x) (fun x => x) =
        ∑ i ∈ Finset.range P.n,
          (f (tags i) * (α (P.pts (i + 1)) - α (P.pts i)) -
            (f (tags i) * α' (tags i)) * (P.pts (i + 1) - P.pts i)) := by
    unfold DarbouxRS.taggedSum
    rw [← Finset.sum_sub_distrib]
  calc
    |DarbouxRS.taggedSum P tags f α -
        DarbouxRS.taggedSum P tags (fun x => f x * α' x) (fun x => x)|
        = |∑ i ∈ Finset.range P.n,
          (f (tags i) * (α (P.pts (i + 1)) - α (P.pts i)) -
            (f (tags i) * α' (tags i)) * (P.pts (i + 1) - P.pts i))| := by
            rw [hsum_rewrite]
    _ ≤ ∑ i ∈ Finset.range P.n,
          |f (tags i) * (α (P.pts (i + 1)) - α (P.pts i)) -
            (f (tags i) * α' (tags i)) * (P.pts (i + 1) - P.pts i)| := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range P.n,
          C * eta * (P.pts (i + 1) - P.pts i) := by
            refine Finset.sum_le_sum ?_
            intro i hi_mem
            have hi : i < P.n := Finset.mem_range.mp hi_mem
            let c := cellMVTTag P hαderiv i
            have hc_eq :
                α (P.pts (i + 1)) - α (P.pts i) =
                  α' c * (P.pts (i + 1) - P.pts i) := by
              simpa [c] using cellMVTTag_increment_eq P hαderiv hi
            have htagI : tags i ∈ Set.Icc a b := tag_mem_Icc P htags hi
            have hcI : c ∈ Set.Icc a b := by
              simpa [c] using cellMVTTag_mem_Icc P hαderiv hi
            have hdist : |c - tags i| < delta := by
              have hle : |c - tags i| ≤ P.mesh := by
                simpa [c] using tag_mvt_distance_le_mesh P htags hαderiv hi
              exact lt_of_le_of_lt hle hmesh
            have hosc : |α' c - α' (tags i)| ≤ eta :=
              hα'osc c hcI (tags i) htagI hdist
            have hfbound : |f (tags i)| ≤ C := hbound (tags i) htagI
            have hlen_nonneg : 0 ≤ P.pts (i + 1) - P.pts i :=
              sub_nonneg.mpr (le_of_lt (P.strict_mono i hi))
            have hprod :
                |f (tags i)| * |α' c - α' (tags i)| *
                    (P.pts (i + 1) - P.pts i) ≤
                  C * eta * (P.pts (i + 1) - P.pts i) := by
              have hmul₁ :
                  |f (tags i)| * |α' c - α' (tags i)| ≤ C * eta :=
                mul_le_mul hfbound hosc (abs_nonneg _) hC
              exact mul_le_mul_of_nonneg_right hmul₁ hlen_nonneg
            have hterm_eq :
                f (tags i) * (α (P.pts (i + 1)) - α (P.pts i)) -
                    (f (tags i) * α' (tags i)) *
                      (P.pts (i + 1) - P.pts i) =
                  f (tags i) * (α' c - α' (tags i)) *
                    (P.pts (i + 1) - P.pts i) := by
              rw [hc_eq]
              ring
            rw [hterm_eq, abs_mul, abs_mul, abs_of_nonneg hlen_nonneg]
            exact hprod
    _ = C * eta * (b - a) := by
            rw [← Finset.mul_sum]
            rw [partition_length_sum P]

theorem cell_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n) :
    DarbouxRS.lowerStep P g i * (P.pts (i + 1) - P.pts i) ≤
        ∫ x in P.pts i..P.pts (i + 1), g x ∧
      ∫ x in P.pts i..P.pts (i + 1), g x ≤
        DarbouxRS.upperStep P g i * (P.pts (i + 1) - P.pts i) := by
  have huv : P.pts i ≤ P.pts (i + 1) := le_of_lt (P.strict_mono i hi)
  have hgcell : ContinuousOn g (Set.Icc (P.pts i) (P.pts (i + 1))) :=
    hg.mono (DarbouxRS.subinterval_subset_Icc_core P hi)
  have hgi : IntervalIntegrable g volume (P.pts i) (P.pts (i + 1)) :=
    ContinuousOn.intervalIntegrable_of_Icc huv hgcell
  have hconstLower :
      IntervalIntegrable (fun _ : ℝ => DarbouxRS.lowerStep P g i) volume
        (P.pts i) (P.pts (i + 1)) :=
    continuous_const.intervalIntegrable _ _
  have hconstUpper :
      IntervalIntegrable (fun _ : ℝ => DarbouxRS.upperStep P g i) volume
        (P.pts i) (P.pts (i + 1)) :=
    continuous_const.intervalIntegrable _ _
  have hcellBelow : BddBelow (g '' DarbouxRS.subinterval P i) := by
    exact (isCompact_Icc.image_of_continuousOn hgcell).bddBelow
  have hcellAbove : BddAbove (g '' DarbouxRS.subinterval P i) := by
    exact (isCompact_Icc.image_of_continuousOn hgcell).bddAbove
  have hLowerPoint :
      ∀ x ∈ Set.Icc (P.pts i) (P.pts (i + 1)), DarbouxRS.lowerStep P g i ≤ g x := by
    intro x hx
    unfold DarbouxRS.lowerStep
    exact csInf_le hcellBelow ⟨x, hx, rfl⟩
  have hUpperPoint :
      ∀ x ∈ Set.Icc (P.pts i) (P.pts (i + 1)), g x ≤ DarbouxRS.upperStep P g i := by
    intro x hx
    unfold DarbouxRS.upperStep
    exact le_csSup hcellAbove ⟨x, hx, rfl⟩
  have hLowerIntegral :
      (∫ x in P.pts i..P.pts (i + 1), DarbouxRS.lowerStep P g i) ≤
        ∫ x in P.pts i..P.pts (i + 1), g x :=
    intervalIntegral.integral_mono_on huv hconstLower hgi hLowerPoint
  have hUpperIntegral :
      (∫ x in P.pts i..P.pts (i + 1), g x) ≤
        ∫ x in P.pts i..P.pts (i + 1), DarbouxRS.upperStep P g i :=
    intervalIntegral.integral_mono_on huv hgi hconstUpper hUpperPoint
  constructor
  · calc
      DarbouxRS.lowerStep P g i * (P.pts (i + 1) - P.pts i)
          = ∫ x in P.pts i..P.pts (i + 1), DarbouxRS.lowerStep P g i := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]
      _ ≤ ∫ x in P.pts i..P.pts (i + 1), g x := hLowerIntegral
  · calc
      ∫ x in P.pts i..P.pts (i + 1), g x
          ≤ ∫ x in P.pts i..P.pts (i + 1), DarbouxRS.upperStep P g i := hUpperIntegral
      _ = DarbouxRS.upperStep P g i * (P.pts (i + 1) - P.pts i) := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]

theorem partition_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : DarbouxRS.Partition a b) :
    DarbouxRS.lowerSum P g (fun x => x) ≤ ∫ x in a..b, g x ∧
      ∫ x in a..b, g x ≤ DarbouxRS.upperSum P g (fun x => x) := by
  have hcellInt :
      ∀ k < P.n, IntervalIntegrable g volume (P.pts k) (P.pts (k + 1)) := by
    intro k hk
    have huv : P.pts k ≤ P.pts (k + 1) := le_of_lt (P.strict_mono k hk)
    have hgcell : ContinuousOn g (Set.Icc (P.pts k) (P.pts (k + 1))) :=
      hg.mono (DarbouxRS.subinterval_subset_Icc_core P hk)
    exact ContinuousOn.intervalIntegrable_of_Icc huv hgcell
  have hsumIntegral :
      (∑ k ∈ Finset.range P.n, ∫ x in P.pts k..P.pts (k + 1), g x) =
        ∫ x in a..b, g x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hcellInt]
    rw [P.pts_start, P.pts_end]
  have hlowerSum :
      (∑ k ∈ Finset.range P.n,
          DarbouxRS.lowerStep P g k * (P.pts (k + 1) - P.pts k)) ≤
        ∑ k ∈ Finset.range P.n, ∫ x in P.pts k..P.pts (k + 1), g x := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact (cell_integral_between_lower_upper_id hg P (Finset.mem_range.mp hk)).1
  have hupperSum :
      (∑ k ∈ Finset.range P.n, ∫ x in P.pts k..P.pts (k + 1), g x) ≤
        ∑ k ∈ Finset.range P.n,
          DarbouxRS.upperStep P g k * (P.pts (k + 1) - P.pts k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact (cell_integral_between_lower_upper_id hg P (Finset.mem_range.mp hk)).2
  constructor
  · calc
      DarbouxRS.lowerSum P g (fun x => x)
          = ∑ k ∈ Finset.range P.n,
              DarbouxRS.lowerStep P g k * (P.pts (k + 1) - P.pts k) := by
            unfold DarbouxRS.lowerSum
            simp
      _ ≤ ∑ k ∈ Finset.range P.n, ∫ x in P.pts k..P.pts (k + 1), g x := hlowerSum
      _ = ∫ x in a..b, g x := hsumIntegral
  · calc
      ∫ x in a..b, g x
          = ∑ k ∈ Finset.range P.n, ∫ x in P.pts k..P.pts (k + 1), g x :=
            hsumIntegral.symm
      _ ≤ ∑ k ∈ Finset.range P.n,
              DarbouxRS.upperStep P g k * (P.pts (k + 1) - P.pts k) := hupperSum
      _ = DarbouxRS.upperSum P g (fun x => x) := by
            unfold DarbouxRS.upperSum
            simp

theorem upper_lower_gap_small_continuous_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    Thm14SourceRouteLocal.ClosedIntervalDarbouxGapSmall a b g (fun x => x) := by
  intro eps heps
  let eta : ℝ := eps / (b - a + 1)
  have hspan_nonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt hab)
  have hden_pos : 0 < b - a + 1 := by linarith
  have heta_pos : 0 < eta := div_pos heps hden_pos
  have hsmall_eta_span : eta * (b - a) < eps := by
    have hspan_lt : b - a < b - a + 1 := by linarith
    have hmul_lt := mul_lt_mul_of_pos_left hspan_lt heta_pos
    have heta_den : eta * (b - a + 1) = eps := by
      dsimp [eta]
      field_simp [ne_of_gt hden_pos]
    linarith
  have hunif : UniformContinuousOn g (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  rcases (Metric.uniformContinuousOn_iff.mp hunif eta heta_pos) with
    ⟨δ, hδ_pos, Hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hAbove : BddAbove (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  have hstep :
      ∀ i : ℕ, i < P.n →
        DarbouxRS.upperStep P g i - DarbouxRS.lowerStep P g i ≤ eta := by
    intro i hi
    refine Thm14SourceRouteLocal.upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      P hi hAbove hBelow ?_
    intro x hx y hy
    have hxI : x ∈ Set.Icc a b := DarbouxRS.subinterval_subset_Icc_core P hi hx
    have hyI : y ∈ Set.Icc a b := DarbouxRS.subinterval_subset_Icc_core P hi hy
    have hxy_len : |x - y| ≤ P.pts (i + 1) - P.pts i :=
      Thm14SourceRouteLocal.abs_sub_le_cell_length_of_mem_subinterval P hx hy
    have hlen_mesh : P.pts (i + 1) - P.pts i ≤ P.mesh :=
      Thm14SourceRouteLocal.partition_length_le_mesh_core P hi
    have hdist : dist x y < δ := by
      simpa [Real.dist_eq] using lt_of_le_of_lt (le_trans hxy_len hlen_mesh) hmesh
    exact le_of_lt (by
      simpa [Real.dist_eq] using Hδ x hxI y hyI hdist)
  have hosc_le :
      Thm14SourceRouteLocal.partitionOscillation P g (fun x => x) ≤ eta * (b - a) := by
    unfold Thm14SourceRouteLocal.partitionOscillation
    have htel :
        (∑ i ∈ Finset.range P.n, (P.pts (i + 1) - P.pts i)) = b - a :=
      partition_length_sum P
    calc
      (∑ i ∈ Finset.range P.n,
          (DarbouxRS.upperStep P g i - DarbouxRS.lowerStep P g i) *
            ((fun x : ℝ => x) (P.pts (i + 1)) - (fun x : ℝ => x) (P.pts i)))
          ≤ ∑ i ∈ Finset.range P.n,
              eta * (P.pts (i + 1) - P.pts i) := by
            refine Finset.sum_le_sum ?_
            intro i hi_mem
            have hi : i < P.n := Finset.mem_range.mp hi_mem
            have hlen_nonneg : 0 ≤ P.pts (i + 1) - P.pts i :=
              sub_nonneg.mpr (le_of_lt (P.strict_mono i hi))
            simpa using mul_le_mul_of_nonneg_right (hstep i hi) hlen_nonneg
      _ = eta * (b - a) := by
            rw [← Finset.mul_sum, htel]
  calc
    DarbouxRS.upperSum P g (fun x => x) - DarbouxRS.lowerSum P g (fun x => x)
        = Thm14SourceRouteLocal.partitionOscillation P g (fun x => x) :=
          Thm14SourceRouteLocal.upperSum_sub_lowerSum_eq_partitionOscillation P
    _ ≤ eta * (b - a) := hosc_le
    _ < eps := hsmall_eta_span

theorem rsUpperLowerCommonLimit_intervalIntegral_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsUpperLowerCommonLimit a b g (fun x => x) (∫ x in a..b, g x) := by
  have hAbove : BddAbove (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  refine ⟨⟨hab, hAbove, hBelow, monotoneOn_id⟩, ?_⟩
  intro eps heps
  rcases upper_lower_gap_small_continuous_id hab hg eps heps with ⟨δ, hδ_pos, Hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hbetween := partition_integral_between_lower_upper_id hg P
  have hgap := Hδ P hmesh
  constructor
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith

theorem rsTaggedCommonLimit_intervalIntegral_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsTaggedCommonLimit a b g (fun x => x) (∫ x in a..b, g x) :=
  Thm14SourceRouteLocal.taggedCommonLimit_of_upperLowerCommonLimit
    (rsUpperLowerCommonLimit_intervalIntegral_id hab hg)

theorem rsTaggedCommonLimit_derivative_of_identity_tagged_limit
    {f α α' : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : Monotone α)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b))
    (hId : rsTaggedCommonLimit a b (fun x => f x * α' x) (fun x => x) L) :
    rsTaggedCommonLimit a b f α L := by
  refine ⟨sourceHypotheses_of_continuous_derivative_integrator hab hf hαmono, ?_⟩
  intro eps heps
  rcases exists_pos_abs_bound_of_continuousOn hf with ⟨C, hCpos, hCbound⟩
  let eta : ℝ := eps / (4 * C * (b - a))
  have hspan_pos : 0 < b - a := sub_pos.mpr hab
  have hden_pos : 0 < 4 * C * (b - a) := by positivity
  have heta_pos : 0 < eta := div_pos heps hden_pos
  have hdiff_budget : C * eta * (b - a) < eps / 2 := by
    have hcalc : C * eta * (b - a) = eps / 4 := by
      dsimp [eta]
      field_simp [ne_of_gt hCpos, ne_of_gt hspan_pos]
    linarith
  have hunif : UniformContinuousOn α' (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hα'cont
  rcases (Metric.uniformContinuousOn_iff.mp hunif eta heta_pos) with
    ⟨δA, hδApos, HδA⟩
  rcases hId with ⟨_hsId, hlimId⟩
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimId (eps / 2) hhalf with ⟨δI, hδIpos, HδI⟩
  refine ⟨min δA δI, lt_min hδApos hδIpos, ?_⟩
  intro P tags htags hmesh
  have hmeshA : P.mesh < δA := lt_of_lt_of_le hmesh (min_le_left δA δI)
  have hmeshI : P.mesh < δI := lt_of_lt_of_le hmesh (min_le_right δA δI)
  have hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < δA → |α' x - α' y| ≤ eta := by
    intro x hx y hy hxy
    have hdist : dist x y < δA := by
      simpa [Real.dist_eq] using hxy
    have h := HδA x hx y hy hdist
    exact le_of_lt (by simpa [Real.dist_eq] using h)
  let Sid : ℝ := DarbouxRS.taggedSum P tags (fun x => f x * α' x) (fun x => x)
  have hdiff :
      |DarbouxRS.taggedSum P tags f α - Sid| < eps / 2 := by
    have hle :
        |DarbouxRS.taggedSum P tags f α - Sid| ≤ C * eta * (b - a) := by
      simpa [Sid] using
        taggedSum_derivative_identity_abs_le
          (f := f) (α := α) (α' := α') (a := a) (b := b)
          (C := C) (eta := eta) (delta := δA)
          P tags htags hαderiv hα'osc hmeshA hCbound (le_of_lt hCpos)
    exact lt_of_le_of_lt hle hdiff_budget
  have hIdClose : |Sid - L| < eps / 2 := by
    simpa [Sid] using HδI P tags htags hmeshI
  have htriangle :
      |DarbouxRS.taggedSum P tags f α - L| ≤
        |DarbouxRS.taggedSum P tags f α - Sid| + |Sid - L| := by
    have hdecomp :
        DarbouxRS.taggedSum P tags f α - L =
          (DarbouxRS.taggedSum P tags f α - Sid) + (Sid - L) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |DarbouxRS.taggedSum P tags f α - L|
        ≤ |DarbouxRS.taggedSum P tags f α - Sid| + |Sid - L| := htriangle
    _ < eps / 2 + eps / 2 := add_lt_add hdiff hIdClose
    _ = eps := by ring

theorem rsTaggedCommonLimit_integral_deriv
    {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : Monotone α)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) := by
  exact rsTaggedCommonLimit_derivative_of_identity_tagged_limit
    hab hf hαmono hαderiv hα'cont
    (rsTaggedCommonLimit_intervalIntegral_id hab
      (derivative_integrand_continuousOn hf hα'cont))

end

end Thm14DerivativeTaggedScratch

/-- Theorem 1.4: if the integrator has a continuous derivative, the
Riemann--Stieltjes integral reduces to the ordinary Riemann integral against
that derivative. -/
theorem thm_1_4 {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hαmono : Monotone α)
    (hαderiv : ∀ x ∈ Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Icc a b))
    (hRS : RSIntegrable f α a b) :
    IntervalIntegrable (fun x => f x * α' x) volume a b ∧
      rsIntegral f α a b hRS = ∫ x in a..b, f x * α' x := by
  have hInt :
      IntervalIntegrable (fun x => f x * α' x) volume a b :=
    (hf.mul hα'cont).intervalIntegrable_of_Icc hab
  have hstrict : a < b :=
    Thm14SourceRouteLocal.strict_interval_of_rsIntegrable hRS
  have hTagged :
      rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) :=
    Thm14DerivativeTaggedScratch.rsTaggedCommonLimit_integral_deriv
      hstrict hf hαmono hαderiv hα'cont
  refine ⟨hInt, ?_⟩
  exact DarbouxRS.taggedCommonLimit_unique (rsIntegral_spec hRS) hTagged

