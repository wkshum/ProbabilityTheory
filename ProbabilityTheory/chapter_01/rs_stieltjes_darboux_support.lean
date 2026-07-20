import ProbabilityTheory.chapter_01.rs_stieltjes_measure_bridge
import ProbabilityTheory.chapter_01.thm_1_2

open MeasureTheory intervalIntegral Set
open scoped Pointwise

noncomputable section

/-!
Darboux algebra and congruence support for the local RS bridge family.
This is a mechanical split from the old mixed `rs_stieltjes_bridge` body.
-/
namespace DarbouxRS

/- Reducible compatibility names for the former namespaced RS surface.  The
current Chapter 1 definitions are top-level, while Chapter 7 historically
referred to them through `DarbouxRS`. -/
abbrev Partition (a b : ℝ) := _root_.Partition a b
abbrev upperStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) :=
  _root_.upperStep P f i
abbrev lowerStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) :=
  _root_.lowerStep P f i
abbrev upperSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) :=
  _root_.upperSum P f alpha
abbrev lowerSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) :=
  _root_.lowerSum P f alpha
abbrev UpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) :=
  _root_.UpperLowerCommonLimit a b f alpha L

theorem exists_partition_mesh_lt {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : Partition a b, P.mesh < δ :=
  _root_.exists_partition_mesh_lt hab hδ

theorem taggedCommonLimit_unique {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ :=
  _root_.taggedCommonLimit_unique h₁ h₂

lemma partition_pts_monotone {a b : ℝ} (P : Partition a b)
    {i j : Fin (P.n + 1)} (hij : i ≤ j) :
    P.pts i ≤ P.pts j :=
  partition_pts_monotone_core P hij

lemma partition_pts_mem_Icc {a b : ℝ} (P : Partition a b)
    {i : Fin (P.n + 1)} :
    P.pts i ∈ Icc a b :=
  partition_pts_mem_Icc_core P

lemma subinterval_subset_Icc {a b : ℝ} (P : Partition a b)
    {i : Fin P.n} :
    _root_.Partition.subinterval P i ⊆ Icc a b :=
  subinterval_subset_Icc_core P

lemma partition_length_le_mesh {a b : ℝ} (P : Partition a b)
    (i : Fin P.n) :
    P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup' (s := (Finset.univ : Finset (Fin P.n)))
    (f := fun j => P.pts j.succ - P.pts j.castSucc) (Finset.mem_univ i)

private lemma sum_adjacent_sub {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) =
      g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun i : Fin (n + 1) => g i.succ)
      have htail' :
          (∑ i : Fin n, (g i.succ.succ - g i.succ.castSucc)) =
            g (Fin.last n).succ - g (Fin.succ 0) := by
        simpa only [Fin.succ_castSucc] using htail
      rw [htail']
      simp

lemma singleJumpStep_monotone {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) :
    Monotone (fun x : ℝ => if x < c then u₁ else u₂) := by
  intro x y hxy
  by_cases hy : y < c
  · have hx : x < c := lt_of_le_of_lt hxy hy
    simp [hx, hy]
  · by_cases hx : x < c
    · simp [hx, hy, hu]
    · simp [hx, hy]

lemma singleJump_increment_nonneg {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂)
    {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ (if y < c then u₁ else u₂) - (if x < c then u₁ else u₂) :=
  sub_nonneg.mpr (singleJumpStep_monotone hu hxy)

lemma singleJump_increment_ne_zero_crosses {x y c u₁ u₂ : ℝ}
    (hxy : x ≤ y)
    (hne : (if y < c then u₁ else u₂) - (if x < c then u₁ else u₂) ≠ 0) :
    x < c ∧ c ≤ y := by
  by_cases hx : x < c
  · by_cases hy : y < c
    · simp [hx, hy] at hne
    · exact ⟨hx, le_of_not_gt hy⟩
  · have hy : ¬ y < c := not_lt.mpr ((le_of_not_gt hx).trans hxy)
    simp [hx, hy] at hne

lemma singleJump_partition_increment_sum {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (hac : a < c) (hcb : c ≤ b) :
    ∑ i : Fin P.n,
      ((if P.pts i.succ < c then u₁ else u₂) -
        (if P.pts i.castSucc < c then u₁ else u₂)) = u₂ - u₁ := by
  have hsum := sum_adjacent_sub
    (fun i : Fin (P.n + 1) => if P.pts i < c then u₁ else u₂)
  have h0 : P.pts 0 < c := by simpa [P.pts_start] using hac
  have hn : ¬ P.pts (Fin.last P.n) < c := by
    have : c ≤ P.pts (Fin.last P.n) := by simpa [P.pts_end] using hcb
    exact not_lt.mpr this
  simpa [h0, hn] using hsum

lemma singleJump_taggedSum_sub_value {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ) (f : ℝ → ℝ)
    (hac : a < c) (hcb : c ≤ b) :
    taggedSum P tags f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁) =
      ∑ i : Fin P.n,
        ((f (tags i) - f c) *
          ((if P.pts i.succ < c then u₁ else u₂) -
            (if P.pts i.castSucc < c then u₁ else u₂))) := by
  have hsum := singleJump_partition_increment_sum
    (P := P) (c := c) (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)
  unfold taggedSum
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma singleJump_upperSum_sub_value {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (f : ℝ → ℝ) (hac : a < c) (hcb : c ≤ b) :
    upperSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁) =
      ∑ i : Fin P.n,
        ((upperStep P f i - f c) *
          ((if P.pts i.succ < c then u₁ else u₂) -
            (if P.pts i.castSucc < c then u₁ else u₂))) := by
  have hsum := singleJump_partition_increment_sum
    (P := P) (c := c) (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)
  unfold DarbouxRS.upperSum _root_.upperSum
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma singleJump_lowerSum_sub_value {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (f : ℝ → ℝ) (hac : a < c) (hcb : c ≤ b) :
    lowerSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁) =
      ∑ i : Fin P.n,
        ((lowerStep P f i - f c) *
          ((if P.pts i.succ < c then u₁ else u₂) -
            (if P.pts i.castSucc < c then u₁ else u₂))) := by
  have hsum := singleJump_partition_increment_sum
    (P := P) (c := c) (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)
  unfold DarbouxRS.lowerSum _root_.lowerSum
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma crossing_tag_abs_sub_le_mesh {a b c : ℝ} {P : Partition a b}
    {tags : Fin P.n → ℝ} (i : Fin P.n) (htags : tagsInPartition P tags)
    (hcross : P.pts i.castSucc < c ∧ c ≤ P.pts i.succ) :
    |tags i - c| ≤ P.mesh := by
  have ht := htags i
  have hlen := partition_length_le_mesh P i
  have habs : |tags i - c| ≤ P.pts i.succ - P.pts i.castSucc := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [ht.1, hcross.2]
    · nlinarith [ht.2, le_of_lt hcross.1]
  exact le_trans habs hlen

lemma crossing_point_abs_sub_le_mesh {a b c x : ℝ} {P : Partition a b}
    (i : Fin P.n) (hx : x ∈ _root_.Partition.subinterval P i)
    (hcross : P.pts i.castSucc < c ∧ c ≤ P.pts i.succ) :
    |x - c| ≤ P.mesh := by
  have hlen := partition_length_le_mesh P i
  have habs : |x - c| ≤ P.pts i.succ - P.pts i.castSucc := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hx.1, hcross.2]
    · nlinarith [hx.2, le_of_lt hcross.1]
  exact le_trans habs hlen

lemma upperStep_abs_sub_le_of_crossing {a b c eta : ℝ} {P : Partition a b}
    {f : ℝ → ℝ} (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hcross : P.pts i.castSucc < c ∧ c ≤ P.pts i.succ)
    (hclose : ∀ x ∈ _root_.Partition.subinterval P i, |f x - f c| < eta) :
    |upperStep P f i - f c| ≤ eta := by
  have hcell_nonempty : (f '' _root_.Partition.subinterval P i).Nonempty := by
    refine ⟨f (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc,
      ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩, rfl⟩
  have hcell_above : BddAbove (f '' _root_.Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc P)) hAbove
  have hupper_le : upperStep P f i ≤ f c + eta := by
    unfold upperStep
    refine csSup_le hcell_nonempty ?_
    rintro y ⟨x, hx, rfl⟩
    linarith [(abs_lt.mp (hclose x hx)).2]
  have hfc_le_upper : f c ≤ upperStep P f i := by
    unfold upperStep
    exact le_csSup hcell_above ⟨c, ⟨le_of_lt hcross.1, hcross.2⟩, rfl⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma lowerStep_abs_sub_le_of_crossing {a b c eta : ℝ} {P : Partition a b}
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Icc a b))
    (hcross : P.pts i.castSucc < c ∧ c ≤ P.pts i.succ)
    (hclose : ∀ x ∈ _root_.Partition.subinterval P i, |f x - f c| < eta) :
    |lowerStep P f i - f c| ≤ eta := by
  have hcell_nonempty : (f '' _root_.Partition.subinterval P i).Nonempty := by
    refine ⟨f (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc,
      ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩, rfl⟩
  have hcell_below : BddBelow (f '' _root_.Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc P)) hBelow
  have hlower_ge : f c - eta ≤ lowerStep P f i := by
    unfold lowerStep
    refine le_csInf hcell_nonempty ?_
    rintro y ⟨x, hx, rfl⟩
    linarith [(abs_lt.mp (hclose x hx)).1]
  have hlower_le_fc : lowerStep P f i ≤ f c := by
    unfold lowerStep
    exact csInf_le hcell_below ⟨c, ⟨le_of_lt hcross.1, hcross.2⟩, rfl⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma upperStep_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} (i : Fin P.n)
    (hfAbove : BddAbove (f '' Icc a b))
    (hgAbove : BddAbove (g '' Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i :=
  upperStep_integrand_add_le_core P i hfAbove hgAbove

lemma lowerStep_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} (i : Fin P.n)
    (hfBelow : BddBelow (f '' Icc a b))
    (hgBelow : BddBelow (g '' Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i :=
  lowerStep_integrand_add_le_core P i hfBelow hgBelow

lemma partition_increment_nonneg_of_source {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
  partition_increment_nonneg_of_source_core P hs

theorem upperSum_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤ upperSum P f alpha + upperSum P g alpha :=
  upperSum_integrand_add_le_core P hsf hsg

theorem lowerSum_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤ lowerSum P (fun x => f x + g x) alpha :=
  lowerSum_integrand_add_le_core P hsf hsg

lemma lowerStep_le_upperStep {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Icc a b))
    (hAbove : BddAbove (f '' Icc a b)) :
    lowerStep P f i ≤ upperStep P f i :=
  lowerStep_le_upperStep_core P i hBelow hAbove

theorem lowerSum_le_upperSum {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha :=
  lowerSum_le_upperSum_core P hs

lemma tag_mem_Icc_of_tagsInPartition {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags) (i : Fin P.n) :
    tags i ∈ Icc a b :=
  tag_mem_Icc_of_tagsInPartition_core P htags i

theorem taggedSum_mono {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
  taggedSum_mono_core P tags hs htags hfg

theorem taggedCommonLimit_mono {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    Lf ≤ Lg :=
  taggedCommonLimit_mono_core hf hg hfg

lemma image_const_mul_subinterval_eq_smul {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) :
    (fun x => c * f x) '' _root_.Partition.subinterval P i =
      c • (f '' _root_.Partition.subinterval P i) :=
  image_const_mul_subinterval_eq_smul_core P f i

lemma upperStep_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    upperStep P (fun x => c * f x) i = c * upperStep P f i :=
  upperStep_const_mul_nonneg_core P f i hc

lemma lowerStep_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    lowerStep P (fun x => c * f x) i = c * lowerStep P f i :=
  lowerStep_const_mul_nonneg_core P f i hc

lemma upperStep_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    upperStep P (fun x => c * f x) i = c * lowerStep P f i :=
  upperStep_const_mul_nonpos_core P f i hc

lemma lowerStep_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    lowerStep P (fun x => c * f x) i = c * upperStep P f i :=
  lowerStep_const_mul_nonpos_core P f i hc

theorem upperLowerCommonLimit_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) :=
  upperLowerCommonLimit_integrand_add_core hf hg

lemma image_const_mul_Icc_eq_smul {a b c : ℝ} (f : ℝ → ℝ) :
    (fun x => c * f x) '' Icc a b = c • (f '' Icc a b) :=
  image_const_mul_Icc_eq_smul_core f

theorem sourceHypotheses_const_mul {a b c : ℝ} {f alpha : ℝ → ℝ}
    (h : SourceHypotheses a b f alpha) :
    SourceHypotheses a b (fun x => c * f x) alpha :=
  sourceHypotheses_const_mul_core h

theorem taggedSum_const_mul {a b c : ℝ} (P : Partition a b)
    (tags : Fin P.n → ℝ) (f alpha : ℝ → ℝ) :
    taggedSum P tags (fun x => c * f x) alpha = c * taggedSum P tags f alpha :=
  taggedSum_const_mul_core P tags f alpha

theorem taggedCommonLimit_const_mul {a b c : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : TaggedCommonLimit a b f alpha L) :
    TaggedCommonLimit a b (fun x => c * f x) alpha (c * L) :=
  taggedCommonLimit_const_mul_core h

theorem upperSum_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    upperSum P (fun x => c * f x) alpha = c * upperSum P f alpha :=
  upperSum_const_mul_nonneg_core P f alpha hc

theorem lowerSum_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    lowerSum P (fun x => c * f x) alpha = c * lowerSum P f alpha :=
  lowerSum_const_mul_nonneg_core P f alpha hc

theorem upperSum_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    upperSum P (fun x => c * f x) alpha = c * lowerSum P f alpha :=
  upperSum_const_mul_nonpos_core P f alpha hc

theorem lowerSum_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    lowerSum P (fun x => c * f x) alpha = c * upperSum P f alpha :=
  lowerSum_const_mul_nonpos_core P f alpha hc

lemma abs_const_mul_error_lt {c old L eps : ℝ}
    (heps : 0 < eps) (hold : |old - L| < eps / (|c| + 1)) :
    |c * (old - L)| < eps :=
  abs_const_mul_error_lt_core heps hold

theorem upperLowerCommonLimit_const_mul {a b c : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    UpperLowerCommonLimit a b (fun x => c * f x) alpha (c * L) :=
  upperLowerCommonLimit_const_mul_core h

theorem singleJump_taggedCommonLimit {f : ℝ → ℝ} {a b c u₁ u₂ : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hu : u₁ < u₂)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcont : ContinuousAt f c) :
    TaggedCommonLimit a b f (fun x => if x < c then u₁ else u₂) (f c * (u₂ - u₁)) := by
  let jump : ℝ := u₂ - u₁
  have hjump_pos : 0 < jump := by
    dsimp [jump]
    exact sub_pos.mpr hu
  refine ⟨?_, ?_⟩
  · refine ⟨lt_of_lt_of_le hac hcb, hAbove, hBelow, ?_⟩
    exact (singleJumpStep_monotone (c := c) hu.le).monotoneOn (Icc a b)
  · intro eps heps
    let eta : ℝ := eps / (jump + 1)
    have hden_pos : 0 < jump + 1 := by positivity
    have heta_pos : 0 < eta := div_pos heps hden_pos
    rcases (Metric.continuousAt_iff.mp hcont) eta heta_pos with ⟨δ, hδ, Hδ⟩
    refine ⟨δ, hδ, ?_⟩
    intro P tags htags hmesh
    rw [singleJump_taggedSum_sub_value (P := P) (tags := tags) (f := f)
      (hac := hac) (hcb := hcb)]
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin P.n)),
        |(f (tags i) - f c) *
          ((if P.pts i.succ < c then u₁ else u₂) -
            (if P.pts i.castSucc < c then u₁ else u₂))| ≤
          eta * ((if P.pts i.succ < c then u₁ else u₂) -
            (if P.pts i.castSucc < c then u₁ else u₂)) := by
      intro i hi
      let inc : ℝ := (if P.pts i.succ < c then u₁ else u₂) -
        (if P.pts i.castSucc < c then u₁ else u₂)
      have hmono_pts : P.pts i.castSucc ≤ P.pts i.succ :=
        le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
      have hinc_nonneg : 0 ≤ inc := by
        dsimp [inc]
        exact singleJump_increment_nonneg hu.le hmono_pts
      by_cases hinc_zero : inc = 0
      · simp [inc, hinc_zero]
      · have hcross := singleJump_increment_ne_zero_crosses hmono_pts
          (by simpa [inc] using hinc_zero)
        have htag_abs_lt : |tags i - c| < δ :=
          lt_of_le_of_lt (crossing_tag_abs_sub_le_mesh (P := P) (tags := tags)
            (i := i) htags hcross) hmesh
        have hclose : |f (tags i) - f c| < eta := by
          have hdist : dist (tags i) c < δ := by
            simpa [Real.dist_eq] using htag_abs_lt
          simpa [Real.dist_eq] using Hδ hdist
        calc
          |(f (tags i) - f c) * inc| = |f (tags i) - f c| * inc := by
            rw [abs_mul, abs_of_nonneg hinc_nonneg]
          _ ≤ eta * inc := mul_le_mul_of_nonneg_right (le_of_lt hclose) hinc_nonneg
    calc
      |∑ i ∈ (Finset.univ : Finset (Fin P.n)),
          ((f (tags i) - f c) *
            ((if P.pts i.succ < c then u₁ else u₂) -
              (if P.pts i.castSucc < c then u₁ else u₂)))|
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
              |((f (tags i) - f c) *
                ((if P.pts i.succ < c then u₁ else u₂) -
                  (if P.pts i.castSucc < c then u₁ else u₂)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
              eta * ((if P.pts i.succ < c then u₁ else u₂) -
                (if P.pts i.castSucc < c then u₁ else u₂)) := Finset.sum_le_sum hterm
      _ = eta * jump := by
        rw [← Finset.mul_sum]
        dsimp [jump]
        rw [singleJump_partition_increment_sum (P := P) (c := c)
          (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)]
      _ < eps := by
        dsimp [eta, jump]
        have hlt_ratio : (u₂ - u₁) / ((u₂ - u₁) + 1) < 1 := by
          have hden : 0 < (u₂ - u₁) + 1 := by positivity
          rw [div_lt_one hden]
          linarith [sub_pos.mpr hu]
        have hmul := mul_lt_mul_of_pos_left hlt_ratio heps
        field_simp [show (u₂ - u₁) + 1 ≠ 0 by positivity] at hmul ⊢
        nlinarith

theorem singleJump_upperLowerCommonLimit {f : ℝ → ℝ} {a b c u₁ u₂ : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hu : u₁ < u₂)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcont : ContinuousAt f c) :
    UpperLowerCommonLimit a b f (fun x => if x < c then u₁ else u₂) (f c * (u₂ - u₁)) := by
  let jump : ℝ := u₂ - u₁
  have hjump_pos : 0 < jump := by
    dsimp [jump]
    exact sub_pos.mpr hu
  refine ⟨?_, ?_⟩
  · refine ⟨lt_of_lt_of_le hac hcb, hAbove, hBelow, ?_⟩
    exact (singleJumpStep_monotone (c := c) hu.le).monotoneOn (Icc a b)
  · intro eps heps
    let eta : ℝ := eps / (jump + 1)
    have hden_pos : 0 < jump + 1 := by positivity
    have heta_pos : 0 < eta := div_pos heps hden_pos
    rcases (Metric.continuousAt_iff.mp hcont) eta heta_pos with ⟨δ, hδ, Hδ⟩
    refine ⟨δ, hδ, ?_⟩
    intro P hmesh
    have hsmall_cell : ∀ i : Fin P.n,
        ((if P.pts i.succ < c then u₁ else u₂) -
          (if P.pts i.castSucc < c then u₁ else u₂)) ≠ 0 →
        ∀ x ∈ _root_.Partition.subinterval P i, |f x - f c| < eta := by
      intro i hne x hx
      have hmono_pts : P.pts i.castSucc ≤ P.pts i.succ := le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
      have hcross := singleJump_increment_ne_zero_crosses hmono_pts hne
      have hx_abs_lt : |x - c| < δ :=
        lt_of_le_of_lt (crossing_point_abs_sub_le_mesh (P := P) (i := i) hx hcross) hmesh
      have hdist : dist x c < δ := by
        simpa [Real.dist_eq] using hx_abs_lt
      simpa [Real.dist_eq] using Hδ hdist
    have hfinal_eta : eta * jump < eps := by
      dsimp [eta, jump]
      have hlt_ratio : (u₂ - u₁) / ((u₂ - u₁) + 1) < 1 := by
        have hden : 0 < (u₂ - u₁) + 1 := by positivity
        rw [div_lt_one hden]
        linarith [sub_pos.mpr hu]
      have hmul := mul_lt_mul_of_pos_left hlt_ratio heps
      field_simp [show (u₂ - u₁) + 1 ≠ 0 by positivity] at hmul ⊢
      nlinarith
    have hsum_bound_upper :
        |upperSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁)| < eps := by
      rw [singleJump_upperSum_sub_value (P := P) (f := f) (hac := hac) (hcb := hcb)]
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin P.n)),
          |(upperStep P f i - f c) *
            ((if P.pts i.succ < c then u₁ else u₂) -
              (if P.pts i.castSucc < c then u₁ else u₂))| ≤
            eta * ((if P.pts i.succ < c then u₁ else u₂) -
              (if P.pts i.castSucc < c then u₁ else u₂)) := by
        intro i hi_mem
        let inc : ℝ := (if P.pts i.succ < c then u₁ else u₂) -
          (if P.pts i.castSucc < c then u₁ else u₂)
        have hmono_pts : P.pts i.castSucc ≤ P.pts i.succ := le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
        have hinc_nonneg : 0 ≤ inc := by
          dsimp [inc]
          exact singleJump_increment_nonneg hu.le hmono_pts
        by_cases hzero : inc = 0
        · simp [inc, hzero]
        · have hcross := singleJump_increment_ne_zero_crosses hmono_pts
            (by simpa [inc] using hzero)
          have hupper_abs : |upperStep P f i - f c| ≤ eta :=
            upperStep_abs_sub_le_of_crossing (P := P) (i := i) hAbove hcross
              (hsmall_cell i (by simpa [inc] using hzero))
          calc
            |(upperStep P f i - f c) * inc| = |upperStep P f i - f c| * inc := by
              rw [abs_mul, abs_of_nonneg hinc_nonneg]
            _ ≤ eta * inc := mul_le_mul_of_nonneg_right hupper_abs hinc_nonneg
      calc
        |∑ i ∈ (Finset.univ : Finset (Fin P.n)),
            ((upperStep P f i - f c) *
              ((if P.pts i.succ < c then u₁ else u₂) -
                (if P.pts i.castSucc < c then u₁ else u₂)))|
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
                |((upperStep P f i - f c) *
                  ((if P.pts i.succ < c then u₁ else u₂) -
                    (if P.pts i.castSucc < c then u₁ else u₂)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
                eta * ((if P.pts i.succ < c then u₁ else u₂) -
                  (if P.pts i.castSucc < c then u₁ else u₂)) := Finset.sum_le_sum hterm
        _ = eta * jump := by
          rw [← Finset.mul_sum]
          dsimp [jump]
          rw [singleJump_partition_increment_sum (P := P) (c := c)
            (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)]
        _ < eps := hfinal_eta
    have hsum_bound_lower :
        |lowerSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁)| < eps := by
      rw [singleJump_lowerSum_sub_value (P := P) (f := f) (hac := hac) (hcb := hcb)]
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin P.n)),
          |(lowerStep P f i - f c) *
            ((if P.pts i.succ < c then u₁ else u₂) -
              (if P.pts i.castSucc < c then u₁ else u₂))| ≤
            eta * ((if P.pts i.succ < c then u₁ else u₂) -
              (if P.pts i.castSucc < c then u₁ else u₂)) := by
        intro i hi_mem
        let inc : ℝ := (if P.pts i.succ < c then u₁ else u₂) -
          (if P.pts i.castSucc < c then u₁ else u₂)
        have hmono_pts : P.pts i.castSucc ≤ P.pts i.succ := le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
        have hinc_nonneg : 0 ≤ inc := by
          dsimp [inc]
          exact singleJump_increment_nonneg hu.le hmono_pts
        by_cases hzero : inc = 0
        · simp [inc, hzero]
        · have hcross := singleJump_increment_ne_zero_crosses hmono_pts
            (by simpa [inc] using hzero)
          have hlower_abs : |lowerStep P f i - f c| ≤ eta :=
            lowerStep_abs_sub_le_of_crossing (P := P) (i := i) hBelow hcross
              (hsmall_cell i (by simpa [inc] using hzero))
          calc
            |(lowerStep P f i - f c) * inc| = |lowerStep P f i - f c| * inc := by
              rw [abs_mul, abs_of_nonneg hinc_nonneg]
            _ ≤ eta * inc := mul_le_mul_of_nonneg_right hlower_abs hinc_nonneg
      calc
        |∑ i ∈ (Finset.univ : Finset (Fin P.n)),
            ((lowerStep P f i - f c) *
              ((if P.pts i.succ < c then u₁ else u₂) -
                (if P.pts i.castSucc < c then u₁ else u₂)))|
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
                |((lowerStep P f i - f c) *
                  ((if P.pts i.succ < c then u₁ else u₂) -
                    (if P.pts i.castSucc < c then u₁ else u₂)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
                eta * ((if P.pts i.succ < c then u₁ else u₂) -
                  (if P.pts i.castSucc < c then u₁ else u₂)) := Finset.sum_le_sum hterm
        _ = eta * jump := by
          rw [← Finset.mul_sum]
          dsimp [jump]
          rw [singleJump_partition_increment_sum (P := P) (c := c)
            (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)]
        _ < eps := hfinal_eta
    exact ⟨hsum_bound_upper, hsum_bound_lower⟩

lemma upperSum_congr_integrator_Icc {a b : ℝ} (P : Partition a b)
    {f α β : ℝ → ℝ}
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    upperSum P f β = upperSum P f α := by
  unfold upperSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hleft : P.pts i.castSucc ∈ Icc a b :=
    partition_pts_mem_Icc P
  have hright : P.pts i.succ ∈ Icc a b :=
    partition_pts_mem_Icc P
  rw [hEq (P.pts i.succ) hright, hEq (P.pts i.castSucc) hleft]

lemma lowerSum_congr_integrator_Icc {a b : ℝ} (P : Partition a b)
    {f α β : ℝ → ℝ}
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    lowerSum P f β = lowerSum P f α := by
  unfold lowerSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hleft : P.pts i.castSucc ∈ Icc a b :=
    partition_pts_mem_Icc P
  have hright : P.pts i.succ ∈ Icc a b :=
    partition_pts_mem_Icc P
  rw [hEq (P.pts i.succ) hright, hEq (P.pts i.castSucc) hleft]

lemma taggedSum_congr_integrator_Icc {a b : ℝ} (P : Partition a b)
    (tags : Fin P.n → ℝ) {f α β : ℝ → ℝ}
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    taggedSum P tags f β = taggedSum P tags f α := by
  unfold taggedSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hleft : P.pts i.castSucc ∈ Icc a b :=
    partition_pts_mem_Icc P
  have hright : P.pts i.succ ∈ Icc a b :=
    partition_pts_mem_Icc P
  rw [hEq (P.pts i.succ) hright, hEq (P.pts i.castSucc) hleft]

lemma sourceHypotheses_congr_integrator_Icc {a b : ℝ} {f α β : ℝ → ℝ}
    (h : SourceHypotheses a b f α)
    (hβmono : MonotoneOn β (Icc a b)) :
    SourceHypotheses a b f β := by
  rcases h with ⟨hab, hAbove, hBelow, _hαmono⟩
  exact ⟨hab, hAbove, hBelow, hβmono⟩

theorem upperLowerCommonLimit_congr_integrator_Icc {a b : ℝ} {f α β : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f α L)
    (hβmono : MonotoneOn β (Icc a b))
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    UpperLowerCommonLimit a b f β L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrator_Icc hs hβmono, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  simpa [upperSum_congr_integrator_Icc P hEq,
    lowerSum_congr_integrator_Icc P hEq] using hP

theorem taggedCommonLimit_congr_integrator_Icc {a b : ℝ} {f α β : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f α L)
    (hβmono : MonotoneOn β (Icc a b))
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    TaggedCommonLimit a b f β L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrator_Icc hs hβmono, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  simpa [taggedSum_congr_integrator_Icc P tags hEq] using hP

lemma upperStep_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} (i : Fin P.n)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    _root_.upperStep P g i = _root_.upperStep P f i := by
  have himage : g '' _root_.Partition.subinterval P i =
      f '' _root_.Partition.subinterval P i := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hx)]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hx)]⟩
  unfold _root_.upperStep
  rw [himage]

lemma lowerStep_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} (i : Fin P.n)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    _root_.lowerStep P g i = _root_.lowerStep P f i := by
  have himage : g '' _root_.Partition.subinterval P i =
      f '' _root_.Partition.subinterval P i := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hx)]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hx)]⟩
  unfold _root_.lowerStep
  rw [himage]

lemma upperSum_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g α : ℝ → ℝ} (hEq : ∀ x ∈ Icc a b, g x = f x) :
    upperSum P g α = upperSum P f α := by
  unfold upperSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [upperStep_congr_integrand_Icc P i hEq]

lemma lowerSum_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g α : ℝ → ℝ} (hEq : ∀ x ∈ Icc a b, g x = f x) :
    lowerSum P g α = lowerSum P f α := by
  unfold lowerSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [lowerStep_congr_integrand_Icc P i hEq]

lemma taggedSum_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    (tags : Fin P.n → ℝ) {f g α : ℝ → ℝ}
    (htags : tagsInPartition P tags)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    taggedSum P tags g α = taggedSum P tags f α := by
  unfold taggedSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have htag : tags i ∈ Icc a b := subinterval_subset_Icc P (htags i)
  rw [hEq (tags i) htag]

lemma sourceHypotheses_congr_integrand_Icc {a b : ℝ} {f g α : ℝ → ℝ}
    (h : SourceHypotheses a b f α)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    SourceHypotheses a b g α := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  have himage : g '' Icc a b = f '' Icc a b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x hx]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x hx]⟩
  exact ⟨hab, by simpa [himage] using hAbove, by simpa [himage] using hBelow, hmono⟩

theorem upperLowerCommonLimit_congr_integrand_Icc {a b : ℝ} {f g α : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f α L)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    UpperLowerCommonLimit a b g α L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrand_Icc hs hEq, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  simpa [upperSum_congr_integrand_Icc P hEq,
    lowerSum_congr_integrand_Icc P hEq] using hP

theorem taggedCommonLimit_congr_integrand_Icc {a b : ℝ} {f g α : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f α L)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    TaggedCommonLimit a b g α L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrand_Icc hs hEq, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  simpa [taggedSum_congr_integrand_Icc P tags htags hEq] using hP

end DarbouxRS
