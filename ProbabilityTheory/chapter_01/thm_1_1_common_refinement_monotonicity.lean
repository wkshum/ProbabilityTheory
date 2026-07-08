import ToyApollo.Output.thm_1_1_common_refinement_points

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

namespace Thm11SourceRoute

/-- A partition `R` refines `P` when every node of `P` appears as a node of
`R`. This is the node-level relation needed for Darboux-sum monotonicity. -/
def DarbouxPartitionRefines {a b : ℝ}
    (R P : DarbouxRS.Partition a b) : Prop :=
  ∀ {i : ℕ}, i ≤ P.n → ∃ j, j ≤ R.n ∧ R.pts j = P.pts i

noncomputable def DarbouxPartitionRefines.index {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    (i : ℕ) (hi : i ≤ P.n) : ℕ :=
  Classical.choose (href hi)

noncomputable def DarbouxPartitionRefines.indexD {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    (i : ℕ) : ℕ :=
  if hi : i ≤ P.n then href.index i hi else href.index P.n le_rfl

lemma DarbouxPartitionRefines.index_le {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i : ℕ} (hi : i ≤ P.n) :
    href.index i hi ≤ R.n :=
  (Classical.choose_spec (href hi)).1

lemma DarbouxPartitionRefines.index_pts {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i : ℕ} (hi : i ≤ P.n) :
    R.pts (href.index i hi) = P.pts i :=
  (Classical.choose_spec (href hi)).2

lemma DarbouxPartitionRefines.indexD_eq_index {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i : ℕ} (hi : i ≤ P.n) :
    href.indexD i = href.index i hi := by
  simp [DarbouxPartitionRefines.indexD, hi]

lemma partition_pts_strict_mono_core {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i j : ℕ}
    (hij : i < j) (hj : j ≤ P.n) :
    P.pts i < P.pts j := by
  have hin : i < P.n := lt_of_lt_of_le hij hj
  have hsucc_le : i + 1 ≤ j := Nat.succ_le_of_lt hij
  calc
    P.pts i < P.pts (i + 1) := P.strict_mono i hin
    _ ≤ P.pts j := DarbouxRS.partition_pts_monotone_core P hsucc_le hj

lemma DarbouxPartitionRefines.index_strictMono {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i j : ℕ} (hij : i < j) (hj : j ≤ P.n) :
    href.index i (le_trans (Nat.le_of_lt hij) hj) < href.index j hj := by
  let ri := href.index i (le_trans (Nat.le_of_lt hij) hj)
  let rj := href.index j hj
  have hri_le : ri ≤ R.n :=
    DarbouxPartitionRefines.index_le href (le_trans (Nat.le_of_lt hij) hj)
  have hrj_le : rj ≤ R.n := DarbouxPartitionRefines.index_le href hj
  have hPi_lt_Pj : P.pts i < P.pts j :=
    partition_pts_strict_mono_core P hij hj
  by_contra hnot
  have hrj_le_ri : rj ≤ ri := le_of_not_gt hnot
  rcases lt_or_eq_of_le hrj_le_ri with hrj_lt_ri | hrj_eq_ri
  · have hR_lt : R.pts rj < R.pts ri :=
      partition_pts_strict_mono_core R hrj_lt_ri hri_le
    have hri_pts :
        R.pts ri = P.pts i :=
      DarbouxPartitionRefines.index_pts href (le_trans (Nat.le_of_lt hij) hj)
    have hrj_pts : R.pts rj = P.pts j :=
      DarbouxPartitionRefines.index_pts href hj
    linarith
  · have hri_pts :
        R.pts ri = P.pts i :=
      DarbouxPartitionRefines.index_pts href (le_trans (Nat.le_of_lt hij) hj)
    have hrj_pts : R.pts rj = P.pts j :=
      DarbouxPartitionRefines.index_pts href hj
    rw [hrj_eq_ri] at hrj_pts
    linarith

lemma DarbouxPartitionRefines.index_mono {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) :
    href.index i (le_trans hij hj) ≤ href.index j hj := by
  rcases eq_or_lt_of_le hij with rfl | hij_lt
  · rfl
  · exact le_of_lt (DarbouxPartitionRefines.index_strictMono href hij_lt hj)

lemma partition_node_index_unique {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i j : ℕ}
    (hi : i ≤ P.n) (hj : j ≤ P.n)
    (hpts : P.pts i = P.pts j) :
    i = j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hlt := partition_pts_strict_mono_core P hij hj
    linarith
  · rfl
  · have hlt := partition_pts_strict_mono_core P hji hi
    linarith

lemma DarbouxPartitionRefines.index_zero {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P) :
    href.index 0 (Nat.zero_le P.n) = 0 := by
  apply partition_node_index_unique R
    (DarbouxPartitionRefines.index_le href (Nat.zero_le P.n))
    (Nat.zero_le R.n)
  rw [DarbouxPartitionRefines.index_pts href (Nat.zero_le P.n),
    P.pts_start, R.pts_start]

lemma DarbouxPartitionRefines.index_last {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P) :
    href.index P.n le_rfl = R.n := by
  apply partition_node_index_unique R
    (DarbouxPartitionRefines.index_le href le_rfl)
    le_rfl
  rw [DarbouxPartitionRefines.index_pts href le_rfl, P.pts_end, R.pts_end]

lemma DarbouxPartitionRefines.subinterval_subset_of_index_block {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i k : ℕ} (hi : i < P.n)
    (hk_left : href.index i (Nat.le_of_lt hi) ≤ k)
    (hk_right : k + 1 ≤ href.index (i + 1) (Nat.succ_le_of_lt hi)) :
    DarbouxRS.subinterval R k ⊆ DarbouxRS.subinterval P i := by
  intro x hx
  unfold DarbouxRS.subinterval at hx ⊢
  have hki_le_Rn : k ≤ R.n := by
    have hright_le_Rn :
        href.index (i + 1) (Nat.succ_le_of_lt hi) ≤ R.n :=
      DarbouxPartitionRefines.index_le href (Nat.succ_le_of_lt hi)
    exact le_trans (Nat.le_of_succ_le hk_right) hright_le_Rn
  have hleft_le : P.pts i ≤ R.pts k := by
    calc
      P.pts i = R.pts (href.index i (Nat.le_of_lt hi)) :=
        (DarbouxPartitionRefines.index_pts href (Nat.le_of_lt hi)).symm
      _ ≤ R.pts k := DarbouxRS.partition_pts_monotone_core R hk_left hki_le_Rn
  have hright_le : R.pts (k + 1) ≤ P.pts (i + 1) := by
    calc
      R.pts (k + 1) ≤ R.pts (href.index (i + 1) (Nat.succ_le_of_lt hi)) :=
        DarbouxRS.partition_pts_monotone_core R hk_right
          (DarbouxPartitionRefines.index_le href (Nat.succ_le_of_lt hi))
      _ = P.pts (i + 1) :=
        DarbouxPartitionRefines.index_pts href (Nat.succ_le_of_lt hi)
  exact ⟨le_trans hleft_le hx.1, le_trans hx.2 hright_le⟩

lemma partition_subinterval_image_nonempty {a b : ℝ}
    (P : DarbouxRS.Partition a b) (f : ℝ → ℝ) {i : ℕ}
    (hi : i < P.n) :
    (f '' DarbouxRS.subinterval P i).Nonempty := by
  refine ⟨f (P.pts i), ?_⟩
  refine ⟨P.pts i, ?_, rfl⟩
  unfold DarbouxRS.subinterval
  exact ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩

lemma lowerStep_le_lowerStep_of_subinterval_subset {f : ℝ → ℝ} {a b : ℝ}
    (P R : DarbouxRS.Partition a b) {i k : ℕ}
    (hi : i < P.n) (hk : k < R.n)
    (hBelow : BddBelow (f '' Icc a b))
    (hsub : DarbouxRS.subinterval R k ⊆ DarbouxRS.subinterval P i) :
    DarbouxRS.lowerStep P f i ≤ DarbouxRS.lowerStep R f k := by
  have hPBelow : BddBelow (f '' DarbouxRS.subinterval P i) :=
    BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hBelow
  have hRnonempty : (f '' DarbouxRS.subinterval R k).Nonempty :=
    partition_subinterval_image_nonempty R f hk
  unfold DarbouxRS.lowerStep
  exact csInf_le_csInf hPBelow hRnonempty (Set.image_mono hsub)

lemma upperStep_le_upperStep_of_subinterval_subset {f : ℝ → ℝ} {a b : ℝ}
    (P R : DarbouxRS.Partition a b) {i k : ℕ}
    (hi : i < P.n) (hk : k < R.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hsub : DarbouxRS.subinterval R k ⊆ DarbouxRS.subinterval P i) :
    DarbouxRS.upperStep R f k ≤ DarbouxRS.upperStep P f i := by
  have hPAbove : BddAbove (f '' DarbouxRS.subinterval P i) :=
    BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hAbove
  have hRnonempty : (f '' DarbouxRS.subinterval R k).Nonempty :=
    partition_subinterval_image_nonempty R f hk
  unfold DarbouxRS.upperStep
  exact csSup_le_csSup hPAbove hRnonempty (Set.image_mono hsub)

lemma sum_Ico_refinement_blocks_eq_Ico {β : Type*} [AddCommMonoid β]
    (g : ℕ → β) (idx : ℕ → ℕ) :
    ∀ n : ℕ,
      (∀ i, i < n → idx i ≤ idx (i + 1)) →
        (∑ i ∈ Finset.range n,
            ∑ k ∈ Finset.Ico (idx i) (idx (i + 1)), g k) =
          ∑ k ∈ Finset.Ico (idx 0) (idx n), g k := by
  intro n
  induction n with
  | zero =>
      intro _hmono
      simp
  | succ n ih =>
      intro hmono
      rw [Finset.sum_range_succ]
      have hmono_init : ∀ i, i < n → idx i ≤ idx (i + 1) := by
        intro i hi
        exact hmono i (Nat.lt_trans hi (Nat.lt_succ_self n))
      rw [ih hmono_init]
      have h0n : idx 0 ≤ idx n := by
        have hchain :
            ∀ m : ℕ, (∀ i, i < m → idx i ≤ idx (i + 1)) → idx 0 ≤ idx m := by
          intro m
          induction m with
          | zero =>
              intro _hm
              rfl
          | succ m ihm =>
              intro hm
              have hm_init : ∀ i, i < m → idx i ≤ idx (i + 1) := by
                intro i hi
                exact hm i (Nat.lt_trans hi (Nat.lt_succ_self m))
              exact le_trans (ihm hm_init) (hm m (Nat.lt_succ_self m))
        exact hchain n hmono_init
      have hn : idx n ≤ idx (n + 1) := hmono n (Nat.lt_succ_self n)
      rw [Finset.sum_Ico_consecutive g h0n hn]

lemma sum_Ico_refinement_blocks_eq_range {a b : ℝ}
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range P.n,
        ∑ k ∈ Finset.Ico
          (href.indexD i)
          (href.indexD (i + 1)), g k) =
      ∑ k ∈ Finset.range R.n, g k := by
  let idx : ℕ → ℕ := href.indexD
  have hmono : ∀ i, i < P.n → idx i ≤ idx (i + 1) := by
    intro i hi
    have hi_le : i ≤ P.n := Nat.le_of_lt hi
    have hi1_le : i + 1 ≤ P.n := Nat.succ_le_of_lt hi
    simp [idx, DarbouxPartitionRefines.indexD_eq_index href hi_le,
      DarbouxPartitionRefines.indexD_eq_index href hi1_le]
    exact le_of_lt (DarbouxPartitionRefines.index_strictMono href
      (Nat.lt_succ_self i) hi1_le)
  have hblocks := sum_Ico_refinement_blocks_eq_Ico g idx P.n hmono
  have hidx0 : idx 0 = 0 := by
    have h0 : 0 ≤ P.n := Nat.zero_le P.n
    simp [idx, DarbouxPartitionRefines.indexD_eq_index href h0,
      DarbouxPartitionRefines.index_zero href]
  have hidxn : idx P.n = R.n := by
    simp [idx, DarbouxPartitionRefines.indexD_eq_index href le_rfl,
      DarbouxPartitionRefines.index_last href]
  simpa [idx, hidx0, hidxn] using hblocks

lemma DarbouxPartitionRefines.lower_cell_le_block_sum {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i : ℕ} (hi : i < P.n) :
    DarbouxRS.lowerStep P f i *
        (α (P.pts (i + 1)) - α (P.pts i)) ≤
      ∑ k ∈ Finset.Ico
          (href.index i (Nat.le_of_lt hi))
          (href.index (i + 1) (Nat.succ_le_of_lt hi)),
        DarbouxRS.lowerStep R f k *
          (α (R.pts (k + 1)) - α (R.pts k)) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmonoα⟩
  let j0 := href.index i (Nat.le_of_lt hi)
  let j1 := href.index (i + 1) (Nat.succ_le_of_lt hi)
  have hj0j1 : j0 ≤ j1 := le_of_lt
    (DarbouxPartitionRefines.index_strictMono href (Nat.lt_succ_self i)
      (Nat.succ_le_of_lt hi))
  have htel :
      (∑ k ∈ Finset.Ico j0 j1,
          (α (R.pts (k + 1)) - α (R.pts k))) =
        α (R.pts j1) - α (R.pts j0) := by
    exact Finset.sum_Ico_sub (fun k => α (R.pts k)) hj0j1
  calc
    DarbouxRS.lowerStep P f i *
        (α (P.pts (i + 1)) - α (P.pts i))
        = DarbouxRS.lowerStep P f i *
          (α (R.pts j1) - α (R.pts j0)) := by
            rw [DarbouxPartitionRefines.index_pts href (Nat.succ_le_of_lt hi),
              DarbouxPartitionRefines.index_pts href (Nat.le_of_lt hi)]
    _ = DarbouxRS.lowerStep P f i *
          (∑ k ∈ Finset.Ico j0 j1,
            (α (R.pts (k + 1)) - α (R.pts k))) := by rw [htel]
    _ = ∑ k ∈ Finset.Ico j0 j1,
          DarbouxRS.lowerStep P f i *
            (α (R.pts (k + 1)) - α (R.pts k)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.Ico j0 j1,
          DarbouxRS.lowerStep R f k *
            (α (R.pts (k + 1)) - α (R.pts k)) := by
        refine Finset.sum_le_sum ?_
        intro k hk_mem
        have hkI := Finset.mem_Ico.mp hk_mem
        have hk_lt_j1 : k < j1 := hkI.2
        have hk_left : j0 ≤ k := hkI.1
        have hk_right : k + 1 ≤ j1 := Nat.succ_le_of_lt hk_lt_j1
        have hk_lt_Rn : k < R.n := by
          have hj1_le : j1 ≤ R.n :=
            DarbouxPartitionRefines.index_le href (Nat.succ_le_of_lt hi)
          exact lt_of_lt_of_le hk_lt_j1 hj1_le
        have hsub :
            DarbouxRS.subinterval R k ⊆ DarbouxRS.subinterval P i :=
          DarbouxPartitionRefines.subinterval_subset_of_index_block href hi
            hk_left hk_right
        have hstep :
            DarbouxRS.lowerStep P f i ≤ DarbouxRS.lowerStep R f k :=
          lowerStep_le_lowerStep_of_subinterval_subset P R hi hk_lt_Rn hBelow hsub
        have hinc :
            0 ≤ α (R.pts (k + 1)) - α (R.pts k) :=
          DarbouxRS.partition_increment_nonneg_of_source_core R
            ⟨hab, hAbove, hBelow, hmonoα⟩ hk_lt_Rn
        exact mul_le_mul_of_nonneg_right hstep hinc

lemma DarbouxPartitionRefines.upper_block_sum_le_cell {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    {R P : DarbouxRS.Partition a b} (href : DarbouxPartitionRefines R P)
    {i : ℕ} (hi : i < P.n) :
      (∑ k ∈ Finset.Ico
          (href.index i (Nat.le_of_lt hi))
          (href.index (i + 1) (Nat.succ_le_of_lt hi)),
        DarbouxRS.upperStep R f k *
          (α (R.pts (k + 1)) - α (R.pts k))) ≤
      DarbouxRS.upperStep P f i *
        (α (P.pts (i + 1)) - α (P.pts i)) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmonoα⟩
  let j0 := href.index i (Nat.le_of_lt hi)
  let j1 := href.index (i + 1) (Nat.succ_le_of_lt hi)
  have hj0j1 : j0 ≤ j1 := le_of_lt
    (DarbouxPartitionRefines.index_strictMono href (Nat.lt_succ_self i)
      (Nat.succ_le_of_lt hi))
  have htel :
      (∑ k ∈ Finset.Ico j0 j1,
          (α (R.pts (k + 1)) - α (R.pts k))) =
        α (R.pts j1) - α (R.pts j0) := by
    exact Finset.sum_Ico_sub (fun k => α (R.pts k)) hj0j1
  calc
    (∑ k ∈ Finset.Ico j0 j1,
        DarbouxRS.upperStep R f k *
          (α (R.pts (k + 1)) - α (R.pts k)))
        ≤ ∑ k ∈ Finset.Ico j0 j1,
          DarbouxRS.upperStep P f i *
            (α (R.pts (k + 1)) - α (R.pts k)) := by
          refine Finset.sum_le_sum ?_
          intro k hk_mem
          have hkI := Finset.mem_Ico.mp hk_mem
          have hk_lt_j1 : k < j1 := hkI.2
          have hk_left : j0 ≤ k := hkI.1
          have hk_right : k + 1 ≤ j1 := Nat.succ_le_of_lt hk_lt_j1
          have hk_lt_Rn : k < R.n := by
            have hj1_le : j1 ≤ R.n :=
              DarbouxPartitionRefines.index_le href (Nat.succ_le_of_lt hi)
            exact lt_of_lt_of_le hk_lt_j1 hj1_le
          have hsub :
              DarbouxRS.subinterval R k ⊆ DarbouxRS.subinterval P i :=
            DarbouxPartitionRefines.subinterval_subset_of_index_block href hi
              hk_left hk_right
          have hstep :
              DarbouxRS.upperStep R f k ≤ DarbouxRS.upperStep P f i :=
            upperStep_le_upperStep_of_subinterval_subset P R hi hk_lt_Rn hAbove hsub
          have hinc :
              0 ≤ α (R.pts (k + 1)) - α (R.pts k) :=
            DarbouxRS.partition_increment_nonneg_of_source_core R
              ⟨hab, hAbove, hBelow, hmonoα⟩ hk_lt_Rn
          exact mul_le_mul_of_nonneg_right hstep hinc
    _ = DarbouxRS.upperStep P f i *
          (∑ k ∈ Finset.Ico j0 j1,
            (α (R.pts (k + 1)) - α (R.pts k))) := by
        rw [Finset.mul_sum]
    _ = DarbouxRS.upperStep P f i *
          (α (R.pts j1) - α (R.pts j0)) := by rw [htel]
    _ = DarbouxRS.upperStep P f i *
        (α (P.pts (i + 1)) - α (P.pts i)) := by
          rw [DarbouxPartitionRefines.index_pts href (Nat.succ_le_of_lt hi),
            DarbouxPartitionRefines.index_pts href (Nat.le_of_lt hi)]

lemma DarbouxPartitionRefines_of_partitionOfStrictEndpointList {a b : ℝ}
    (P : DarbouxRS.Partition a b) (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b)
    (hcover : ∀ {i : ℕ}, i ≤ P.n → P.pts i ∈ l) :
    DarbouxPartitionRefines
      (partitionOfStrictEndpointList l hlen hstart hend hstrict) P := by
  intro i hi
  exact partitionOfStrictEndpointList_mem_node l hlen hstart hend hstrict (hcover hi)

lemma concreteCommonRefinementPartition_refines_left {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    DarbouxPartitionRefines (concreteCommonRefinementPartition P Q) P := by
  unfold concreteCommonRefinementPartition
  exact DarbouxPartitionRefines_of_partitionOfStrictEndpointList
    P (commonRefinementPointList P Q)
    (commonRefinementPointList_length_two_le P Q)
    (commonRefinementPointList_getD_zero P Q)
    (commonRefinementPointList_getD_last P Q)
    (fun hi => commonRefinementPointList_adjacent_getD_lt P Q hi)
    (fun hi => commonRefinementPointList_covers_left P Q hi)

lemma concreteCommonRefinementPartition_refines_right {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    DarbouxPartitionRefines (concreteCommonRefinementPartition P Q) Q := by
  unfold concreteCommonRefinementPartition
  exact DarbouxPartitionRefines_of_partitionOfStrictEndpointList
    Q (commonRefinementPointList P Q)
    (commonRefinementPointList_length_two_le P Q)
    (commonRefinementPointList_getD_zero P Q)
    (commonRefinementPointList_getD_last P Q)
    (fun hi => commonRefinementPointList_adjacent_getD_lt P Q hi)
    (fun hi => commonRefinementPointList_covers_right P Q hi)

theorem DarbouxCommonRefinementExists_nodes {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    ∃ R : DarbouxRS.Partition a b,
      DarbouxPartitionRefines R P ∧ DarbouxPartitionRefines R Q := by
  refine ⟨concreteCommonRefinementPartition P Q, ?_, ?_⟩
  · exact concreteCommonRefinementPartition_refines_left P Q
  · exact concreteCommonRefinementPartition_refines_right P Q

lemma concreteCommonRefinementPartition_mesh_lt {a b δ : ℝ}
    (P Q : DarbouxRS.Partition a b)
    (hPmesh : P.mesh < δ) (hQmesh : Q.mesh < δ) :
    (concreteCommonRefinementPartition P Q).mesh < δ := by
  unfold concreteCommonRefinementPartition partitionOfStrictEndpointList
    DarbouxRS.Partition.mesh
  rw [Finset.sup'_lt_iff]
  intro i hi
  exact commonRefinementPointList_adjacent_length_lt_delta
    P Q hPmesh hQmesh (by
      have hi' : i < (commonRefinementPointList P Q).length - 1 :=
        Finset.mem_range.mp hi
      omega)

/-- The common-refinement construction target separated from the upper/lower
sum estimates. The mesh bound is included here so the later sandwich proof
does not need to inspect how the refinement partition was built. -/
def DarbouxCommonRefinementExists (a b : ℝ) : Prop :=
  ∀ δ > 0, ∀ P Q : DarbouxRS.Partition a b,
    P.mesh < δ →
    Q.mesh < δ →
      ∃ R : DarbouxRS.Partition a b,
        R.mesh < δ ∧
        DarbouxPartitionRefines R P ∧
        DarbouxPartitionRefines R Q

theorem DarbouxCommonRefinementExists_concrete {a b : ℝ} :
    DarbouxCommonRefinementExists a b := by
  intro δ _hδ P Q hPmesh hQmesh
  refine ⟨concreteCommonRefinementPartition P Q, ?_, ?_, ?_⟩
  · exact concreteCommonRefinementPartition_mesh_lt P Q hPmesh hQmesh
  · exact concreteCommonRefinementPartition_refines_left P Q
  · exact concreteCommonRefinementPartition_refines_right P Q

/-- The Darboux monotonicity target for a single refinement: lower sums
increase and upper sums decrease when the partition is refined. -/
def DarbouxRefinementSumMonotone
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  DarbouxRS.SourceHypotheses a b f α →
    ∀ P R : DarbouxRS.Partition a b,
      DarbouxPartitionRefines R P →
        DarbouxRS.lowerSum P f α ≤ DarbouxRS.lowerSum R f α ∧
        DarbouxRS.upperSum R f α ≤ DarbouxRS.upperSum P f α

theorem DarbouxRefinementSumMonotone_proof
    {f α : ℝ → ℝ} {a b : ℝ} :
    DarbouxRefinementSumMonotone a b f α := by
  intro hs P R href
  constructor
  · unfold DarbouxRS.lowerSum
    let g : ℕ → ℝ := fun k =>
      DarbouxRS.lowerStep R f k *
        (α (R.pts (k + 1)) - α (R.pts k))
    calc
      (∑ i ∈ Finset.range P.n,
          DarbouxRS.lowerStep P f i *
            (α (P.pts (i + 1)) - α (P.pts i)))
          ≤ ∑ i ∈ Finset.range P.n,
              ∑ k ∈ Finset.Ico (href.indexD i) (href.indexD (i + 1)), g k := by
            refine Finset.sum_le_sum ?_
            intro i hi_mem
            have hi : i < P.n := Finset.mem_range.mp hi_mem
            have hi_le : i ≤ P.n := Nat.le_of_lt hi
            have hi1_le : i + 1 ≤ P.n := Nat.succ_le_of_lt hi
            simpa [g, DarbouxPartitionRefines.indexD_eq_index href hi_le,
              DarbouxPartitionRefines.indexD_eq_index href hi1_le]
              using DarbouxPartitionRefines.lower_cell_le_block_sum hs href hi
      _ = ∑ k ∈ Finset.range R.n, g k := by
            exact sum_Ico_refinement_blocks_eq_range href g
  · unfold DarbouxRS.upperSum
    let g : ℕ → ℝ := fun k =>
      DarbouxRS.upperStep R f k *
        (α (R.pts (k + 1)) - α (R.pts k))
    calc
      (∑ k ∈ Finset.range R.n,
          DarbouxRS.upperStep R f k *
            (α (R.pts (k + 1)) - α (R.pts k)))
          = ∑ i ∈ Finset.range P.n,
              ∑ k ∈ Finset.Ico (href.indexD i) (href.indexD (i + 1)), g k := by
            exact (sum_Ico_refinement_blocks_eq_range href g).symm
      _ ≤ ∑ i ∈ Finset.range P.n,
              DarbouxRS.upperStep P f i *
                (α (P.pts (i + 1)) - α (P.pts i)) := by
            refine Finset.sum_le_sum ?_
            intro i hi_mem
            have hi : i < P.n := Finset.mem_range.mp hi_mem
            have hi_le : i ≤ P.n := Nat.le_of_lt hi
            have hi1_le : i + 1 ≤ P.n := Nat.succ_le_of_lt hi
            simpa [g, DarbouxPartitionRefines.indexD_eq_index href hi_le,
              DarbouxPartitionRefines.indexD_eq_index href hi1_le]
              using DarbouxPartitionRefines.upper_block_sum_le_cell hs href hi

/-- Once the concrete common-refinement partition exists and Darboux sums are
monotone under refinement, the four-sided sandwich interface follows
formally. -/
theorem DarbouxCommonRefinementSandwich_of_exists_and_sumMonotone
    {f α : ℝ → ℝ} {a b : ℝ}
    (hexists : DarbouxCommonRefinementExists a b)
    (hmono : DarbouxRefinementSumMonotone a b f α)
    (hs : DarbouxRS.SourceHypotheses a b f α) :
    DarbouxCommonRefinementSandwich a b f α := by
  intro δ hδ P Q hPmesh hQmesh
  rcases hexists δ hδ P Q hPmesh hQmesh with
    ⟨R, hRmesh, hRP, hRQ⟩
  rcases hmono hs P R hRP with ⟨hLP_R, hUR_P⟩
  rcases hmono hs Q R hRQ with ⟨hLQ_R, hUR_Q⟩
  exact ⟨R, hRmesh, hLP_R, hLQ_R, hUR_P, hUR_Q⟩

theorem DarbouxCommonRefinementSandwich_of_sumMonotone
    {f α : ℝ → ℝ} {a b : ℝ}
    (hmono : DarbouxRefinementSumMonotone a b f α)
    (hs : DarbouxRS.SourceHypotheses a b f α) :
    DarbouxCommonRefinementSandwich a b f α :=
  DarbouxCommonRefinementSandwich_of_exists_and_sumMonotone
    DarbouxCommonRefinementExists_concrete hmono hs

theorem DarbouxCommonRefinementSandwich_proof
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α) :
    DarbouxCommonRefinementSandwich a b f α :=
  DarbouxCommonRefinementSandwich_of_sumMonotone
    DarbouxRefinementSumMonotone_proof hs

/-- Once common-refinement monotonicity is available, same-partition gap
smallness upgrades to the cross-partition fine-Cauchy comparison needed by the
real-completeness extraction. This lemma is generic Darboux infrastructure:
the finite-discontinuity estimate is not used here. -/
theorem closedIntervalDarbouxFineCauchy_of_commonRefinementSandwich
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    (hgap : ClosedIntervalDarbouxGapSmall a b f α)
    (hrefine : DarbouxCommonRefinementSandwich a b f α) :
    ClosedIntervalDarbouxFineCauchy a b f α := by
  intro eps heps
  have hhalf : 0 < eps / 2 := by linarith
  rcases hgap (eps / 2) hhalf with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P Q hPmesh hQmesh
  rcases hrefine δ hδ P Q hPmesh hQmesh with
    ⟨R, hRmesh, hLP_R, hLQ_R, hUR_P, hUR_Q⟩
  have hgapP : DarbouxRS.upperSum P f α - DarbouxRS.lowerSum P f α < eps / 2 :=
    Hδ P hPmesh
  have hgapQ : DarbouxRS.upperSum Q f α - DarbouxRS.lowerSum Q f α < eps / 2 :=
    Hδ Q hQmesh
  have hLR_UR : DarbouxRS.lowerSum R f α ≤ DarbouxRS.upperSum R f α :=
    DarbouxRS.lowerSum_le_upperSum_core R hs
  have hLR_UP : DarbouxRS.lowerSum R f α ≤ DarbouxRS.upperSum P f α :=
    le_trans hLR_UR hUR_P
  have hLR_UQ : DarbouxRS.lowerSum R f α ≤ DarbouxRS.upperSum Q f α :=
    le_trans hLR_UR hUR_Q
  have hLQ_UP : DarbouxRS.lowerSum Q f α ≤ DarbouxRS.upperSum P f α :=
    le_trans hLQ_R hLR_UP
  have hLP_UQ : DarbouxRS.lowerSum P f α ≤ DarbouxRS.upperSum Q f α :=
    le_trans hLP_R hLR_UQ
  have hUP_UQ : DarbouxRS.upperSum P f α - DarbouxRS.upperSum Q f α < eps / 2 := by
    have hle₁ :
        DarbouxRS.upperSum P f α - DarbouxRS.upperSum Q f α ≤
          DarbouxRS.upperSum P f α - DarbouxRS.lowerSum R f α := by
      linarith
    have hle₂ :
        DarbouxRS.upperSum P f α - DarbouxRS.lowerSum R f α ≤
          DarbouxRS.upperSum P f α - DarbouxRS.lowerSum P f α := by
      linarith
    exact lt_of_le_of_lt (le_trans hle₁ hle₂) hgapP
  have hUQ_UP : DarbouxRS.upperSum Q f α - DarbouxRS.upperSum P f α < eps / 2 := by
    have hle₁ :
        DarbouxRS.upperSum Q f α - DarbouxRS.upperSum P f α ≤
          DarbouxRS.upperSum Q f α - DarbouxRS.lowerSum R f α := by
      linarith
    have hle₂ :
        DarbouxRS.upperSum Q f α - DarbouxRS.lowerSum R f α ≤
          DarbouxRS.upperSum Q f α - DarbouxRS.lowerSum Q f α := by
      linarith
    exact lt_of_le_of_lt (le_trans hle₁ hle₂) hgapQ
  have hLP_LQ : DarbouxRS.lowerSum P f α - DarbouxRS.lowerSum Q f α < eps / 2 := by
    have hLP_UQ' : DarbouxRS.lowerSum P f α ≤ DarbouxRS.upperSum Q f α := hLP_UQ
    linarith
  have hLQ_LP : DarbouxRS.lowerSum Q f α - DarbouxRS.lowerSum P f α < eps / 2 := by
    have hLQ_UP' : DarbouxRS.lowerSum Q f α ≤ DarbouxRS.upperSum P f α := hLQ_UP
    linarith
  have hUP_LQ : DarbouxRS.upperSum P f α - DarbouxRS.lowerSum Q f α < eps := by
    linarith
  have hUQ_LP : DarbouxRS.upperSum Q f α - DarbouxRS.lowerSum P f α < eps := by
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · exact abs_lt.mpr ⟨by linarith, by linarith⟩

end Thm11SourceRoute
