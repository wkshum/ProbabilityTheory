import ToyApollo.Output.thm_1_1_darboux_gap

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

namespace Thm11SourceRoute

/-- A reusable common-refinement monotonicity target for Darboux sums. It says
that two fine partitions have a common fine partition whose lower sum dominates
both lower sums and whose upper sum is dominated by both upper sums. Proving
this from an explicit point-set refinement construction is the remaining
partition-combinatorial step. -/
def DarbouxCommonRefinementSandwich
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ δ > 0, ∀ P Q : DarbouxRS.Partition a b,
    P.mesh < δ →
    Q.mesh < δ →
      ∃ R : DarbouxRS.Partition a b,
        R.mesh < δ ∧
        DarbouxRS.lowerSum P f α ≤ DarbouxRS.lowerSum R f α ∧
        DarbouxRS.lowerSum Q f α ≤ DarbouxRS.lowerSum R f α ∧
        DarbouxRS.upperSum R f α ≤ DarbouxRS.upperSum P f α ∧
        DarbouxRS.upperSum R f α ≤ DarbouxRS.upperSum Q f α

/-- The finite set of nodes belonging to a partition. It includes both
endpoints because the range is `0, ..., P.n`. -/
noncomputable def partitionPointSet {a b : ℝ}
    (P : DarbouxRS.Partition a b) : Finset ℝ :=
  (Finset.range (P.n + 1)).image P.pts

lemma mem_partitionPointSet_iff {a b x : ℝ}
    (P : DarbouxRS.Partition a b) :
    x ∈ partitionPointSet P ↔ ∃ i, i ≤ P.n ∧ P.pts i = x := by
  simp [partitionPointSet, eq_comm]

lemma partitionPointSet_left_mem {a b : ℝ}
    (P : DarbouxRS.Partition a b) :
    a ∈ partitionPointSet P := by
  rw [mem_partitionPointSet_iff]
  exact ⟨0, Nat.zero_le P.n, P.pts_start⟩

lemma partitionPointSet_right_mem {a b : ℝ}
    (P : DarbouxRS.Partition a b) :
    b ∈ partitionPointSet P := by
  rw [mem_partitionPointSet_iff]
  exact ⟨P.n, le_rfl, P.pts_end⟩

lemma partitionPointSet_subset_Icc {a b x : ℝ}
    (P : DarbouxRS.Partition a b)
    (hx : x ∈ partitionPointSet P) :
    x ∈ Icc a b := by
  rcases (mem_partitionPointSet_iff P).1 hx with ⟨i, hi, rfl⟩
  exact DarbouxRS.partition_pts_mem_Icc_core P hi

/-- The concrete finite set underlying the common refinement of two
partitions: the union of both node sets. -/
noncomputable def commonRefinementPointSet {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) : Finset ℝ :=
  partitionPointSet P ∪ partitionPointSet Q

/-- The concrete sorted node list for the common refinement. The later
partition-construction step turns this list into a `DarbouxRS.Partition`. -/
noncomputable def commonRefinementPointList {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) : List ℝ :=
  (commonRefinementPointSet P Q).sort (fun x y : ℝ => x ≤ y)

lemma mem_commonRefinementPointList_iff {a b x : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    x ∈ commonRefinementPointList P Q ↔
      x ∈ partitionPointSet P ∨ x ∈ partitionPointSet Q := by
  unfold commonRefinementPointList commonRefinementPointSet
  rw [Finset.mem_sort, Finset.mem_union]

lemma commonRefinementPointList_sorted {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    (commonRefinementPointList P Q).Pairwise (fun x y : ℝ => x ≤ y) := by
  unfold commonRefinementPointList
  exact Finset.pairwise_sort (commonRefinementPointSet P Q) (fun x y : ℝ => x ≤ y)

lemma commonRefinementPointList_nodup {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    (commonRefinementPointList P Q).Nodup := by
  unfold commonRefinementPointList
  exact Finset.sort_nodup (commonRefinementPointSet P Q) (fun x y : ℝ => x ≤ y)

lemma commonRefinementPointList_left_mem {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    a ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inl (partitionPointSet_left_mem P)

lemma commonRefinementPointList_right_mem {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    b ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inl (partitionPointSet_right_mem P)

lemma commonRefinementPointList_covers_left {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) {i : ℕ}
    (hi : i ≤ P.n) :
    P.pts i ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inl ((mem_partitionPointSet_iff P).2 ⟨i, hi, rfl⟩)

lemma commonRefinementPointList_covers_right {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) {i : ℕ}
    (hi : i ≤ Q.n) :
    Q.pts i ∈ commonRefinementPointList P Q := by
  rw [mem_commonRefinementPointList_iff]
  exact Or.inr ((mem_partitionPointSet_iff Q).2 ⟨i, hi, rfl⟩)

lemma commonRefinementPointList_subset_Icc {a b x : ℝ}
    (P Q : DarbouxRS.Partition a b)
    (hx : x ∈ commonRefinementPointList P Q) :
    x ∈ Icc a b := by
  rcases (mem_commonRefinementPointList_iff P Q).1 hx with hxP | hxQ
  · exact partitionPointSet_subset_Icc P hxP
  · exact partitionPointSet_subset_Icc Q hxQ

lemma sorted_nodup_adjacent_lt {l : List ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (hnodup : l.Nodup) {i : ℕ}
    (hi : i + 1 < l.length) :
    l[i] < l[i + 1] := by
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hle : l[i] ≤ l[i + 1] :=
    (List.pairwise_iff_getElem.mp hsorted) i (i + 1) hi0 hi (Nat.lt_succ_self i)
  have hne : l[i] ≠ l[i + 1] := by
    intro hEq
    have hidx : i = i + 1 := by
      exact (List.Nodup.getElem_inj_iff (l := l) hnodup (i := i) (hi := hi0)
        (j := i + 1) (hj := hi)).1 hEq
    omega
  exact lt_of_le_of_ne hle hne

lemma commonRefinementPointList_adjacent_lt {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q)[i] <
      (commonRefinementPointList P Q)[i + 1] :=
  sorted_nodup_adjacent_lt
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_nodup P Q) hi

lemma sorted_nodup_adjacent_getD_lt {l : List ℝ} {fallback : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (hnodup : l.Nodup) {i : ℕ}
    (hi : i + 1 < l.length) :
    l.getD i fallback < l.getD (i + 1) fallback := by
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  rw [List.getD_eq_getElem l fallback hi0]
  rw [List.getD_eq_getElem l fallback hi]
  exact sorted_nodup_adjacent_lt hsorted hnodup hi

lemma commonRefinementPointList_adjacent_getD_lt {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q).getD i b <
      (commonRefinementPointList P Q).getD (i + 1) b :=
  sorted_nodup_adjacent_getD_lt
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_nodup P Q) hi

lemma partition_endpoints_lt {a b : ℝ} (P : DarbouxRS.Partition a b) :
    a < b := by
  have h01 : P.pts 0 < P.pts (0 + 1) := P.strict_mono 0 P.hn
  have h1n : P.pts 1 ≤ P.pts P.n :=
    DarbouxRS.partition_pts_monotone_core P (Nat.succ_le_of_lt P.hn) le_rfl
  calc
    a = P.pts 0 := P.pts_start.symm
    _ < P.pts 1 := by simpa using h01
    _ ≤ P.pts P.n := h1n
    _ = b := P.pts_end

lemma list_length_two_le_of_nodup_mem_ne {l : List ℝ} {a b : ℝ}
    (_hnodup : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    2 ≤ l.length := by
  rcases List.mem_iff_getElem.1 ha with ⟨i, hi, hia⟩
  rcases List.mem_iff_getElem.1 hb with ⟨j, hj, hjb⟩
  have hij : i ≠ j := by
    intro h
    subst j
    apply hne
    exact hia.symm.trans hjb
  omega

lemma sorted_list_getD_zero_eq_left {l : List ℝ} {a b : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (ha : a ∈ l)
    (hsub : ∀ {x : ℝ}, x ∈ l → x ∈ Icc a b) :
    l.getD 0 b = a := by
  have hlen : 0 < l.length := by
    rcases List.mem_iff_getElem.1 ha with ⟨i, hi, _⟩
    omega
  have hhead_mem : l[0] ∈ l := by
    exact List.getElem_mem (l := l) (n := 0) hlen
  have hge : a ≤ l[0] := (hsub hhead_mem).1
  have hle : l[0] ≤ a := by
    rcases List.mem_iff_getElem.1 ha with ⟨j, hj, hjv⟩
    by_cases hj0 : j = 0
    · subst j
      exact le_of_eq hjv
    · have h0j : 0 < j := Nat.pos_of_ne_zero hj0
      have hle0j :=
        (List.pairwise_iff_getElem.mp hsorted) 0 j hlen hj h0j
      simpa [hjv] using hle0j
  have hEq : l[0] = a := le_antisymm hle hge
  rw [List.getD_eq_getElem l b hlen]
  exact hEq

lemma sorted_list_getD_last_eq_right {l : List ℝ} {a b : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (hb : b ∈ l)
    (hsub : ∀ {x : ℝ}, x ∈ l → x ∈ Icc a b) :
    l.getD (l.length - 1) a = b := by
  have hlen : 0 < l.length := by
    rcases List.mem_iff_getElem.1 hb with ⟨i, hi, _⟩
    omega
  have hlast : l.length - 1 < l.length := by omega
  have hlast_mem : l[l.length - 1] ∈ l := by
    exact List.getElem_mem (l := l) (n := l.length - 1) hlast
  have hle : l[l.length - 1] ≤ b := (hsub hlast_mem).2
  have hge : b ≤ l[l.length - 1] := by
    rcases List.mem_iff_getElem.1 hb with ⟨j, hj, hjv⟩
    by_cases hjlast : j = l.length - 1
    · subst j
      exact le_of_eq hjv.symm
    · have hj_lt_last : j < l.length - 1 := by omega
      have hle_last :=
        (List.pairwise_iff_getElem.mp hsorted) j (l.length - 1) hj hlast hj_lt_last
      simpa [hjv] using hle_last
  have hEq : l[l.length - 1] = b := le_antisymm hle hge
  rw [List.getD_eq_getElem l a hlast]
  exact hEq

lemma commonRefinementPointList_length_two_le {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    2 ≤ (commonRefinementPointList P Q).length := by
  refine list_length_two_le_of_nodup_mem_ne
    (commonRefinementPointList_nodup P Q)
    (commonRefinementPointList_left_mem P Q)
    (commonRefinementPointList_right_mem P Q) ?_
  exact ne_of_lt (partition_endpoints_lt P)

lemma commonRefinementPointList_getD_zero {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    (commonRefinementPointList P Q).getD 0 b = a := by
  exact sorted_list_getD_zero_eq_left
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_left_mem P Q)
    (fun hx => commonRefinementPointList_subset_Icc P Q hx)

lemma commonRefinementPointList_getD_last {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    (commonRefinementPointList P Q).getD
      ((commonRefinementPointList P Q).length - 1) a = b := by
  exact sorted_list_getD_last_eq_right
    (commonRefinementPointList_sorted P Q)
    (commonRefinementPointList_right_mem P Q)
    (fun hx => commonRefinementPointList_subset_Icc P Q hx)

lemma partition_length_le_mesh_core {a b : ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n) :
    P.pts (i + 1) - P.pts i ≤ P.mesh := by
  unfold DarbouxRS.Partition.mesh
  exact Finset.le_sup'
    (fun j => P.pts (j + 1) - P.pts j)
    (Finset.mem_range.mpr hi)

lemma sorted_nodup_adjacent_no_mem_between {l : List ℝ} {fallback z : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    {i : ℕ}
    (hi : i + 1 < l.length)
    (hz : z ∈ l) :
    ¬ (l.getD i fallback < z ∧ z < l.getD (i + 1) fallback) := by
  intro hbetween
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  rw [List.getD_eq_getElem l fallback hi0] at hbetween
  rw [List.getD_eq_getElem l fallback hi] at hbetween
  rcases hbetween with ⟨hleft, hright⟩
  rcases List.mem_iff_getElem.1 hz with ⟨k, hk, hkz⟩
  by_cases hki : k ≤ i
  · have hle_left : z ≤ l[i] := by
      by_cases hki_eq : k = i
      · subst k
        exact le_of_eq hkz.symm
      · have hk_lt_i : k < i := lt_of_le_of_ne hki hki_eq
        have hleki :=
          (List.pairwise_iff_getElem.mp hsorted) k i hk hi0 hk_lt_i
        simpa [hkz] using hleki
    linarith
  · have hik : i + 1 ≤ k := by omega
    have hle_right : l[i + 1] ≤ z := by
      by_cases hk_eq : k = i + 1
      · subst k
        exact le_of_eq hkz
      · have hlt : i + 1 < k := lt_of_le_of_ne hik (Ne.symm hk_eq)
        have hleik :=
          (List.pairwise_iff_getElem.mp hsorted) (i + 1) k hi hk hlt
        simpa [hkz] using hleik
    linarith

lemma list_getD_mem_of_lt {l : List ℝ} {fallback : ℝ} {i : ℕ}
    (hi : i < l.length) :
    l.getD i fallback ∈ l := by
  rw [List.getD_eq_getElem l fallback hi]
  exact List.getElem_mem (l := l) (n := i) hi

lemma commonRefinementPointList_adjacent_right_le_next_of_left_partition
    {a b : ℝ} (P Q : DarbouxRS.Partition a b) {i k : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hk : k ≤ P.n)
    (hleft : (commonRefinementPointList P Q).getD i b = P.pts k) :
    (commonRefinementPointList P Q).getD (i + 1) b ≤ P.pts (k + 1) := by
  let l := commonRefinementPointList P Q
  have hsorted : l.Pairwise (fun x y : ℝ => x ≤ y) :=
    commonRefinementPointList_sorted P Q
  have hnodup : l.Nodup := commonRefinementPointList_nodup P Q
  have hgap : l.getD i b < l.getD (i + 1) b :=
    commonRefinementPointList_adjacent_getD_lt P Q hi
  have hright_mem : l.getD (i + 1) b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi
  have hright_le_b : l.getD (i + 1) b ≤ b :=
    (commonRefinementPointList_subset_Icc P Q hright_mem).2
  have hklt : k < P.n := by
    by_contra hnot
    have hk_eq : k = P.n := le_antisymm hk (le_of_not_gt hnot)
    have hleft_b : l.getD i b = b := by
      rw [hleft, hk_eq, P.pts_end]
    linarith
  by_contra hnot
  have hnext_lt_right : P.pts (k + 1) < l.getD (i + 1) b :=
    lt_of_not_ge hnot
  have hleft_lt_next : l.getD i b < P.pts (k + 1) := by
    rw [hleft]
    exact P.strict_mono k hklt
  have hnext_mem : P.pts (k + 1) ∈ l :=
    commonRefinementPointList_covers_left P Q (Nat.succ_le_of_lt hklt)
  exact (sorted_nodup_adjacent_no_mem_between hsorted hi hnext_mem)
    ⟨hleft_lt_next, hnext_lt_right⟩

lemma commonRefinementPointList_adjacent_right_le_next_of_right_partition
    {a b : ℝ} (P Q : DarbouxRS.Partition a b) {i k : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hk : k ≤ Q.n)
    (hleft : (commonRefinementPointList P Q).getD i b = Q.pts k) :
    (commonRefinementPointList P Q).getD (i + 1) b ≤ Q.pts (k + 1) := by
  let l := commonRefinementPointList P Q
  have hsorted : l.Pairwise (fun x y : ℝ => x ≤ y) :=
    commonRefinementPointList_sorted P Q
  have hgap : l.getD i b < l.getD (i + 1) b :=
    commonRefinementPointList_adjacent_getD_lt P Q hi
  have hright_mem : l.getD (i + 1) b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi
  have hright_le_b : l.getD (i + 1) b ≤ b :=
    (commonRefinementPointList_subset_Icc P Q hright_mem).2
  have hklt : k < Q.n := by
    by_contra hnot
    have hk_eq : k = Q.n := le_antisymm hk (le_of_not_gt hnot)
    have hleft_b : l.getD i b = b := by
      rw [hleft, hk_eq, Q.pts_end]
    linarith
  by_contra hnot
  have hnext_lt_right : Q.pts (k + 1) < l.getD (i + 1) b :=
    lt_of_not_ge hnot
  have hleft_lt_next : l.getD i b < Q.pts (k + 1) := by
    rw [hleft]
    exact Q.strict_mono k hklt
  have hnext_mem : Q.pts (k + 1) ∈ l :=
    commonRefinementPointList_covers_right P Q (Nat.succ_le_of_lt hklt)
  exact (sorted_nodup_adjacent_no_mem_between hsorted hi hnext_mem)
    ⟨hleft_lt_next, hnext_lt_right⟩

lemma commonRefinementPointList_adjacent_length_le_mesh_of_left_partition
    {a b : ℝ} (P Q : DarbouxRS.Partition a b) {i k : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hk : k ≤ P.n)
    (hleft : (commonRefinementPointList P Q).getD i b = P.pts k) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b ≤ P.mesh := by
  let l := commonRefinementPointList P Q
  have hright_le_next :
      l.getD (i + 1) b ≤ P.pts (k + 1) :=
    commonRefinementPointList_adjacent_right_le_next_of_left_partition
      P Q hi hk hleft
  have hgap : l.getD i b < l.getD (i + 1) b :=
    commonRefinementPointList_adjacent_getD_lt P Q hi
  have hright_mem : l.getD (i + 1) b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi
  have hright_le_b : l.getD (i + 1) b ≤ b :=
    (commonRefinementPointList_subset_Icc P Q hright_mem).2
  have hklt : k < P.n := by
    by_contra hnot
    have hk_eq : k = P.n := le_antisymm hk (le_of_not_gt hnot)
    have hleft_b : l.getD i b = b := by
      rw [hleft, hk_eq, P.pts_end]
    linarith
  have hlen_le :
      l.getD (i + 1) b - l.getD i b ≤ P.pts (k + 1) - P.pts k := by
    rw [hleft]
    linarith
  exact le_trans hlen_le (partition_length_le_mesh_core P hklt)

lemma commonRefinementPointList_adjacent_length_le_mesh_of_right_partition
    {a b : ℝ} (P Q : DarbouxRS.Partition a b) {i k : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length)
    (hk : k ≤ Q.n)
    (hleft : (commonRefinementPointList P Q).getD i b = Q.pts k) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b ≤ Q.mesh := by
  let l := commonRefinementPointList P Q
  have hright_le_next :
      l.getD (i + 1) b ≤ Q.pts (k + 1) :=
    commonRefinementPointList_adjacent_right_le_next_of_right_partition
      P Q hi hk hleft
  have hgap : l.getD i b < l.getD (i + 1) b :=
    commonRefinementPointList_adjacent_getD_lt P Q hi
  have hright_mem : l.getD (i + 1) b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi
  have hright_le_b : l.getD (i + 1) b ≤ b :=
    (commonRefinementPointList_subset_Icc P Q hright_mem).2
  have hklt : k < Q.n := by
    by_contra hnot
    have hk_eq : k = Q.n := le_antisymm hk (le_of_not_gt hnot)
    have hleft_b : l.getD i b = b := by
      rw [hleft, hk_eq, Q.pts_end]
    linarith
  have hlen_le :
      l.getD (i + 1) b - l.getD i b ≤ Q.pts (k + 1) - Q.pts k := by
    rw [hleft]
    linarith
  exact le_trans hlen_le (partition_length_le_mesh_core Q hklt)

lemma commonRefinementPointList_adjacent_length_lt_delta {a b δ : ℝ}
    (P Q : DarbouxRS.Partition a b)
    (hPmesh : P.mesh < δ) (hQmesh : Q.mesh < δ)
    {i : ℕ}
    (hi : i + 1 < (commonRefinementPointList P Q).length) :
    (commonRefinementPointList P Q).getD (i + 1) b -
        (commonRefinementPointList P Q).getD i b < δ := by
  let l := commonRefinementPointList P Q
  have hi0 : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi
  have hleft_mem : l.getD i b ∈ l :=
    list_getD_mem_of_lt (l := l) (fallback := b) hi0
  rcases (mem_commonRefinementPointList_iff P Q).1 hleft_mem with hP | hQ
  · rcases (mem_partitionPointSet_iff P).1 hP with ⟨k, hk, hkleft⟩
    have hle :=
      commonRefinementPointList_adjacent_length_le_mesh_of_left_partition
        P Q hi hk hkleft.symm
    exact lt_of_le_of_lt hle hPmesh
  · rcases (mem_partitionPointSet_iff Q).1 hQ with ⟨k, hk, hkleft⟩
    have hle :=
      commonRefinementPointList_adjacent_length_le_mesh_of_right_partition
        P Q hi hk hkleft.symm
    exact lt_of_le_of_lt hle hQmesh

/-- Build a textbook partition from an endpoint list whose consecutive entries
are strictly increasing. This is the list-to-partition constructor needed after
the sorted union-of-nodes list is shown to start at `a` and end at `b`. -/
noncomputable def partitionOfStrictEndpointList {a b : ℝ} (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b) :
    DarbouxRS.Partition a b where
  n := l.length - 1
  hn := by omega
  pts := fun i => l.getD i b
  pts_start := by
    exact hstart
  pts_end := by
    have hlast : l.length - 1 < l.length := by omega
    rw [List.getD_eq_getElem l b hlast]
    rw [List.getD_eq_getElem l a hlast] at hend
    exact hend
  strict_mono := by
    intro i hi
    have hi_succ : i + 1 < l.length := by omega
    exact hstrict hi_succ

lemma partitionOfStrictEndpointList_mem_node {a b : ℝ} (l : List ℝ)
    (hlen : 2 ≤ l.length)
    (hstart : l.getD 0 b = a)
    (hend : l.getD (l.length - 1) a = b)
    (hstrict : ∀ {i : ℕ}, i + 1 < l.length → l.getD i b < l.getD (i + 1) b)
    {x : ℝ} (hx : x ∈ l) :
    ∃ j, j ≤ (partitionOfStrictEndpointList l hlen hstart hend hstrict).n ∧
      (partitionOfStrictEndpointList l hlen hstart hend hstrict).pts j = x := by
  rcases List.mem_iff_getElem.1 hx with ⟨j, hj, hjx⟩
  refine ⟨j, ?_, ?_⟩
  · simp [partitionOfStrictEndpointList]
    omega
  · change l.getD j b = x
    rw [List.getD_eq_getElem l b hj]
    exact hjx

/-- Data already obtained from the concrete union-of-nodes construction. This
is the point-list form of a common refinement; converting this sorted list into
a `DarbouxRS.Partition` is the next combinatorial layer. -/
structure DarbouxCommonRefinementPointList {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) where
  points : List ℝ
  sorted : points.Pairwise (fun x y : ℝ => x ≤ y)
  nodup : points.Nodup
  left_mem : a ∈ points
  right_mem : b ∈ points
  covers_left : ∀ {i : ℕ}, i ≤ P.n → P.pts i ∈ points
  covers_right : ∀ {i : ℕ}, i ≤ Q.n → Q.pts i ∈ points
  subset_Icc : ∀ {x : ℝ}, x ∈ points → x ∈ Icc a b

/-- Concrete common-refinement node list obtained by sorting the union of the
two finite partition-node sets. -/
noncomputable def concreteCommonRefinementPointList {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    DarbouxCommonRefinementPointList P Q where
  points := commonRefinementPointList P Q
  sorted := commonRefinementPointList_sorted P Q
  nodup := commonRefinementPointList_nodup P Q
  left_mem := commonRefinementPointList_left_mem P Q
  right_mem := commonRefinementPointList_right_mem P Q
  covers_left := by
    intro i hi
    exact commonRefinementPointList_covers_left P Q hi
  covers_right := by
    intro i hi
    exact commonRefinementPointList_covers_right P Q hi
  subset_Icc := by
    intro x hx
    exact commonRefinementPointList_subset_Icc P Q hx

/-- The concrete common-refinement partition built from the sorted union of
the two node sets. Its endpoints and strictness are discharged by the sorted
nodup endpoint-list helpers above. -/
noncomputable def concreteCommonRefinementPartition {a b : ℝ}
    (P Q : DarbouxRS.Partition a b) :
    DarbouxRS.Partition a b :=
  partitionOfStrictEndpointList
    (commonRefinementPointList P Q)
    (commonRefinementPointList_length_two_le P Q)
    (commonRefinementPointList_getD_zero P Q)
    (commonRefinementPointList_getD_last P Q)
    (fun hi => commonRefinementPointList_adjacent_getD_lt P Q hi)


end Thm11SourceRoute
