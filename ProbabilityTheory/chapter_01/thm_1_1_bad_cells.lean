import ProbabilityTheory.chapter_01.thm_1_1_oscillation_basic

open Finset BigOperators
open MeasureTheory
open Set Topology

noncomputable section

namespace Thm11SourceRoute

/-- The good remainder after removing open bad-point neighborhoods from the
closed interval. Points in this set stay at least `rho c` away from every
bad point `c ∈ S`. -/
def goodRemainder (a b : ℝ) (S : Finset ℝ) (rho : ℝ → ℝ) : Set ℝ :=
  Icc a b ∩ ⋂ c ∈ S, {x : ℝ | rho c ≤ |x - c|}

lemma mem_goodRemainder_iff {a b x : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    x ∈ goodRemainder a b S rho ↔
      x ∈ Icc a b ∧ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
  simp [goodRemainder]

/-- The good remainder is compact: it is the closed interval intersected with
finitely many closed distance constraints. -/
lemma isCompact_goodRemainder {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ} :
    IsCompact (goodRemainder a b S rho) := by
  have hclosed_constraints :
      IsClosed (⋂ c ∈ S, {x : ℝ | rho c ≤ |x - c|}) := by
    refine isClosed_iInter ?_
    intro c
    refine isClosed_iInter ?_
    intro _hc
    have hcont : Continuous (fun x : ℝ => |x - c|) :=
      (continuous_id.sub continuous_const).abs
    exact isClosed_Ici.preimage hcont
  exact isCompact_Icc.inter_right hclosed_constraints

/-- On the good remainder, every point is outside the finite discontinuity
set, so `f` is continuous there. -/
lemma continuousOn_goodRemainder
    {f : ℝ → ℝ} {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c) :
    ContinuousOn f (goodRemainder a b S rho) := by
  intro x hx
  rw [mem_goodRemainder_iff] at hx
  have hx_not_bad : x ∉ discontinuitySetOn f a b := by
    intro hxbad
    have hxS : x ∈ S := (hS x).2 hxbad
    have hle_zero : rho x ≤ 0 := by
      simpa using hx.2 x hxS
    exact (not_lt_of_ge hle_zero) (hrho_pos x hxS)
  refine (continuousWithinAt_of_not_mem_discontinuitySetOn hx.1 hx_not_bad).mono ?_
  intro y hy
  exact (mem_goodRemainder_iff.mp hy).1

/-- Compactness of the good remainder upgrades pointwise continuity of `f`
there into a uniform two-point oscillation bound. This is the good-cell side
of the finite-discontinuity partition classification. -/
lemma exists_goodRemainder_uniform_oscillation
    {f : ℝ → ℝ} {a b eta : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x : ℝ, x ∈ goodRemainder a b S rho →
      ∀ y : ℝ, y ∈ goodRemainder a b S rho →
        |x - y| < delta → |f x - f y| < eta := by
  have hcompact : IsCompact (goodRemainder a b S rho) :=
    isCompact_goodRemainder
  have hcont : ContinuousOn f (goodRemainder a b S rho) :=
    continuousOn_goodRemainder hS hrho_pos
  have hunif : UniformContinuousOn f (goodRemainder a b S rho) :=
    hcompact.uniformContinuousOn_of_continuous hcont
  rcases (Metric.uniformContinuousOn_iff.mp hunif eta heta) with
    ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x hx y hy hxy
  have hdist : dist x y < delta := by
    simpa [Real.dist_eq] using hxy
  have h := Hdelta x hx y hy hdist
  simpa [Real.dist_eq] using h

/-- Any two points in one partition cell are separated by at most that cell's
length. -/
lemma abs_sub_le_cell_length_of_mem_subinterval {a b x y : ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hx : x ∈ Partition.subinterval P i)
    (hy : y ∈ Partition.subinterval P i) :
    |x - y| ≤ P.pts i.succ - P.pts i.castSucc := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- A cell contained in the good remainder has small Darboux oscillation once
the partition mesh is smaller than the uniform-good modulus. -/
lemma exists_upperStep_sub_lowerStep_lt_of_goodRemainder_cell
    {f : ℝ → ℝ} {a b eta : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (hS : ∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (P : Partition a b) (i : Fin P.n),
        P.mesh < delta →
        Partition.subinterval P i ⊆ goodRemainder a b S rho →
          upperStep P f i - lowerStep P f i < eta := by
  have hhalf : 0 < eta / 2 := by linarith
  rcases exists_goodRemainder_uniform_oscillation
      (f := f) (a := a) (b := b) (eta := eta / 2)
      (S := S) (rho := rho) hS hrho_pos hhalf with
    ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P i hmesh hcell_good
  have hle :
      upperStep P f i - lowerStep P f i ≤ eta / 2 := by
    refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      P i hAbove hBelow ?_
    intro x hx y hy
    have hxy_len :
        |x - y| ≤ P.pts i.succ - P.pts i.castSucc :=
      abs_sub_le_cell_length_of_mem_subinterval P hx hy
    have hlen_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh :=
      by
        unfold Partition.mesh
        exact Finset.le_sup'
          (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
          (Finset.mem_univ i)
    have hxy_delta : |x - y| < delta :=
      lt_of_le_of_lt (le_trans hxy_len hlen_mesh) hmesh
    exact le_of_lt (Hdelta x (hcell_good hx) y (hcell_good hy) hxy_delta)
  linarith

/-- If both endpoints of a partition cell lie in the same ball around `c`,
then every point of the cell lies in that ball. -/
lemma abs_sub_lt_of_mem_subinterval_of_endpoints_abs_lt
    {a b c delta : ℝ} (P : Partition a b) {i : Fin P.n}
    {x : ℝ}
    (hx : x ∈ Partition.subinterval P i)
    (hleft : |P.pts i.castSucc - c| < delta)
    (hright : |P.pts i.succ - c| < delta) :
    |x - c| < delta := by
  rcases hx with ⟨hleft_x, hx_right⟩
  rcases abs_lt.mp hleft with ⟨hcl, hlc⟩
  rcases abs_lt.mp hright with ⟨_hcr, hrc⟩
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

/-- A cell whose endpoints are sufficiently close to a continuity point of
`f` has small upper-minus-lower step. -/
lemma exists_upperStep_sub_lowerStep_lt_of_continuousAt_nearby
    {f : ℝ → ℝ} {a b c eps : ℝ}
    (hf : ContinuousAt f c)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (P : Partition a b) (i : Fin P.n),
        |P.pts i.castSucc - c| < delta →
        |P.pts i.succ - c| < delta →
          upperStep P f i - lowerStep P f i < eps := by
  have hhalf : 0 < eps / 2 := by linarith
  rcases continuousAt_local_oscillation hf hhalf with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P i hleft hright
  have hle :
      upperStep P f i - lowerStep P f i ≤ eps / 2 := by
    refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      P i hAbove hBelow ?_
    intro x hx y hy
    exact le_of_lt (Hdelta x y
      (abs_sub_lt_of_mem_subinterval_of_endpoints_abs_lt P hx hleft hright)
      (abs_sub_lt_of_mem_subinterval_of_endpoints_abs_lt P hy hleft hright))
  linarith

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

/-- The coarse global bound on cell oscillation yields a coarse bound for the
whole partition oscillation by the total `α` increment. -/
lemma partitionOscillation_le_two_mul_bound_alpha_span
    {f α : ℝ → ℝ} {a b C : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    partitionOscillation P f α ≤ 2 * C * (α b - α a) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold partitionOscillation
  have htel :
      (∑ i : Fin P.n,
        (α (P.pts i.succ) - α (P.pts i.castSucc))) = α b - α a := by
    simpa [P.pts_start, P.pts_end] using sum_adjacent_sub (fun i => α (P.pts i))
  calc
    (∑ i : Fin P.n,
      (upperStep P f i - lowerStep P f i) *
        (α (P.pts i.succ) - α (P.pts i.castSucc)))
        ≤ ∑ i : Fin P.n,
          (2 * C) * (α (P.pts i.succ) - α (P.pts i.castSucc)) := by
            refine Finset.sum_le_sum ?_
            intro i hi_mem
            have hstep :
                upperStep P f i - lowerStep P f i ≤ 2 * C :=
              upperStep_sub_lowerStep_le_two_mul_abs_bound P i hAbove hBelow hC
            have hinc : 0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
              DarbouxRS.partition_increment_nonneg_of_source_core P
                ⟨hab, hAbove, hBelow, hmono⟩
            exact mul_le_mul_of_nonneg_right hstep hinc
    _ = (2 * C) * (α b - α a) := by
          rw [← Finset.mul_sum, htel]

/-- If a partition cell is not contained in the good remainder, then it meets
one of the removed bad-point balls. -/
lemma exists_bad_point_of_not_subset_goodRemainder_cell
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆ goodRemainder a b S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c := by
  rw [Set.not_subset] at hcell_not_good
  rcases hcell_not_good with ⟨x, hxcell, hxnotgood⟩
  have hxI : x ∈ Icc a b :=
    DarbouxRS.subinterval_subset_Icc_core P hxcell
  rw [mem_goodRemainder_iff] at hxnotgood
  have hnot_all : ¬ ∀ c : ℝ, c ∈ S → rho c ≤ |x - c| := by
    intro hall
    exact hxnotgood ⟨hxI, hall⟩
  push Not at hnot_all
  rcases hnot_all with ⟨c, hcS, hclose⟩
  exact ⟨c, hcS, x, hxcell, hclose⟩

/-- A bad cell for the half-radius good remainder meets a half-radius bad ball. -/
lemma exists_bad_point_half_radius_of_not_subset_goodRemainder_cell
    {a b : ℝ} {S : Finset ℝ} {rho : ℝ → ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hcell_not_good :
      ¬ Partition.subinterval P i ⊆
        goodRemainder a b S (fun c : ℝ => rho c / 2)) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      x ∈ Partition.subinterval P i ∧ |x - c| < rho c / 2 :=
  exists_bad_point_of_not_subset_goodRemainder_cell P hcell_not_good

/-- If a cell meets the half-radius ball around `c` and the mesh is below that
half-radius, then both cell endpoints lie in the full-radius ball around `c`. -/
lemma partition_cell_endpoints_abs_lt_of_meets_half_radius
    {a b c r : ℝ} (P : Partition a b) {i : Fin P.n}
    (_hr : 0 < r)
    (hmesh : P.mesh < r / 2)
    {x : ℝ} (hxcell : x ∈ Partition.subinterval P i)
    (hxclose : |x - c| < r / 2) :
    |P.pts i.castSucc - c| < r ∧ |P.pts i.succ - c| < r := by
  have hleft_mem : P.pts i.castSucc ∈ Partition.subinterval P i :=
    ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
  have hright_mem : P.pts i.succ ∈ Partition.subinterval P i :=
    ⟨le_of_lt (P.strict_mono Fin.castSucc_lt_succ), le_rfl⟩
  have hleft_len :
      |P.pts i.castSucc - x| ≤ P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval P hleft_mem hxcell
  have hright_len :
      |P.pts i.succ - x| ≤ P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval P hright_mem hxcell
  have hlen_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
    unfold Partition.mesh
    exact Finset.le_sup'
      (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
      (Finset.mem_univ i)
  have hleft_close : |P.pts i.castSucc - x| < r / 2 :=
    lt_of_le_of_lt (le_trans hleft_len hlen_mesh) hmesh
  have hright_close : |P.pts i.succ - x| < r / 2 :=
    lt_of_le_of_lt (le_trans hright_len hlen_mesh) hmesh
  have hleft_tri :
      |P.pts i.castSucc - c| ≤ |P.pts i.castSucc - x| + |x - c| := by
    have hdecomp : P.pts i.castSucc - c = (P.pts i.castSucc - x) + (x - c) := by ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hright_tri :
      |P.pts i.succ - c| ≤ |P.pts i.succ - x| + |x - c| := by
    have hdecomp : P.pts i.succ - c =
        (P.pts i.succ - x) + (x - c) := by ring
    rw [hdecomp]
    exact abs_add_le _ _
  constructor <;> linarith

/-- If both endpoints of a cell lie in `[c-r,c+r]`, monotonicity charges the
cell's Stieltjes increment to that bad-point interval. -/
lemma partition_cell_increment_le_bad_interval
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {i : Fin P.n}
    (hleft : |P.pts i.castSucc - c| < r)
    (hright : |P.pts i.succ - c| < r) :
    α (P.pts i.succ) - α (P.pts i.castSucc) ≤ α (c + r) - α (c - r) := by
  have hci : c - r ≤ P.pts i.castSucc := by
    have h := (abs_lt.mp hleft).1
    linarith
  have hjc : P.pts i.succ ≤ c + r := by
    have h := (abs_lt.mp hright).2
    linarith
  have hα_left : α (c - r) ≤ α (P.pts i.castSucc) := hα_mono hci
  have hα_right : α (P.pts i.succ) ≤ α (c + r) := hα_mono hjc
  linarith

/-- A bad cell selected by the half-radius classification can be charged to
the full bad-point `α` increment. -/
lemma partition_cell_increment_le_bad_interval_of_half_radius_hit
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {i : Fin P.n}
    (hr : 0 < r)
    (hmesh : P.mesh < r / 2)
    {x : ℝ} (hxcell : x ∈ Partition.subinterval P i)
    (hxclose : |x - c| < r / 2) :
    α (P.pts i.succ) - α (P.pts i.castSucc) ≤ α (c + r) - α (c - r) := by
  rcases partition_cell_endpoints_abs_lt_of_meets_half_radius
      P hr hmesh hxcell hxclose with ⟨hleft, hright⟩
  exact partition_cell_increment_le_bad_interval hα_mono P hleft hright

private def pointAtNat {a b : ℝ} (P : Partition a b) (j : ℕ) : ℝ :=
  if h : j ≤ P.n then P.pts ⟨j, Nat.lt_succ_iff.mpr h⟩ else b

private lemma pointAtNat_eq {a b : ℝ} (P : Partition a b)
    {j : ℕ} (hj : j ≤ P.n) :
    pointAtNat P j = P.pts ⟨j, Nat.lt_succ_iff.mpr hj⟩ := by
  simp [pointAtNat, hj]

private lemma pointAtNat_zero {a b : ℝ} (P : Partition a b) :
    pointAtNat P 0 = a := by
  simp [pointAtNat, P.pts_start]

private lemma pointAtNat_end {a b : ℝ} (P : Partition a b) :
    pointAtNat P P.n = b := by
  rw [pointAtNat_eq P (le_refl P.n)]
  convert P.pts_end using 1
  congr 1

private lemma pointAtNat_mono {a b : ℝ} (P : Partition a b)
    {i j : ℕ} (hi : i ≤ P.n) (hj : j ≤ P.n) (hij : i ≤ j) :
    pointAtNat P i ≤ pointAtNat P j := by
  rw [pointAtNat_eq P hi, pointAtNat_eq P hj]
  exact DarbouxRS.partition_pts_monotone_core P (by exact_mod_cast hij)

private lemma pointAtNat_strictMono {a b : ℝ} (P : Partition a b)
    {i j : ℕ} (hi : i ≤ P.n) (hj : j ≤ P.n) (hij : i < j) :
    pointAtNat P i < pointAtNat P j := by
  rw [pointAtNat_eq P hi, pointAtNat_eq P hj]
  exact P.strict_mono (by exact_mod_cast hij)

/-- The partition cells whose two endpoints lie strictly inside the bad-point
interval `(c-r,c+r)`. These are the geometric blocks that will later be
compressed into consecutive `Ico` index blocks. -/
noncomputable def badPointEndpointBlock {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range P.n).filter
    (fun i => c - r < pointAtNat P i ∧ pointAtNat P (i + 1) < c + r)

private lemma mem_badPointEndpointBlock_iff {a b c r : ℝ}
    (P : Partition a b) {i : ℕ} :
    i ∈ badPointEndpointBlock P c r ↔
      i < P.n ∧ c - r < pointAtNat P i ∧ pointAtNat P (i + 1) < c + r := by
  classical
  simp [badPointEndpointBlock]

/-- Disjoint real bad-point intervals induce disjoint endpoint-cell blocks. -/
lemma badPointEndpointBlock_disjoint_of_disjoint_Ioo {a b c d r s : ℝ}
    (P : Partition a b)
    (hsep :
      Disjoint (Set.Ioo (c - r) (c + r)) (Set.Ioo (d - s) (d + s))) :
    Disjoint (badPointEndpointBlock P c r) (badPointEndpointBlock P d s) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiC hiD
  rw [mem_badPointEndpointBlock_iff P] at hiC
  rw [mem_badPointEndpointBlock_iff P] at hiD
  have hstep : pointAtNat P i < pointAtNat P (i + 1) :=
    pointAtNat_strictMono P (Nat.le_of_lt hiC.1) (Nat.succ_le_of_lt hiC.1) (by omega)
  have hxC : pointAtNat P i ∈ Set.Ioo (c - r) (c + r) :=
    ⟨hiC.2.1, lt_trans hstep hiC.2.2⟩
  have hxD : pointAtNat P i ∈ Set.Ioo (d - s) (d + s) :=
    ⟨hiD.2.1, lt_trans hstep hiD.2.2⟩
  have hempty :
      Set.Ioo (c - r) (c + r) ∩ Set.Ioo (d - s) (d + s) = (∅ : Set ℝ) :=
    Set.disjoint_iff_inter_eq_empty.mp hsep
  have hxempty : pointAtNat P i ∈ (∅ : Set ℝ) := by
    simpa [hempty] using
      (show pointAtNat P i ∈
          Set.Ioo (c - r) (c + r) ∩ Set.Ioo (d - s) (d + s) from
        ⟨hxC, hxD⟩)
  exact hxempty

/-- Pairwise disjoint bad-point intervals induce pairwise disjoint endpoint-cell
blocks. -/
lemma badPointEndpointBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
    {a b : ℝ} (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ => badPointEndpointBlock P c (rho c)) := by
  classical
  rw [Set.PairwiseDisjoint] at hsep ⊢
  intro c hc d hd hne
  exact badPointEndpointBlock_disjoint_of_disjoint_Ioo P (hsep hc hd hne)

/-- Partition cutpoints at or to the right of the left endpoint of a bad-point
interval. -/
noncomputable def badPointLeftCutCandidates {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : Finset ℕ :=
  (Finset.range (P.n + 1)).filter (fun j => c - r ≤ pointAtNat P j)

/-- Partition cutpoints at or to the left of the right endpoint of a bad-point
interval. -/
noncomputable def badPointRightCutCandidates {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : Finset ℕ :=
  (Finset.range (P.n + 1)).filter (fun j => pointAtNat P j ≤ c + r)

/-- The first partition cutpoint not left of `c-r`. -/
noncomputable def badPointCanonicalLo {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : ℕ :=
  if h : (badPointLeftCutCandidates P c r).Nonempty then
    (badPointLeftCutCandidates P c r).min' h
  else 0

/-- The last partition cutpoint not right of `c+r`. -/
noncomputable def badPointCanonicalHi {a b : ℝ}
    (P : Partition a b) (c r : ℝ) : ℕ :=
  if h : (badPointRightCutCandidates P c r).Nonempty then
    (badPointRightCutCandidates P c r).max' h
  else 0

lemma badPointLeftCutCandidates_nonempty {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    (badPointLeftCutCandidates P c r).Nonempty := by
  refine ⟨P.n, ?_⟩
  simp [badPointLeftCutCandidates, pointAtNat_end P]
  linarith [hcI.2, hr]

lemma badPointRightCutCandidates_nonempty {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    (badPointRightCutCandidates P c r).Nonempty := by
  refine ⟨0, ?_⟩
  simp [badPointRightCutCandidates, pointAtNat_zero P]
  linarith [hcI.1, hr]

lemma badPointCanonicalLo_mem_leftCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalLo P c r ∈ badPointLeftCutCandidates P c r := by
  have hne := badPointLeftCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalLo]
  rw [dif_pos hne]
  exact Finset.min'_mem _ hne

lemma badPointCanonicalHi_mem_rightCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalHi P c r ∈ badPointRightCutCandidates P c r := by
  have hne := badPointRightCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalHi]
  rw [dif_pos hne]
  exact Finset.max'_mem _ hne

lemma badPointCanonicalLo_le_of_mem_leftCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) {j : ℕ}
    (hj : j ∈ badPointLeftCutCandidates P c r) :
    badPointCanonicalLo P c r ≤ j := by
  have hne := badPointLeftCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalLo]
  rw [dif_pos hne]
  exact Finset.min'_le _ j hj

lemma le_badPointCanonicalHi_of_mem_rightCandidates {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) {j : ℕ}
    (hj : j ∈ badPointRightCutCandidates P c r) :
    j ≤ badPointCanonicalHi P c r := by
  have hne := badPointRightCutCandidates_nonempty P hcI hr
  dsimp [badPointCanonicalHi]
  rw [dif_pos hne]
  exact Finset.le_max' _ j hj

lemma badPointCanonicalLo_le_n {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalLo P c r ≤ P.n := by
  have hmem := badPointCanonicalLo_mem_leftCandidates P hcI hr
  rw [badPointLeftCutCandidates] at hmem
  have hrange := (Finset.mem_filter.mp hmem).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)

lemma badPointCanonicalHi_le_n {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointCanonicalHi P c r ≤ P.n := by
  have hmem := badPointCanonicalHi_mem_rightCandidates P hcI hr
  rw [badPointRightCutCandidates] at hmem
  have hrange := (Finset.mem_filter.mp hmem).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)

private lemma badPointCanonicalLo_left_bound {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    c - r ≤ pointAtNat P (badPointCanonicalLo P c r) := by
  have hmem := badPointCanonicalLo_mem_leftCandidates P hcI hr
  rw [badPointLeftCutCandidates] at hmem
  exact (Finset.mem_filter.mp hmem).2

private lemma badPointCanonicalHi_right_bound {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    pointAtNat P (badPointCanonicalHi P c r) ≤ c + r := by
  have hmem := badPointCanonicalHi_mem_rightCandidates P hcI hr
  rw [badPointRightCutCandidates] at hmem
  exact (Finset.mem_filter.mp hmem).2

private lemma badPointCanonicalLo_right_bound_of_mesh {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r)
    (hmesh : P.mesh < r / 2) :
    pointAtNat P (badPointCanonicalLo P c r) ≤ c + r := by
  by_cases hlo0 : badPointCanonicalLo P c r = 0
  · rw [hlo0, pointAtNat_zero]
    linarith [hcI.1, hr]
  · let k := badPointCanonicalLo P c r - 1
    have hk_succ : k + 1 = badPointCanonicalLo P c r := by
      dsimp [k]
      omega
    have hk_lt_lo : k < badPointCanonicalLo P c r := by
      dsimp [k]
      omega
    have hlo_le_n := badPointCanonicalLo_le_n P hcI hr
    have hk_lt_n : k < P.n := by
      dsimp [k]
      omega
    have hk_not_mem : k ∉ badPointLeftCutCandidates P c r := by
      intro hk_mem
      have hlo_le_k := badPointCanonicalLo_le_of_mem_leftCandidates P hcI hr hk_mem
      omega
    have hk_left_lt : pointAtNat P k < c - r := by
      apply lt_of_not_ge
      intro hk_left
      apply hk_not_mem
      rw [badPointLeftCutCandidates]
      refine Finset.mem_filter.mpr ⟨?_, hk_left⟩
      exact Finset.mem_range.mpr (Nat.lt_trans hk_lt_n (Nat.lt_succ_self P.n))
    have hlen_mesh : pointAtNat P (k + 1) - pointAtNat P k ≤ P.mesh := by
      unfold Partition.mesh
      rw [pointAtNat_eq P (Nat.succ_le_of_lt hk_lt_n), pointAtNat_eq P (Nat.le_of_lt hk_lt_n)]
      exact Finset.le_sup'
        (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
        (Finset.mem_univ ⟨k, hk_lt_n⟩)
    have hlen_lt : pointAtNat P (badPointCanonicalLo P c r) - pointAtNat P k < r / 2 := by
      have h := lt_of_le_of_lt hlen_mesh hmesh
      simpa [hk_succ] using h
    linarith

lemma badPointCanonicalLo_le_hi_of_mesh {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r)
    (hmesh : P.mesh < r / 2) :
    badPointCanonicalLo P c r ≤ badPointCanonicalHi P c r := by
  have hlo_le_n := badPointCanonicalLo_le_n P hcI hr
  have hlo_right := badPointCanonicalLo_right_bound_of_mesh P hcI hr hmesh
  have hlo_mem_right : badPointCanonicalLo P c r ∈ badPointRightCutCandidates P c r := by
    rw [badPointRightCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, hlo_right⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlo_le_n)
  exact le_badPointCanonicalHi_of_mem_rightCandidates P hcI hr hlo_mem_right

/-- The endpoint-selected bad cells around `c` are covered by the canonical
consecutive block cut out by the first left and last right partition cutpoints. -/
lemma badPointEndpointBlock_subset_canonical_Ico {a b c r : ℝ}
    (P : Partition a b)
    (hcI : c ∈ Icc a b) (hr : 0 < r) :
    badPointEndpointBlock P c r ⊆
      Finset.Ico (badPointCanonicalLo P c r) (badPointCanonicalHi P c r) := by
  intro i hi_block
  rw [mem_badPointEndpointBlock_iff P] at hi_block
  have hi_left : i ∈ badPointLeftCutCandidates P c r := by
    rw [badPointLeftCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, le_of_lt hi_block.2.1⟩
    exact Finset.mem_range.mpr (Nat.lt_trans hi_block.1 (Nat.lt_succ_self P.n))
  have hi_right : i + 1 ∈ badPointRightCutCandidates P c r := by
    rw [badPointRightCutCandidates]
    refine Finset.mem_filter.mpr ⟨?_, le_of_lt hi_block.2.2⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hi_block.1))
  rw [Finset.mem_Ico]
  exact ⟨badPointCanonicalLo_le_of_mem_leftCandidates P hcI hr hi_left,
    Nat.lt_of_succ_le
      (le_badPointCanonicalHi_of_mem_rightCandidates P hcI hr hi_right)⟩

/-- Pairwise-disjoint bad-point intervals induce pairwise-disjoint canonical
consecutive partition-index blocks. -/
lemma badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
    {a b : ℝ} (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ =>
        Finset.Ico (badPointCanonicalLo P c (rho c))
          (badPointCanonicalHi P c (rho c))) := by
  classical
  rw [Set.PairwiseDisjoint] at hsep ⊢
  intro c hc d hd hne
  change Disjoint
    (Finset.Ico (badPointCanonicalLo P c (rho c))
      (badPointCanonicalHi P c (rho c)))
    (Finset.Ico (badPointCanonicalLo P d (rho d))
      (badPointCanonicalHi P d (rho d)))
  rw [Finset.disjoint_left]
  intro i hiC hiD
  rw [Finset.mem_Ico] at hiC hiD
  have hhiC_le_n := badPointCanonicalHi_le_n P (hcI c hc) (hrho_pos c hc)
  have hhiD_le_n := badPointCanonicalHi_le_n P (hcI d hd) (hrho_pos d hd)
  have hi_lt_n : i < P.n := lt_of_lt_of_le hiC.2 hhiC_le_n
  have hstep : pointAtNat P i < pointAtNat P (i + 1) :=
    pointAtNat_strictMono P (Nat.le_of_lt hi_lt_n) (Nat.succ_le_of_lt hi_lt_n) (by omega)
  let y : ℝ := (pointAtNat P i + pointAtNat P (i + 1)) / 2
  have hleftC : c - rho c ≤ pointAtNat P i := by
    exact le_trans
      (badPointCanonicalLo_left_bound P (hcI c hc) (hrho_pos c hc))
      (pointAtNat_mono P
        (badPointCanonicalLo_le_n P (hcI c hc) (hrho_pos c hc))
        (Nat.le_of_lt hi_lt_n) hiC.1)
  have hrightC : pointAtNat P (i + 1) ≤ c + rho c := by
    exact le_trans
      (pointAtNat_mono P (Nat.succ_le_of_lt hi_lt_n) hhiC_le_n
        (Nat.succ_le_of_lt hiC.2))
      (badPointCanonicalHi_right_bound P (hcI c hc) (hrho_pos c hc))
  have hleftD : d - rho d ≤ pointAtNat P i := by
    exact le_trans
      (badPointCanonicalLo_left_bound P (hcI d hd) (hrho_pos d hd))
      (pointAtNat_mono P
        (badPointCanonicalLo_le_n P (hcI d hd) (hrho_pos d hd))
        (Nat.le_of_lt hi_lt_n) hiD.1)
  have hrightD : pointAtNat P (i + 1) ≤ d + rho d := by
    exact le_trans
      (pointAtNat_mono P (Nat.succ_le_of_lt hi_lt_n) hhiD_le_n
        (Nat.succ_le_of_lt hiD.2))
      (badPointCanonicalHi_right_bound P (hcI d hd) (hrho_pos d hd))
  have hy_left : pointAtNat P i < y := by
    dsimp [y]
    linarith
  have hy_right : y < pointAtNat P (i + 1) := by
    dsimp [y]
    linarith
  have hyC : y ∈ Set.Ioo (c - rho c) (c + rho c) :=
    ⟨lt_of_le_of_lt hleftC hy_left, lt_of_lt_of_le hy_right hrightC⟩
  have hyD : y ∈ Set.Ioo (d - rho d) (d + rho d) :=
    ⟨lt_of_le_of_lt hleftD hy_left, lt_of_lt_of_le hy_right hrightD⟩
  have hempty :
      Set.Ioo (c - rho c) (c + rho c) ∩
          Set.Ioo (d - rho d) (d + rho d) = (∅ : Set ℝ) :=
    Set.disjoint_iff_inter_eq_empty.mp (hsep hc hd hne)
  have hyempty : y ∈ (∅ : Set ℝ) := by
    simpa [hempty] using
      (show y ∈
          Set.Ioo (c - rho c) (c + rho c) ∩
            Set.Ioo (d - rho d) (d + rho d) from
        ⟨hyC, hyD⟩)
  exact hyempty

/-- A consecutive block of partition cells contained in a bad-point interval
telescopes to at most that interval's `α` increment. -/
private lemma partition_increment_sum_Ico_le_bad_interval
    {α : ℝ → ℝ} {a b c r : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b) {j0 j1 : ℕ}
    (hj0j1 : j0 ≤ j1)
    (_hj1 : j1 ≤ P.n)
    (hleft : c - r ≤ pointAtNat P j0)
    (hright : pointAtNat P j1 ≤ c + r) :
    (∑ i ∈ Finset.Ico j0 j1,
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      α (c + r) - α (c - r) := by
  have htel :
      (∑ i ∈ Finset.Ico j0 j1,
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) =
        α (pointAtNat P j1) - α (pointAtNat P j0) := by
    exact Finset.sum_Ico_sub (fun k => α (pointAtNat P k)) hj0j1
  have hα_left : α (c - r) ≤ α (pointAtNat P j0) := hα_mono hleft
  have hα_right : α (pointAtNat P j1) ≤ α (c + r) := hα_mono hright
  rw [htel]
  linarith

/-- If each bad point is assigned one consecutive block of partition cells inside
its bad interval, the sum of those block increments is charged by the sum of the
bad-point `α` increments. -/
private lemma partition_increment_sum_Ico_blocks_le_bad_intervals
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ c ∈ S,
        ∑ i ∈ Finset.Ico (lo c) (hi c),
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  refine Finset.sum_le_sum ?_
  intro c hc
  exact partition_increment_sum_Ico_le_bad_interval hα_mono P
    (hlohi c hc) (hhi c hc) (hleft c hc) (hright c hc)

/-- A disjoint cover of a bad index set by consecutive bad-point blocks gives
the desired global bad-cell `α`-increment charge. The remaining geometric work
is to build such blocks from the half-radius bad-cell classification. -/
private lemma partition_increment_sum_le_bad_intervals_of_disjoint_Ico_cover
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (B : Finset ℕ) (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hdisj :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hcover :
      B ⊆ S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ i ∈ B, (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  let blockUnion : Finset ℕ :=
    S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c))
  let inc : ℕ → ℝ := fun i => α (pointAtNat P (i + 1)) - α (pointAtNat P i)
  have hB_le_union :
      (∑ i ∈ B, inc i) ≤ ∑ i ∈ blockUnion, inc i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hcover ?_
    intro i hi_union _hi_not_B
    rcases (Finset.mem_biUnion.mp hi_union) with ⟨c, hcS, hiIco⟩
    have hi_lt : i < P.n := by
      have hi_block := (Finset.mem_Ico.mp hiIco).2
      exact lt_of_lt_of_le hi_block (hhi c hcS)
    have hpts : pointAtNat P i ≤ pointAtNat P (i + 1) :=
      pointAtNat_mono P (Nat.le_of_lt hi_lt) (Nat.succ_le_of_lt hi_lt) (by omega)
    have hα : α (pointAtNat P i) ≤ α (pointAtNat P (i + 1)) := hα_mono hpts
    dsimp [inc]
    linarith
  have hunion_eq :
      (∑ i ∈ blockUnion, inc i) =
        ∑ c ∈ S, ∑ i ∈ Finset.Ico (lo c) (hi c), inc i := by
    dsimp [blockUnion]
    exact Finset.sum_biUnion hdisj
  have hblocks_le :
      (∑ c ∈ S,
          ∑ i ∈ Finset.Ico (lo c) (hi c),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
        ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) :=
    partition_increment_sum_Ico_blocks_le_bad_intervals hα_mono P S rho lo hi
      hlohi hhi hleft hright
  calc
    (∑ i ∈ B, (α (pointAtNat P (i + 1)) - α (pointAtNat P i)))
        = ∑ i ∈ B, inc i := by rfl
    _ ≤ ∑ i ∈ blockUnion, inc i := hB_le_union
    _ = ∑ c ∈ S, ∑ i ∈ Finset.Ico (lo c) (hi c), inc i := hunion_eq
    _ = ∑ c ∈ S,
          ∑ i ∈ Finset.Ico (lo c) (hi c),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by rfl
    _ ≤ ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := hblocks_le

/-- Split the partition oscillation into a small good-cell contribution plus
a coarse bad-cell contribution supported on a chosen finite index set. -/
lemma partitionOscillation_le_good_bad_split
    {f α : ℝ → ℝ} {a b C eta : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (B : Finset ℕ)
    (heta_nonneg : 0 ≤ eta)
    (hgood :
      ∀ i : Fin P.n, i.val ∉ B →
        upperStep P f i - lowerStep P f i ≤ eta)
    (hbad :
      ∀ i : Fin P.n, i.val ∈ B →
        upperStep P f i - lowerStep P f i ≤ 2 * C) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C *
          (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B),
            (α (P.pts i.succ) - α (P.pts i.castSucc))) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold partitionOscillation
  let inc : Fin P.n → ℝ := fun i => α (P.pts i.succ) - α (P.pts i.castSucc)
  have htel :
      (∑ i : Fin P.n, inc i) = α b - α a := by
    simpa [inc, P.pts_start, P.pts_end] using sum_adjacent_sub (fun i => α (P.pts i))
  have hsum_le :
      (∑ i : Fin P.n,
        (upperStep P f i - lowerStep P f i) * inc i)
        ≤ ∑ i : Fin P.n,
            (eta * inc i + if i.val ∈ B then (2 * C) * inc i else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hinc_nonneg : 0 ≤ inc i :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    by_cases hiB : i.val ∈ B
    · have hterm :
          (upperStep P f i - lowerStep P f i) * inc i ≤
            (2 * C) * inc i :=
        mul_le_mul_of_nonneg_right (hbad i hiB) hinc_nonneg
      have heta_inc : 0 ≤ eta * inc i := mul_nonneg heta_nonneg hinc_nonneg
      simp [hiB]
      linarith
    · have hterm :
          (upperStep P f i - lowerStep P f i) * inc i ≤
            eta * inc i :=
        mul_le_mul_of_nonneg_right (hgood i hiB) hinc_nonneg
      simp [hiB]
      exact hterm
  have hsum_eq :
      (∑ i : Fin P.n,
            (eta * inc i + if i.val ∈ B then (2 * C) * inc i else 0)) =
        eta * (α b - α a) +
          2 * C *
            (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
    rw [Finset.sum_add_distrib]
    have hfirst :
        (∑ i : Fin P.n, eta * inc i) = eta * (α b - α a) := by
      rw [← Finset.mul_sum, htel]
    have hsecond :
        (∑ i : Fin P.n, (if i.val ∈ B then (2 * C) * inc i else 0)) =
          2 * C *
            (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
      calc
        (∑ i : Fin P.n, (if i.val ∈ B then (2 * C) * inc i else 0))
            = ∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B),
                (2 * C) * inc i := by
              rw [Finset.sum_filter]
        _ = 2 * C *
              (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter (fun i => i.val ∈ B), inc i) := by
              rw [Finset.mul_sum]
    rw [hfirst, hsecond]
  exact le_trans hsum_le (le_of_eq hsum_eq)

/-- The partition indices whose cells are not contained in the chosen good
remainder. These are the cells that must be charged to bad-point neighborhoods. -/
private def subintervalAtNat {a b : ℝ} (P : Partition a b) (i : ℕ) : Set ℝ :=
  if h : i < P.n then Partition.subinterval P ⟨i, h⟩ else ∅

private lemma subintervalAtNat_eq {a b : ℝ} (P : Partition a b)
    {i : ℕ} (hi : i < P.n) :
    subintervalAtNat P i = Partition.subinterval P ⟨i, hi⟩ := by
  simp [subintervalAtNat, hi]

noncomputable def badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ) :
    Finset ℕ := by
  classical
  exact (Finset.range P.n).filter
    (fun i => ¬ subintervalAtNat P i ⊆ goodRemainder a b S rho)

lemma mem_badCellIndices_iff {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ) {i : ℕ} :
    i ∈ badCellIndices P S rho ↔
      i < P.n ∧
        ∀ hi : i < P.n,
          ¬ Partition.subinterval P ⟨i, hi⟩ ⊆ goodRemainder a b S rho := by
  classical
  rw [badCellIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, hbad⟩
    refine ⟨hi, ?_⟩
    intro hi'
    simpa [subintervalAtNat, hi] using hbad
  · rintro ⟨hi, hbad⟩
    refine ⟨hi, ?_⟩
    simpa [subintervalAtNat, hi] using hbad hi

lemma cell_subset_goodRemainder_of_not_mem_badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (i : Fin P.n)
    (hi_not_bad : i.val ∉ badCellIndices P S rho) :
    Partition.subinterval P i ⊆ goodRemainder a b S rho := by
  by_contra hnot
  exact hi_not_bad ((mem_badCellIndices_iff P S rho).2 ⟨i.isLt, fun _ => hnot⟩)

lemma exists_bad_point_of_mem_badCellIndices {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    {i : ℕ} (hi_bad : i ∈ badCellIndices P S rho) :
    ∃ c : ℝ, c ∈ S ∧ ∃ x : ℝ,
      ∃ hi : i < P.n, x ∈ Partition.subinterval P ⟨i, hi⟩ ∧ |x - c| < rho c := by
  rcases (mem_badCellIndices_iff P S rho).1 hi_bad with ⟨hi, hnot⟩
  rcases exists_bad_point_of_not_subset_goodRemainder_cell P (hnot hi) with
    ⟨c, hc, x, hx, hclose⟩
  exact ⟨c, hc, x, hi, hx, hclose⟩

/-- With mesh below every half-radius, each half-radius bad cell is covered by
the endpoint block of some bad point. -/
lemma badCellIndices_half_radius_subset_badPointEndpointBlocks {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => badPointEndpointBlock P c (rho c)) := by
  classical
  intro i hi_bad
  rcases (mem_badCellIndices_iff P S (fun c : ℝ => rho c / 2)).1 hi_bad with
    ⟨hi, hnot_good⟩
  rcases exists_bad_point_half_radius_of_not_subset_goodRemainder_cell
      P (hnot_good hi) with
    ⟨c, hcS, x, hxcell, hxclose⟩
  rcases partition_cell_endpoints_abs_lt_of_meets_half_radius
      P (hrho_pos c hcS) (hmesh c hcS) hxcell hxclose with
    ⟨hleft_abs, hright_abs⟩
  refine Finset.mem_biUnion.mpr ⟨c, hcS, ?_⟩
  rw [mem_badPointEndpointBlock_iff P]
  refine ⟨hi, ?_, ?_⟩
  · have hleft_abs' : |pointAtNat P i - c| < rho c := by
      rw [pointAtNat_eq P (Nat.le_of_lt hi)]
      simpa using hleft_abs
    have hleft := (abs_lt.mp hleft_abs').1
    linarith
  · have hright_abs' : |pointAtNat P (i + 1) - c| < rho c := by
      rw [pointAtNat_eq P (Nat.succ_le_of_lt hi)]
      simpa using hright_abs
    have hright := (abs_lt.mp hright_abs').2
    linarith

/-- If every endpoint block is contained in an assigned consecutive `Ico`
block, the half-radius bad-cell set is covered by the assigned `Ico` blocks. -/
lemma badCellIndices_half_radius_subset_Ico_blocks_of_endpointBlock_cover
    {a b : ℝ}
    (P : Partition a b) (S : Finset ℝ) (rho : ℝ → ℝ)
    (lo hi : ℝ → ℕ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hblock_cover :
      ∀ c : ℝ, c ∈ S →
        badPointEndpointBlock P c (rho c) ⊆ Finset.Ico (lo c) (hi c)) :
    badCellIndices P S (fun c : ℝ => rho c / 2) ⊆
      S.biUnion (fun c : ℝ => Finset.Ico (lo c) (hi c)) := by
  classical
  intro i hi_bad
  have hendpoint_cover :=
    badCellIndices_half_radius_subset_badPointEndpointBlocks
      P S rho hrho_pos hmesh hi_bad
  rcases (Finset.mem_biUnion.mp hendpoint_cover) with ⟨c, hcS, hi_block⟩
  exact Finset.mem_biUnion.mpr ⟨c, hcS, hblock_cover c hcS hi_block⟩

/-- Endpoint-block coverage is the remaining geometric input needed to apply
the existing disjoint-`Ico` bad-interval summation lemma to the canonical
half-radius bad-cell set. -/
private lemma partition_increment_sum_badCellIndices_half_radius_le_bad_intervals
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ) (lo hi : ℝ → ℕ)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hblock_cover :
      ∀ c : ℝ, c ∈ S →
        badPointEndpointBlock P c (rho c) ⊆ Finset.Ico (lo c) (hi c))
    (hdisj :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Finset.Ico (lo c) (hi c)))
    (hlohi : ∀ c : ℝ, c ∈ S → lo c ≤ hi c)
    (hhi : ∀ c : ℝ, c ∈ S → hi c ≤ P.n)
    (hleft : ∀ c : ℝ, c ∈ S → c - rho c ≤ pointAtNat P (lo c))
    (hright : ∀ c : ℝ, c ∈ S → pointAtNat P (hi c) ≤ c + rho c) :
    (∑ i ∈ badCellIndices P S (fun c : ℝ => rho c / 2),
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  classical
  refine partition_increment_sum_le_bad_intervals_of_disjoint_Ico_cover
    hα_mono P (badCellIndices P S (fun c : ℝ => rho c / 2))
    S rho lo hi hdisj ?_ hlohi hhi hleft hright
  exact badCellIndices_half_radius_subset_Ico_blocks_of_endpointBlock_cover
    P S rho lo hi hrho_pos hmesh hblock_cover

/-- Canonical cutpoint blocks discharge the bad-cell `α` increment estimate for
the half-radius good-remainder classification. -/
private lemma partition_increment_sum_badCellIndices_half_radius_le_bad_intervals_canonical
    {α : ℝ → ℝ} {a b : ℝ}
    (hα_mono : Monotone α)
    (P : Partition a b)
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    (∑ i ∈ badCellIndices P S (fun c : ℝ => rho c / 2),
        (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) ≤
      ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  refine partition_increment_sum_badCellIndices_half_radius_le_bad_intervals
    hα_mono P S rho
    (fun c : ℝ => badPointCanonicalLo P c (rho c))
    (fun c : ℝ => badPointCanonicalHi P c (rho c))
    hrho_pos hmesh ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    exact badPointEndpointBlock_subset_canonical_Ico P (hcI c hc) (hrho_pos c hc)
  · exact badPointCanonicalIcoBlocks_pairwiseDisjoint_of_pairwiseDisjoint_Ioo
      P S rho hcI hrho_pos hsep
  · intro c hc
    exact badPointCanonicalLo_le_hi_of_mesh P (hcI c hc) (hrho_pos c hc) (hmesh c hc)
  · intro c hc
    exact badPointCanonicalHi_le_n P (hcI c hc) (hrho_pos c hc)
  · intro c hc
    exact badPointCanonicalLo_left_bound P (hcI c hc) (hrho_pos c hc)
  · intro c hc
    exact badPointCanonicalHi_right_bound P (hcI c hc) (hrho_pos c hc)

/-- Once the good-cell Darboux bound is available for cells contained in the
good remainder, the whole oscillation sum reduces to the chosen bad-cell
increment sum. -/
private lemma partitionOscillation_le_goodRemainder_badCell_split
    {f α : ℝ → ℝ} {a b C eta δgood : ℝ}
    {S : Finset ℝ} {rho : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hgood_step :
      ∀ (P' : Partition a b) (i : Fin P'.n),
        P'.mesh < δgood →
        Partition.subinterval P' i ⊆ goodRemainder a b S rho →
          upperStep P' f i - lowerStep P' f i < eta)
    (hmesh_good : P.mesh < δgood) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C *
          (∑ i ∈ badCellIndices P S rho,
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i))) := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  let hs' : SourceHypotheses a b f α :=
    ⟨hab, hAbove, hBelow, hmono⟩
  have hsplit := partitionOscillation_le_good_bad_split
    (f := f) (α := α) (a := a) (b := b) (C := C) (eta := eta)
    hs' P (badCellIndices P S rho) heta_nonneg
    (fun i hi_not_bad =>
      le_of_lt (hgood_step P i hmesh_good
        (cell_subset_goodRemainder_of_not_mem_badCellIndices P S rho i hi_not_bad)))
    (fun i _hi_bad =>
      upperStep_sub_lowerStep_le_two_mul_abs_bound P i hAbove hBelow hC)
  have hfin_to_range :
      (∑ i ∈ (Finset.univ : Finset (Fin P.n)).filter
          (fun i => i.val ∈ badCellIndices P S rho),
          (α (P.pts i.succ) - α (P.pts i.castSucc))) =
        ∑ i ∈ (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho),
          (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
    rw [Finset.sum_filter]
    calc
      (∑ i : Fin P.n,
          if i.val ∈ badCellIndices P S rho then
            α (P.pts i.succ) - α (P.pts i.castSucc)
          else 0) =
          ∑ i : Fin P.n,
            if i.val ∈ badCellIndices P S rho then
              α (pointAtNat P (i.val + 1)) - α (pointAtNat P i.val)
            else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i _
              by_cases hi : i.val ∈ badCellIndices P S rho
              · simp only [hi, if_true]
                rw [pointAtNat_eq P (Nat.succ_le_of_lt i.isLt),
                  pointAtNat_eq P (Nat.le_of_lt i.isLt)]
                rfl
              · simp [hi]
      _ = ∑ i ∈ Finset.range P.n,
            if i ∈ badCellIndices P S rho then
              α (pointAtNat P (i + 1)) - α (pointAtNat P i)
            else 0 := by
              exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
                if i ∈ badCellIndices P S rho then
                  α (pointAtNat P (i + 1)) - α (pointAtNat P i)
                else 0) P.n
      _ = ∑ i ∈ (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho),
            (α (pointAtNat P (i + 1)) - α (pointAtNat P i)) := by
              rw [Finset.sum_filter]
  have hfilter_eq :
      (Finset.range P.n).filter (fun i => i ∈ badCellIndices P S rho) =
        badCellIndices P S rho := by
    ext i
    simp [badCellIndices]
  rw [hfin_to_range, hfilter_eq] at hsplit
  exact hsplit

/-- Clean cross-file estimate combining the good-cell oscillation bound with
the canonical bad-interval charge, without exposing implementation-only
natural-number partition accessors. -/
lemma partitionOscillation_le_goodRemainder_badIntervals
    {f α : ℝ → ℝ} {a b C eta δgood : ℝ}
    {S : Finset ℝ} {rho : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    (hα_mono : Monotone α)
    (P : Partition a b)
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (hC_nonneg : 0 ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hgood_step :
      ∀ (P' : Partition a b) (i : Fin P'.n),
        P'.mesh < δgood →
        Partition.subinterval P' i ⊆
          goodRemainder a b S (fun c : ℝ => rho c / 2) →
          upperStep P' f i - lowerStep P' f i < eta)
    (hmesh_good : P.mesh < δgood)
    (hcI : ∀ c : ℝ, c ∈ S → c ∈ Icc a b)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c)
    (hmesh_bad : ∀ c : ℝ, c ∈ S → P.mesh < rho c / 2)
    (hsep :
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c))) :
    partitionOscillation P f α ≤
      eta * (α b - α a) +
        2 * C * ∑ c ∈ S, (α (c + rho c) - α (c - rho c)) := by
  have hsplit := partitionOscillation_le_goodRemainder_badCell_split
    (f := f) (α := α) (a := a) (b := b)
    (C := C) (eta := eta) (δgood := δgood)
    (S := S) (rho := fun c : ℝ => rho c / 2)
    hs P hC heta_nonneg hgood_step hmesh_good
  have hbad :=
    partition_increment_sum_badCellIndices_half_radius_le_bad_intervals_canonical
      hα_mono P S rho hcI hrho_pos hmesh_bad hsep
  have htwoC_nonneg : 0 ≤ 2 * C :=
    mul_nonneg (by norm_num) hC_nonneg
  have hbad_term :=
    mul_le_mul_of_nonneg_left hbad htwoC_nonneg
  linarith

/-- A positive mesh threshold can be chosen below a good-cell modulus and below
all half-radii attached to a finite bad set. -/
lemma exists_pos_mesh_bound_le_good_and_half_radii
    (S : Finset ℝ) (rho : ℝ → ℝ) {δgood : ℝ}
    (hδgood : 0 < δgood)
    (hrho_pos : ∀ c : ℝ, c ∈ S → 0 < rho c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δgood ∧
      ∀ c : ℝ, c ∈ S → δ ≤ rho c / 2 := by
  classical
  by_cases hS : S.Nonempty
  · let rmin : ℝ := S.inf' hS (fun c : ℝ => rho c / 2)
    have hrmin_pos : 0 < rmin := by
      dsimp [rmin]
      rw [Finset.lt_inf'_iff]
      intro c hc
      linarith [hrho_pos c hc]
    refine ⟨min δgood rmin, ?_, ?_, ?_⟩
    · exact lt_min hδgood hrmin_pos
    · exact min_le_left δgood rmin
    · intro c hc
      exact le_trans (min_le_right δgood rmin)
        (by
          dsimp [rmin]
          exact Finset.inf'_le (fun c : ℝ => rho c / 2) hc)
  · refine ⟨δgood, hδgood, le_rfl, ?_⟩
    intro c hc
    exact False.elim (hS ⟨c, hc⟩)


end Thm11SourceRoute
