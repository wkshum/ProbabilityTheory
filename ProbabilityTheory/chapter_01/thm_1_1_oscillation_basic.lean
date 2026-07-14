import ProbabilityTheory.chapter_01.thm_1_1_basic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
<<<<<<< HEAD
open MeasureTheory
=======
>>>>>>> 9f9e0899aab75b7bd64d9e5f546a93c80411d6af
open Set Topology

noncomputable section

namespace Thm11SourceRoute


noncomputable def partitionOscillation {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    (upperStep P f i - lowerStep P f i) *
      (α (P.pts i.succ) - α (P.pts i.castSucc))

/-- The upper-lower Darboux gap is the partition oscillation sum. -/
lemma upperSum_sub_lowerSum_eq_partitionOscillation {f α : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) :
    upperSum P f α - lowerSum P f α =
      partitionOscillation P f α := by
  unfold partitionOscillation upperSum lowerSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-- Under source hypotheses, the partition oscillation sum is nonnegative. -/
lemma partitionOscillation_nonneg_of_source {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) :
    0 ≤ partitionOscillation P f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold partitionOscillation
  refine Finset.sum_nonneg ?_
  intro i hi_mem
  have hstep_le : lowerStep P f i ≤ upperStep P f i :=
    DarbouxRS.lowerStep_le_upperStep_core P i hBelow hAbove
  have hosc_nonneg :
      0 ≤ upperStep P f i - lowerStep P f i :=
    sub_nonneg.mpr hstep_le
  have hinc_nonneg : 0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
    DarbouxRS.partition_increment_nonneg_of_source_core P
      ⟨hab, hAbove, hBelow, hmono⟩
  exact mul_nonneg hosc_nonneg hinc_nonneg

/-- A bounded integrand on `[a,b]` admits one positive absolute-value bound.
This is the global `M` used in the finite-discontinuity oscillation estimate
near the finitely many bad points. -/
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

/-- If all values of `f` on a partition cell differ by at most `eta`, then
the cell upper-minus-lower step is at most `eta`. -/
lemma upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
    {f : ℝ → ℝ} {a b eta : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hosc :
      ∀ x, x ∈ Partition.subinterval P i →
      ∀ y, y ∈ Partition.subinterval P i → |f x - f y| ≤ eta) :
    upperStep P f i - lowerStep P f i ≤ eta := by
  let cell := Partition.subinterval P i
  have hcell_nonempty : (f '' cell).Nonempty := by
    refine ⟨f (P.pts i.castSucc), ?_⟩
    refine ⟨P.pts i.castSucc, ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
  have hcellAbove : BddAbove (f '' cell) :=
    BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hAbove
  have hcellBelow : BddBelow (f '' cell) :=
    BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P)) hBelow
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
  unfold upperStep lowerStep
  linarith

/-- A uniform absolute-value bound on `[a,b]` gives a coarse cell oscillation
bound. This is the estimate used for cells near discontinuities. -/
lemma upperStep_sub_lowerStep_le_two_mul_abs_bound
    {f : ℝ → ℝ} {a b C : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hC : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C) :
    upperStep P f i - lowerStep P f i ≤ 2 * C := by
  refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
    P i hAbove hBelow ?_
  intro x hx y hy
  have hxI : x ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hx
  have hyI : y ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hy
  have hxC := hC x hxI
  have hyC := hC y hyI
  have htri : |f x - f y| ≤ |f x| + |f y| := by
    calc
      |f x - f y| = |f x + -f y| := by ring_nf
      _ ≤ |f x| + |-f y| := abs_add_le (f x) (-f y)
      _ = |f x| + |f y| := by rw [abs_neg]
  linarith

/-- Metric form of continuity at a real point, specialized to absolute values. -/
lemma continuousAt_abs_sub_lt {g : ℝ → ℝ} {c eps : ℝ}
    (hg : ContinuousAt g c) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x : ℝ, |x - c| < delta → |g x - g c| < eps := by
  rcases (Metric.continuousAt_iff.mp hg eps heps) with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x hx
  have hx' : dist x c < delta := by
    simpa [Real.dist_eq] using hx
  have h := Hdelta hx'
  simpa [Real.dist_eq] using h

/-- Continuity of `f` at `c` gives a local two-point oscillation bound. -/
lemma continuousAt_local_oscillation {f : ℝ → ℝ} {c eps : ℝ}
    (hf : ContinuousAt f c) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x y : ℝ,
        |x - c| < delta → |y - c| < delta → |f x - f y| < eps := by
  have hhalf : 0 < eps / 2 := by linarith
  rcases continuousAt_abs_sub_lt hf hhalf with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x y hx hy
  have hx' := Hdelta x hx
  have hy' := Hdelta y hy
  have htri : |f x - f y| ≤ |f x - f c| + |f y - f c| := by
    calc
      |f x - f y| = |(f x - f c) + -(f y - f c)| := by ring_nf
      _ ≤ |f x - f c| + |-(f y - f c)| :=
        abs_add_le (f x - f c) (-(f y - f c))
      _ = |f x - f c| + |f y - f c| := by rw [abs_neg]
  linarith

/-- Continuity of the integrator at a bad point makes its local increment
small. The finite-discontinuity proof later sums this estimate over the
finite bad set. -/
lemma continuousAt_alpha_local_increment {α : ℝ → ℝ} {c eps : ℝ}
    (hα : ContinuousAt α c) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x y : ℝ,
        |x - c| < delta → |y - c| < delta → α y - α x < eps := by
  have hhalf : 0 < eps / 2 := by linarith
  rcases continuousAt_abs_sub_lt hα hhalf with ⟨delta, hdelta, Hdelta⟩
  refine ⟨delta, hdelta, ?_⟩
  intro x y hx hy
  have hx' := abs_lt.mp (Hdelta x hx)
  have hy' := abs_lt.mp (Hdelta y hy)
  linarith

/-- Finite bad points can be assigned local radii so the sum of the
corresponding `α` increments is arbitrarily small. This is the finite
summation form of continuity of the integrator at each bad point. -/
lemma finite_sum_alpha_local_increment_small {α : ℝ → ℝ}
    (S : Finset ℝ)
    (hα : ∀ c : ℝ, c ∈ S → ContinuousAt α c)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ → ℝ,
      (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
      (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps := by
  let quota : ℝ := eps / ((S.card : ℝ) + 1)
  have hden_pos : 0 < (S.card : ℝ) + 1 := by positivity
  have hquota : 0 < quota := div_pos heps hden_pos
  have hsmall :
      ∀ c : ℝ, c ∈ S →
        ∃ delta : ℝ, 0 < delta ∧
          α (c + delta / 2) - α (c - delta / 2) < quota := by
    intro c hc
    rcases continuousAt_alpha_local_increment (hα c hc) hquota with
      ⟨delta, hdelta, Hdelta⟩
    refine ⟨delta, hdelta, ?_⟩
    have hleft : |(c - delta / 2) - c| < delta := by
      refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
    have hright : |(c + delta / 2) - c| < delta := by
      refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
    exact Hdelta (c - delta / 2) (c + delta / 2) hleft hright
  let rho : ℝ → ℝ := fun c =>
    if hc : c ∈ S then Classical.choose (hsmall c hc) / 2 else 1
  refine ⟨rho, ?_, ?_⟩
  · intro c hc
    dsimp [rho]
    rw [dif_pos hc]
    have hdelta_pos : 0 < Classical.choose (hsmall c hc) :=
      (Classical.choose_spec (hsmall c hc)).1
    linarith
  · have hterm :
        ∀ c : ℝ, c ∈ S →
          α (c + rho c) - α (c - rho c) < quota := by
      intro c hc
      dsimp [rho]
      rw [dif_pos hc]
      exact (Classical.choose_spec (hsmall c hc)).2
    have hsum_le :
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) ≤
          ∑ _c ∈ S, quota := by
      refine Finset.sum_le_sum ?_
      intro c hc
      exact le_of_lt (hterm c hc)
    have hconst :
        (∑ _c ∈ S, quota) = (S.card : ℝ) * quota := by
      simp
    have hcard_quota_lt : (S.card : ℝ) * quota < eps := by
      have hcard_lt : (S.card : ℝ) < (S.card : ℝ) + 1 := by linarith
      have hmul_lt :
          (S.card : ℝ) * quota < ((S.card : ℝ) + 1) * quota :=
        mul_lt_mul_of_pos_right hcard_lt hquota
      have hquota_eq : ((S.card : ℝ) + 1) * quota = eps := by
        dsimp [quota]
        field_simp [ne_of_gt hden_pos]
      linarith
    exact lt_of_le_of_lt hsum_le (by simpa [hconst] using hcard_quota_lt)

/-- For a monotone integrator, shrinking a symmetric interval around a point
does not increase its `α`-increment. -/
lemma alpha_local_increment_mono_of_radius_le {α : ℝ → ℝ}
    (hα_mono : Monotone α) {c r R : ℝ}
    (hrR : r ≤ R) :
    α (c + r) - α (c - r) ≤ α (c + R) - α (c - R) := by
  have hleft : c - R ≤ c - r := by linarith
  have hright : c + r ≤ c + R := by linarith
  have hα_left : α (c - R) ≤ α (c - r) := hα_mono hleft
  have hα_right : α (c + r) ≤ α (c + R) := hα_mono hright
  linarith

/-- If all radii are at most one quarter of the finite set's infimum
separation, the corresponding open real intervals are pairwise disjoint. -/
lemma pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four
    (S : Finset ℝ) (rho : ℝ → ℝ)
    (hrho_le :
      ∀ c : ℝ, c ∈ S →
        (S : Set ℝ).Nontrivial →
        rho c ≤ (S : Set ℝ).infsep / 4) :
    (↑S : Set ℝ).PairwiseDisjoint
      (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by
  classical
  rw [Set.PairwiseDisjoint]
  intro c hc d hd hne
  change Disjoint (Set.Ioo (c - rho c) (c + rho c))
    (Set.Ioo (d - rho d) (d + rho d))
  rw [Set.disjoint_left]
  intro x hxC hxD
  have hnontrivial : (S : Set ℝ).Nontrivial := ⟨c, hc, d, hd, hne⟩
  have hinf_pos : 0 < (S : Set ℝ).infsep := by
    exact (Finset.infsep_pos_iff_nontrivial S).2 hnontrivial
  have hcd_inf : (S : Set ℝ).infsep ≤ dist c d :=
    Set.infsep_le_dist_of_mem hc hd hne
  have hρc : rho c ≤ (S : Set ℝ).infsep / 4 := hrho_le c hc hnontrivial
  have hρd : rho d ≤ (S : Set ℝ).infsep / 4 := hrho_le d hd hnontrivial
  have hsumρ : rho c + rho d ≤ (S : Set ℝ).infsep / 2 := by
    linarith
  rcases le_total c d with hcd | hdc
  · have hcd_lt : c < d := lt_of_le_of_ne hcd hne
    have hdist_eq : dist c d = d - c := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hcd)]
      ring
    have hgap_lt : d - c < rho c + rho d := by
      linarith [hxC.2, hxD.1]
    have hgap_ge : (S : Set ℝ).infsep ≤ d - c := by
      simpa [hdist_eq] using hcd_inf
    linarith
  · have hdc_lt : d < c := lt_of_le_of_ne hdc hne.symm
    have hdist_eq : dist c d = c - d := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hdc)]
    have hgap_lt : c - d < rho c + rho d := by
      linarith [hxD.2, hxC.1]
    have hgap_ge : (S : Set ℝ).infsep ≤ c - d := by
      simpa [hdist_eq] using hcd_inf
    linarith

/-- Finite bad points can be assigned local radii which simultaneously make
the total `α` increment small and make the bad-point intervals pairwise
disjoint. -/
lemma finite_sum_alpha_local_increment_small_pairwise
    {α : ℝ → ℝ}
    (S : Finset ℝ)
    (hα_mono : Monotone α)
    (hα : ∀ c : ℝ, c ∈ S → ContinuousAt α c)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ → ℝ,
      (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
      (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps ∧
      (↑S : Set ℝ).PairwiseDisjoint
        (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by
  classical
  rcases finite_sum_alpha_local_increment_small S hα heps with
    ⟨rho0, hrho0_pos, hsum0_lt⟩
  let cap : ℝ :=
    if (S : Set ℝ).Nontrivial then (S : Set ℝ).infsep / 4 else 1
  have hcap_pos :
      0 < cap := by
    dsimp [cap]
    by_cases hnontrivial : (S : Set ℝ).Nontrivial
    · rw [if_pos hnontrivial]
      have hinf_pos : 0 < (S : Set ℝ).infsep := by
        exact (Finset.infsep_pos_iff_nontrivial S).2 hnontrivial
      linarith
    · rw [if_neg hnontrivial]
      norm_num
  let rho : ℝ → ℝ := fun c =>
    if c ∈ S then min (rho0 c) cap else 1
  refine ⟨rho, ?_, ?_, ?_⟩
  · intro c hc
    dsimp [rho]
    rw [if_pos hc]
    exact lt_min (hrho0_pos c hc) hcap_pos
  · have hterm_le :
        ∀ c : ℝ, c ∈ S →
          α (c + rho c) - α (c - rho c) ≤
            α (c + rho0 c) - α (c - rho0 c) := by
      intro c hc
      dsimp [rho]
      rw [if_pos hc]
      exact alpha_local_increment_mono_of_radius_le hα_mono
        (min_le_left (rho0 c) cap)
    have hsum_le :
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) ≤
          ∑ c ∈ S, (α (c + rho0 c) - α (c - rho0 c)) := by
      refine Finset.sum_le_sum ?_
      intro c hc
      exact hterm_le c hc
    exact lt_of_le_of_lt hsum_le hsum0_lt
  · refine pairwiseDisjoint_Ioo_of_radii_le_infsep_div_four S rho ?_
    intro c hc hnontrivial
    dsimp [rho]
    rw [if_pos hc]
    dsimp [cap]
    rw [if_pos hnontrivial]
    exact min_le_right (rho0 c) ((S : Set ℝ).infsep / 4)

/-- The task hypotheses on finitely many discontinuities provide a concrete
bad-point Finset and local `α` radii with arbitrarily small total increment. -/
lemma finite_discontinuity_alpha_local_increment_data
    {f α : ℝ → ℝ} {a b eps : ℝ}
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont :
      ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x)
    (heps : 0 < eps) :
    ∃ S : Finset ℝ,
      (∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b) ∧
      ∃ rho : ℝ → ℝ,
        (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps := by
  rcases hDiscFinite.exists_finset with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  exact finite_sum_alpha_local_increment_small S
    (fun c hc => hαCont ((hS c).1 hc)) heps

/-- The task hypotheses provide a concrete bad-point Finset and local `α`
radii which satisfy the small-increment quota and are pairwise disjoint. -/
lemma finite_discontinuity_alpha_local_increment_pairwise_data
    {f α : ℝ → ℝ} {a b eps : ℝ}
    (hα_mono : Monotone α)
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont :
      ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x)
    (heps : 0 < eps) :
    ∃ S : Finset ℝ,
      (∀ x : ℝ, x ∈ S ↔ x ∈ discontinuitySetOn f a b) ∧
      ∃ rho : ℝ → ℝ,
        (∀ c : ℝ, c ∈ S → 0 < rho c) ∧
        (∑ c ∈ S, (α (c + rho c) - α (c - rho c))) < eps ∧
        (↑S : Set ℝ).PairwiseDisjoint
          (fun c : ℝ => Set.Ioo (c - rho c) (c + rho c)) := by
  rcases hDiscFinite.exists_finset with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  exact finite_sum_alpha_local_increment_small_pairwise S hα_mono
    (fun c hc => hαCont ((hS c).1 hc)) heps


end Thm11SourceRoute
