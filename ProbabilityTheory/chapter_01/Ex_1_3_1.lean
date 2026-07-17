import ProbabilityTheory.chapter_01.thm_1_2_4

open Set
open scoped BigOperators


/-- Step integrator with one jump at `c`.

It is equal to `u₁` to the left of `c`, and equal to `u₂` at and to the
right of `c`.
-/
noncomputable def jumpStep (c u₁ u₂ : ℝ) : ℝ → ℝ :=
  fun x => if x < c then u₁ else u₂

private theorem jumpStep_monotone {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) :
    Monotone (jumpStep c u₁ u₂) := by
  intro x y hxy
  by_cases hy : y < c
  · have hx : x < c := lt_of_le_of_lt hxy hy
    simp [jumpStep, hx, hy]
  · by_cases hx : x < c
    · simp [jumpStep, hx, hy, hu]
    · simp [jumpStep, hx, hy]

private lemma partition_length_le_mesh {a b : ℝ} (P : Partition a b)
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

private lemma jumpStep_increment_nonneg {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂)
    {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ jumpStep c u₁ u₂ y - jumpStep c u₁ u₂ x :=
  sub_nonneg.mpr (jumpStep_monotone hu hxy)

private lemma jumpStep_increment_ne_zero_crosses {x y c u₁ u₂ : ℝ}
    (hxy : x ≤ y)
    (hne : jumpStep c u₁ u₂ y - jumpStep c u₁ u₂ x ≠ 0) :
    x < c ∧ c ≤ y := by
  by_cases hx : x < c
  · by_cases hy : y < c
    · simp [jumpStep, hx, hy] at hne
    · exact ⟨hx, le_of_not_gt hy⟩
  · have hy : ¬ y < c := not_lt.mpr ((le_of_not_gt hx).trans hxy)
    simp [jumpStep, hx, hy] at hne

private lemma jumpStep_partition_increment_sum {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (hac : a < c) (hcb : c ≤ b) :
    ∑ i : Fin P.n,
      (jumpStep c u₁ u₂ (P.pts i.succ) -
        jumpStep c u₁ u₂ (P.pts i.castSucc)) = u₂ - u₁ := by
  have hsum := sum_adjacent_sub
    (fun i : Fin (P.n + 1) => jumpStep c u₁ u₂ (P.pts i))
  have h0 : P.pts 0 < c := by simpa [P.pts_start] using hac
  have hn : ¬ P.pts (Fin.last P.n) < c := by
    have : c ≤ P.pts (Fin.last P.n) := by simpa [P.pts_end] using hcb
    exact not_lt.mpr this
  simpa [jumpStep, h0, hn] using hsum

private lemma jumpStep_taggedSum_sub_value {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ) (f : ℝ → ℝ)
    (hac : a < c) (hcb : c ≤ b) :
    taggedSum P tags f (jumpStep c u₁ u₂) - f c * (u₂ - u₁) =
      ∑ i : Fin P.n,
        ((f (tags i) - f c) *
          (jumpStep c u₁ u₂ (P.pts i.succ) -
            jumpStep c u₁ u₂ (P.pts i.castSucc))) := by
  have hsum := jumpStep_partition_increment_sum
    (P := P) (c := c) (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)
  unfold taggedSum
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

private lemma crossing_tag_abs_sub_le_mesh {a b c : ℝ} {P : Partition a b}
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



theorem taggedCommonLimit_jumpStep_of_continuousAt
    {f : ℝ → ℝ} {c u₁ u₂ a b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hu : u₁ ≤ u₂)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hfcont : ContinuousAt f c) :
    TaggedCommonLimit a b f (jumpStep c u₁ u₂)
      (f c * (u₂ - u₁)) := by
  rcases hu.eq_or_lt with rfl | hu
  · refine ⟨⟨hac.trans hcb, hAbove, hBelow, ?_⟩, ?_⟩
    · exact (jumpStep_monotone (c := c) le_rfl).monotoneOn (Icc a b)
    · intro eps heps
      refine ⟨1, zero_lt_one, ?_⟩
      intro P tags _htags _hmesh
      simp [taggedSum, jumpStep, heps]
  · refine ⟨⟨hac.trans hcb, hAbove, hBelow, ?_⟩, ?_⟩
    · exact (jumpStep_monotone (c := c) hu.le).monotoneOn (Icc a b)
    · intro eps heps
      let jump : ℝ := u₂ - u₁
      let eta : ℝ := eps / (jump + 1)
      have hden_pos : 0 < jump + 1 := by
        dsimp [jump]
        positivity
      have heta_pos : 0 < eta := div_pos heps hden_pos
      rcases (Metric.continuousAt_iff.mp hfcont) eta heta_pos with ⟨δ, hδ, Hδ⟩
      refine ⟨δ, hδ, ?_⟩
      intro P tags htags hmesh
      rw [jumpStep_taggedSum_sub_value (P := P) (tags := tags) (f := f)
        (hac := hac) (hcb := hcb.le)]
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin P.n)),
          |(f (tags i) - f c) *
            (jumpStep c u₁ u₂ (P.pts i.succ) -
              jumpStep c u₁ u₂ (P.pts i.castSucc))| ≤
            eta * (jumpStep c u₁ u₂ (P.pts i.succ) -
              jumpStep c u₁ u₂ (P.pts i.castSucc)) := by
        intro i _hi
        let inc : ℝ := jumpStep c u₁ u₂ (P.pts i.succ) -
          jumpStep c u₁ u₂ (P.pts i.castSucc)
        have hmono_pts : P.pts i.castSucc ≤ P.pts i.succ :=
          le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
        have hinc_nonneg : 0 ≤ inc := by
          dsimp [inc]
          exact jumpStep_increment_nonneg hu.le hmono_pts
        by_cases hinc_zero : inc = 0
        · simp [inc, hinc_zero]
        · have hcross := jumpStep_increment_ne_zero_crosses hmono_pts
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
              (jumpStep c u₁ u₂ (P.pts i.succ) -
                jumpStep c u₁ u₂ (P.pts i.castSucc)))|
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
                |((f (tags i) - f c) *
                  (jumpStep c u₁ u₂ (P.pts i.succ) -
                    jumpStep c u₁ u₂ (P.pts i.castSucc)))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin P.n)),
                eta * (jumpStep c u₁ u₂ (P.pts i.succ) -
                  jumpStep c u₁ u₂ (P.pts i.castSucc)) := Finset.sum_le_sum hterm
        _ = eta * jump := by
          rw [← Finset.mul_sum]
          dsimp [jump]
          rw [jumpStep_partition_increment_sum (P := P) (c := c)
            (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb.le)]
        _ < eps := by
          dsimp [eta, jump]
          have hlt_ratio : (u₂ - u₁) / ((u₂ - u₁) + 1) < 1 := by
            have hden : 0 < (u₂ - u₁) + 1 := by positivity
            rw [div_lt_one hden]
            linarith [hu]
          have hmul := mul_lt_mul_of_pos_left hlt_ratio heps
          field_simp [show (u₂ - u₁) + 1 ≠ 0 by positivity] at hmul ⊢
          nlinarith


/--
The Riemann--Stieltjes integral with respect to a one-jump step integrator.

If

* `a < c < b`,
* `α x = u₁` for `x < c`,
* `α x = u₂` for `x ≥ c`,
* `u₁ ≤ u₂`,
* `f` is continuous at `c`,

then

`∫_[a,b] f dα = f(c) * (u₂ - u₁)`.

The proof uses tagged-sum uniqueness.  The hard analytic content is contained in
`taggedCommonLimit_jumpStep_of_continuousAt`, which proves directly that every
tagged Riemann--Stieltjes sum converges to `f c * (u₂ - u₁)`.
-/
theorem rsIntegral_jumpStep_eq {f : ℝ → ℝ} {c u₁ u₂ a b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hu : u₁ ≤ u₂)
    (hfcont : ContinuousAt f c)
    (h : RSIntegrable f (jumpStep c u₁ u₂) a b) :
    rsIntegral f (jumpStep c u₁ u₂) a b h =
      f c * (u₂ - u₁) := by
  have hs := (rsIntegral_spec h).1
  exact taggedCommonLimit_unique
    (rsIntegral_spec h)
    (taggedCommonLimit_jumpStep_of_continuousAt
      (f := f) (c := c) (u₁ := u₁) (u₂ := u₂)
      hac hcb hu hs.2.1 hs.2.2.1 hfcont)
