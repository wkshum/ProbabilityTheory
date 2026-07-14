import ProbabilityTheory.chapter_01.def_1_2


/-

 Theorem 1.2, parts 1, 2, and 3.



 Using the machinary developed in this file, we also prove a fundamental
 result:

 Any lower sum L(P,f,α) is bounded above by any upper sum U(P', f,α)
 on the same interval

 by considering the common refinement of partition P and P'. This fact
 will be usedin part 4 of Theorem 1.2.

-/

open scoped BigOperators Pointwise

open Finset Set


noncomputable section Thm_1_2

namespace DarbouxRS

/-
 Some helper lemmas
-/


/-
 If i ≤ j, the the i-th point in a partition is less than
 the j-th point.

 We call a function from Mathlib directly to prove this lemma.
-/
lemma partition_pts_monotone_core {a b : ℝ} (P : Partition a b)
    {i j : Fin (P.n + 1)} (hij : i ≤ j) :
  P.pts i ≤ P.pts j := by
  exact P.strict_mono.monotone hij

/--
Every point in a partition `P` of `[a, b]` lies within the closed interval `[a, b]`.

This lemma uses the monotonicity of the partition points to demonstrate that
`a = P.pts 0 ≤ P.pts i ≤ P.pts (last) = b` for any valid index `i`.
-/
lemma partition_pts_mem_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin (P.n + 1)} :
    P.pts i ∈ Set.Icc a b := by
  constructor
  · calc
      a = P.pts 0 := P.pts_start.symm
      _ ≤ P.pts i := partition_pts_monotone_core P (Fin.zero_le i)
  · calc
      P.pts i ≤ P.pts (Fin.last P.n) := partition_pts_monotone_core P (Fin.le_last i)
      _ = b := P.pts_end


/--
Every subinterval `[x_i, x_{i+1}]` of a partition `P` of `[a, b]` is a subset of
the entire interval `[a, b]`.

This lemma proves that if a point `x` belongs to the `i`-th subinterval, it naturally
inherits the global bounds `a ≤ x ≤ b` from the partition's endpoints.
-/
lemma subinterval_subset_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin P.n} :
    Partition.subinterval P i ⊆ Set.Icc a b := by
  intro x hx
  constructor
  · -- a ≤ P.pts i.castSucc ≤ x
    exact le_trans (partition_pts_mem_Icc_core P).1 hx.1
  · -- x ≤ P.pts i.succ ≤ b
    exact le_trans hx.2 (partition_pts_mem_Icc_core P).2



theorem taggedSum_integrand_add {a b : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (f g alpha : ℝ → ℝ) :
  taggedSum P tags (fun x => f x + g x) alpha =
      taggedSum P tags f alpha + taggedSum P tags g alpha := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem sourceHypotheses_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    (hf : SourceHypotheses a b f alpha)
    (hg : SourceHypotheses a b g alpha) :
    SourceHypotheses a b (fun x => f x + g x) alpha := by
  rcases hf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hg with ⟨_habg, hgAbove, hgBelow, _hmonog⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · refine BddAbove.mono ?_ (hfAbove.add hgAbove)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩
  · refine BddBelow.mono ?_ (hfBelow.add hgBelow)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩


theorem taggedCommonLimit_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg) :
    TaggedCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P tags htags hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg
  have hadd :
      taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg) =
        (taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg) := by
    rw [taggedSum_integrand_add]
    ring
  calc
    |taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg)| =
        |(taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f alpha - Lf| +
        |taggedSum P tags g alpha - Lg| := abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f alpha - Lf| +
            |taggedSum P tags g alpha - Lg| < eps / 2 + eps / 2 :=
        add_lt_add hPf hPg
      simpa using hlt


/--
The supremum of the sum of two functions on a partition subinterval is less than or
equal to the sum of their individual supremums on that subinterval.

Mathematically, this states that for the `i`-th subinterval `I_i = [x_i, x_{i+1}]`:
`sup { f(x) + g(x) | x ∈ I_i } ≤ sup { f(x) | x ∈ I_i } + sup { g(x) | x ∈ I_i }`

This is a core foundational lemma for proving the subadditivity of
upper Riemann-Stieltjes sums.

The hypotheses `hfAbove` and `hgAbove` ensure that the functions are bounded above
on the entire interval `[a, b]`, which guarantees the supremums are mathematically
well-defined real numbers.
-/
lemma upperStep_integrand_add_le_core {a b : ℝ}
    {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    (hgAbove : BddAbove (g '' Set.Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfAbove

  have hgCellAbove : BddAbove (g '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgAbove

  unfold upperStep
  refine csSup_le hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : f x ≤ sSup (f '' Partition.subinterval P i) :=
    le_csSup hfCellAbove ⟨x, hx, rfl⟩

  have hgx : g x ≤ sSup (g '' Partition.subinterval P i) :=
    le_csSup hgCellAbove ⟨x, hx, rfl⟩

  linarith



/--
The sum of the infimums of two functions on a partition subinterval is less than or
equal to the infimum of their sum on that subinterval.

Mathematically, this states that for the `i`-th subinterval `I_i = [x_i, x_{i+1}]`:
`inf { f(x) | x ∈ I_i } + inf { g(x) | x ∈ I_i } ≤ inf { f(x) + g(x) | x ∈ I_i }`

This is a core foundational lemma for proving the superadditivity of lower Riemann-Stieltjes sums.
The hypotheses `hfBelow` and `hgBelow` ensure that the functions are bounded below on the
entire interval `[a, b]`, which guarantees the infimums are mathematically well-defined real numbers.
-/
lemma lowerStep_integrand_add_le_core {a b : ℝ} {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    (hgBelow : BddBelow (g '' Set.Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfBelow

  have hgCellBelow : BddBelow (g '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgBelow

  unfold lowerStep
  refine le_csInf hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : sInf (f '' Partition.subinterval P i) ≤ f x :=
    csInf_le hfCellBelow ⟨x, hx, rfl⟩

  have hgx : sInf (g '' Partition.subinterval P i) ≤ g x :=
    csInf_le hgCellBelow ⟨x, hx, rfl⟩

  linarith



/-
  Image of a constant c times a function f is the same as first taking
  the image of f, and then multiply all numbers in the image set by c.
-/
lemma image_const_mul_Icc_eq_smul_core {a b c : ℝ} (f : ℝ → ℝ) :
    (fun x => c * f x) '' Icc a b = c • (f '' Icc a b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩


/-
  If f satisfies the basic assumptions of integrand in the textbook,
  i.e., f is bounded from above and below,
  then c f also satisfies the assumptions.
-/
theorem sourceHypotheses_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    (h : SourceHypotheses a b f alpha) :
    SourceHypotheses a b (fun x => c * f x) alpha := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hAbove.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddBelow.smul_of_nonpos hc' hBelow
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hBelow.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddAbove.smul_of_nonpos hc' hAbove


/--
The integrator function `alpha` does not decrease across any subinterval of the partition.

Because `alpha` is assumed to be monotonic on `[a, b]` (via `SourceHypotheses`), and the
partition points strictly increase (`x_i < x_{i+1}`), the difference `alpha(x_{i+1}) - alpha(x_i)`
is always non-negative. This guarantees that the width/weights in the Riemann-Stieltjes sum
are non-negative.
-/
lemma partition_increment_nonneg_of_source_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
  -- Unpack the SourceHypotheses to get the monotonicity of alpha
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩

  -- The endpoints of the subinterval are in [a, b]
  have hleft : P.pts i.castSucc ∈ Set.Icc a b := partition_pts_mem_Icc_core P
  have hright : P.pts i.succ ∈ Set.Icc a b := partition_pts_mem_Icc_core P

  -- Because x_i < x_{i+1}, monotonicity implies alpha(x_i) ≤ alpha(x_{i+1})
  have h_pts_lt : P.pts i.castSucc < P.pts i.succ :=
    P.strict_mono (Fin.castSucc_lt_succ)

  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt h_pts_lt))



/--
The upper Riemann-Stieltjes sum of the sum of two functions is subadditive:
`U(P, f + g, α) ≤ U(P, f, α) + U(P, g, α)`
-/
theorem upperSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by
  rcases hsf with ⟨_hab, hfAbove, _hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, hgAbove, _hgBelow, _hmonog⟩
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- `i` is explicitly passed
  have hstep := upperStep_integrand_add_le_core P i hfAbove hgAbove

  -- Reconstruct the SourceHypotheses on the fly using the pieces in your context!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P ⟨_hab, hfAbove, _hfBelow, _hmono⟩

  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith


theorem lowerSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  -- For lower sums, we need the `BddBelow` pieces!
  rcases hsf with ⟨_hab, _hfAbove, hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, _hgAbove, hgBelow, _hmonog⟩
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- Apply the lowerStep lemma we fixed earlier
  have hstep := lowerStep_integrand_add_le_core P i hfBelow hgBelow

  -- Reconstruct the SourceHypotheses for the increment proof
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨_hab, _hfAbove, hfBelow, _hmono⟩

  -- Multiply the step inequality by the non-negative increment width
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

/--
For any subinterval in a partition, the infimum of a function is less than
or equal to its supremum.

Mathematically: `m_i ≤ M_i`.
This relies on the fact that the subinterval is non-empty (it contains at least
its left endpoint), and that the function is bounded both below and above.
-/
lemma lowerStep_le_upperStep_core {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Set.Icc a b))
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  have hcell_nonempty : (f '' Partition.subinterval P i).Nonempty := by
    -- We show the image is non-empty by plugging in the left endpoint
    refine ⟨f (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow

  have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove

  rcases hcell_nonempty with ⟨y, hy⟩
  unfold lowerStep upperStep

  -- inf(f) ≤ y and y ≤ sup(f), therefore inf(f) ≤ sup(f)
  exact le_trans (csInf_le hcellBelow hy) (le_csSup hcellAbove hy)


/--
For any partition, the lower Riemann-Stieltjes sum is always less than
or equal to the upper Riemann-Stieltjes sum.
-/
theorem lowerSum_le_upperSum_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by
  -- Keep a copy of `hs` so we can extract bounds without destroying the original
  have hs_copy := hs
  rcases hs_copy with ⟨_hab, hAbove, hBelow, _hmono⟩

  unfold lowerSum upperSum
  refine Finset.sum_le_sum ?_
  intro i _hi  -- _hi is `i ∈ Finset.univ`, which we ignore

  -- 1. Prove the step inequality: m_i ≤ M_i
  have hstep := lowerStep_le_upperStep_core P i hBelow hAbove

  -- 2. Prove the increment is non-negative: 0 ≤ Δα_i
  -- We can just pass the intact `hs` directly!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 3. Multiply them together: m_i * Δα_i ≤ M_i * Δα_i
  exact mul_le_mul_of_nonneg_right hstep hinc


/--
Additivity of the Riemann-Stieltjes integral with respect to the integrand.

If both `f` and `g` are Riemann-Stieltjes integrable with respect to `alpha`
(having upper/lower limits `Lf` and `Lg` respectively), then their sum `f + g`
is also integrable, and its limit is `Lf + Lg`.

Proof Idea:
This proof is a classic textbook `ε/2` argument, combined with the subadditivity
and superadditivity of partition sums:

1. *Common Refinement:* For a given `eps > 0`, we find `δf` and `δg` corresponding
   to `eps / 2` for `f` and `g`. We require the partition mesh to be less than
   `min(δf, δg)` so both conditions hold simultaneously.

2. *Algebraic Bounds:* We utilize the previously proven subadditivity of upper sums
   (`U(f+g) ≤ U(f) + U(g)`) and superadditivity of lower sums (`L(f) + L(g) ≤ L(f+g)`).

3. *Squeeze:* Because `U(f)` and `L(f)` are tightly squeezed around `Lf` (and similarly
   for `g` around `Lg`), the algebraic bounds force `U(f+g)` and `L(f+g)` to be strictly
   squeezed within an `eps` radius of `Lf + Lg`. The tactic `linarith` handles the
   heavy lifting of unfolding the absolute values and chaining the inequalities.
-/
theorem upperLowerCommonLimit_integrand_add_core {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P hmeshf
  have hPg := Hg P hmeshg
  have hsumUpper :
      upperSum P (fun x => f x + g x) alpha ≤
        upperSum P f alpha + upperSum P g alpha :=
    upperSum_integrand_add_le_core P hsf hsg
  have hsumLower :
      lowerSum P f alpha + lowerSum P g alpha ≤
        lowerSum P (fun x => f x + g x) alpha :=
    lowerSum_integrand_add_le_core P hsf hsg
  have hlowerUpper :
      lowerSum P (fun x => f x + g x) alpha ≤
        upperSum P (fun x => f x + g x) alpha :=
    lowerSum_le_upperSum_core P (sourceHypotheses_integrand_add hsf hsg)
  constructor
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt



lemma abs_const_mul_error_lt_core {c old L eps : ℝ}
    (heps : 0 < eps) (hold : |old - L| < eps / (|c| + 1)) :
    |c * (old - L)| < eps := by
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rw [abs_mul]
  have hmul₁ : |c| * |old - L| ≤ |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt (by simpa [C] using hold)) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)


/--
Multiplying a function by a constant `c` scales its image on any subinterval by `c`.

Mathematically, this states that `{ c * f(x) | x ∈ I_i } = c • { f(x) | x ∈ I_i }`.
This is a key algebraic step for proving that `U(P, c * f, α) = c * U(P, f, α)`.
-/
lemma image_const_mul_subinterval_eq_smul_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) :
    (fun x => c * f x) '' Partition.subinterval P i = c • (f '' Partition.subinterval P i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

/--
Multiplying a function by a non-negative constant `c` scales its supremum
on any partition subinterval by `c`.

Mathematically: `sup { c * f(x) | x ∈ I_i } = c * sup { f(x) | x ∈ I_i }` for `c ≥ 0`.
This relies on the fact that scaling by a non-negative number preserves the ordering
of the real numbers.
-/
lemma upperStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    upperStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sSup_smul_of_nonneg` proves sup(c • S) = c • sup(S) when c ≥ 0
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonneg hc (f '' Partition.subinterval P i)


/--
The upper Riemann-Stieltjes sum scales linearly with respect to multiplication
by a non-negative constant.

Mathematically: `U(P, c * f, α) = c * U(P, f, α)` when `c ≥ 0`.

The requirement that `c` is non-negative is crucial. If `c` were negative,
multiplying the function by `c` would flip the ordering of the reals. The supremum
of `c * f` would then be determined by the *infimum* of `f`, which would transform
the upper sum into a scaled lower sum instead.
-/
theorem upperSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    upperSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonneg_core P f i hc]
  ring


/--
Multiplying a function by a non-negative constant `c` scales its infimum
on any partition subinterval by `c`.

Mathematically: `inf { c * f(x) | x ∈ I_i } = c * inf { f(x) | x ∈ I_i }` for `c ≥ 0`.
This relies on the fact that scaling by a non-negative number preserves the ordering
of the real numbers.
-/
lemma lowerStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    lowerStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sInf_smul_of_nonneg` proves inf(c • S) = c • inf(S) when c ≥ 0
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonneg hc (f '' Partition.subinterval P i)

/--
The lower Riemann-Stieltjes sum scales linearly with respect to multiplication
by a non-negative constant.

Mathematically: `L(P, c * f, α) = c * L(P, f, α)` when `c ≥ 0`.

The requirement that `c` is non-negative is crucial. If `c` were negative,
multiplying the function by `c` would flip the ordering of the reals. The infimum
of `c * f` would then be determined by the *supremum* of `f`, transforming
the lower sum into a scaled upper sum.
-/
theorem lowerSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    lowerSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonneg_core P f i hc]
  ring

/--
Multiplying a function by a non-positive constant `c` transforms its scaled infimum
into a supremum on any partition subinterval.

Mathematically: `sup { c * f(x) | x ∈ I_i } = c * inf { f(x) | x ∈ I_i }` for `c ≤ 0`.
This occurs because multiplying by a negative number reverses the ordering of the reals,
turning the lowest points into the highest points.
-/
lemma upperStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    upperStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold upperStep lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sSup_smul_of_nonpos` proves sup(c • S) = c • inf(S) when c ≤ 0
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonpos hc (f '' Partition.subinterval P i)

theorem upperSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    upperSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold upperSum lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonpos_core P f i hc]
  ring

/--
Multiplying a function by a non-positive constant `c` transforms its scaled supremum
into an infimum on any partition subinterval.

Mathematically: `inf { c * f(x) | x ∈ I_i } = c * sup { f(x) | x ∈ I_i }` for `c ≤ 0`.
Because multiplying by a non-positive number reverses the ordering of the reals,
the highest points of `f` become the lowest points of `c * f`.
-/
lemma lowerStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    lowerStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold lowerStep upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sInf_smul_of_nonpos` proves inf(c • S) = c • sup(S) when c ≤ 0
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonpos hc (f '' Partition.subinterval P i)


/--
The lower Riemann-Stieltjes sum of a function multiplied by a non-positive constant
`c` is equal to `c` times the *upper* sum of the original function.

Mathematically: `L(P, c * f, α) = c * U(P, f, α)` when `c ≤ 0`.

Since `c ≤ 0`, the infimum of the scaled function is determined by the supremum
of the original function, thereby transforming the lower sum into a scaled upper sum.
-/
theorem lowerSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    lowerSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold lowerSum upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonpos_core P f i hc]
  ring


/--
Linearity of the Riemann-Stieltjes integral with respect to scalar multiplication.

If a function `f` is Riemann-Stieltjes integrable with respect to `alpha`
(with limit `L`), then `c * f` is also integrable, and its limit is `c * L`.

Proof Idea:
This proof relies on bounding the scaled error by choosing a sufficiently small `eps`.

1. *Scaling Factor `C`:* We define an artificial bounding constant `C = |c| + 1`.
   The `+ 1` is a standard analytic trick to ensure `C > 0` even when `c = 0`,
   preventing division-by-zero errors when we request an initial error of `eps / C`.

2. *Case Split on `c`:* The proof branches depending on whether `c` is non-negative
   or negative:

   - *Case `0 ≤ c`:* Scalar multiplication preserves the order of bounds.
     The error `|U(c*f) - c*L|` cleanly factors into `|c| * |U(f) - L|`, which is
     strictly less than `|c| * (eps / C) < eps`. The lower sum behaves identically.

   - *Case `c < 0`:* Scalar multiplication flips the supremum and infimum.
     Therefore, the upper sum error `|U(c*f) - c*L|` factors into `|c| * |L(f) - L|`
     (using the lower sum of `f`). Because both the upper and lower sums of `f`
     converge to `L`, the error is still bounded by `eps`.
-/
theorem upperLowerCommonLimit_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    UpperLowerCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  by_cases hc : 0 ≤ c
  · constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [upperSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [upperSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)

/--
The tagged Riemann-Stieltjes sum scales linearly with respect to multiplication
by a constant.

Mathematically: `S(P, tags, c * f, α) = c * S(P, tags, f, α)`.

Unlike upper and lower sums, tagged sums evaluate the function at specific points
rather than taking supremums or infimums. Because of this, pulling a constant `c`
out of the sum is purely distributive algebra, and holds for *any* real number `c`
(no `c ≥ 0` or `c ≤ 0` cases are required).
-/
theorem taggedSum_const_mul_core {a b c : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) :
    taggedSum P tags (fun x => c * f x) alpha = c * taggedSum P tags f alpha := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring


/--
Linearity of the tagged Riemann-Stieltjes limit with respect to scalar multiplication.

If the tagged sums of `f` converge to `L`, then the tagged sums of `c * f`
converge to `c * L`.

*Proof Idea:*
This is the tagged-sum equivalent of `upperLowerCommonLimit_const_mul_core`.
However, because tagged sums evaluate the function at specific points rather than
taking supremums or infimums, the proof is actually much simpler! We do not need
to split into `c ≥ 0` and `c < 0` cases.

The proof uses a standard epsilon-delta scaling argument:

1. *Safety Constant:* We define `C = |c| + 1 > 0` to prevent division-by-zero
   when `c = 0`.

2. *Tolerance Scaling:* We ask the original limit `h` for a `δ` that guarantees
   the error of `f`'s sum is strictly less than `eps / C`.

3. *Algebraic Factoring:* Using `taggedSum_const_mul_core`, we factor `c` out
   of the sum algebraically, transforming the target error into
   `|c| * |taggedSum(f) - L|`.

4. *Squeeze:* Because `|taggedSum(f) - L| < eps / C`, the total error is bounded
   by `|c| * (eps / C)`. Since `|c| < |c| + 1 = C`, this strictly bounds the total
   error below `C * (eps / C) = eps`, completing the proof.
-/
theorem taggedCommonLimit_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f alpha L) :
    TaggedCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  have hEq :
      taggedSum P tags (fun x => c * f x) alpha - c * L =
        c * (taggedSum P tags f alpha - L) := by
    rw [taggedSum_const_mul_core]
    ring
  rw [hEq, abs_mul]
  have hmul₁ : |c| * |taggedSum P tags f alpha - L| ≤
      |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt hP) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)


/--
If tags are chosen within their respective partition subintervals,
then every tag natively belongs to the overall interval `[a, b]`.

This acts as a bridge between local bounds (the tag is in `[x_i, x_{i+1}]`)
and global bounds (the tag is in `[a, b]`).
-/
lemma tag_mem_Icc_of_tagsInPartition_core {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags)
    (i : Fin P.n) :
    tags i ∈ Set.Icc a b :=
  -- `htags i` proves the tag is in the subinterval.
  -- `subinterval_subset_Icc_core` applies the subset property.
  subinterval_subset_Icc_core P (htags i)


/--
Monotonicity of the tagged Riemann-Stieltjes sum.

If `f(x) ≤ g(x)` everywhere on the interval `[a, b]`, then for any partition
and any valid choice of tags, the tagged sum of `f` is less than or equal to
the tagged sum of `g`.

Mathematically: `S(P, tags, f, α) ≤ S(P, tags, g, α)`.
This relies on the integrator `α` being monotonically increasing, ensuring that
the width/weight `Δα_i` is non-negative, preserving the inequality `f(t_i) ≤ g(t_i)`.
-/
theorem taggedSum_mono_core {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha := by
  unfold taggedSum
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- 1. Prove the tag is inside [a, b]
  have htag : tags i ∈ Set.Icc a b := tag_mem_Icc_of_tagsInPartition_core P htags i

  -- 2. Evaluate the function inequality at the tag
  have hstep : f (tags i) ≤ g (tags i) := hfg (tags i) htag

  -- 3. The increment is non-negative (pass `hs` directly!)
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 4. Multiply the step inequality by the non-negative increment
  exact mul_le_mul_of_nonneg_right hstep hinc


/--
Monotonicity of the Riemann-Stieltjes limit.

If `f(x) ≤ g(x)` everywhere on the interval `[a, b]`, and both functions are
integrable with respect to `alpha`, then the integral limit of `f` is less than
or equal to the integral limit of `g` (`Lf ≤ Lg`).

**Proof Idea:**
This proof relies on the algebraic fact that `A ≤ B` is equivalent to proving
that `A < B + eps` for any `eps > 0`.
By picking a partition `P` whose mesh is small enough to simultaneously satisfy
the limit convergence for both `f` and `g`, we can bound `Lf` close to `S(P, f)`,
and `Lg` close to `S(P, g)`. Since the sum of `f` is strictly bounded by the
sum of `g` (proven in `taggedSum_mono_core`), `linarith` easily squeezes the
limits to prove `Lf ≤ Lg`.
-/
theorem taggedCommonLimit_mono_core {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    Lf ≤ Lg := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨_hsg, hlimg⟩

  -- Create a copy of `hsf` so we can extract `hab` without destroying `hsf`
  have hsf_copy := hsf
  rcases hsf_copy with ⟨hab, _hAbove, _hBelow, _hmono⟩

  rw [le_iff_forall_pos_lt_add]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  rcases exists_partition_mesh_lt hab (lt_min hδf hδg) with ⟨P, hPmesh⟩

  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- We already proved this earlier!
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmeshf : P.mesh < δf := lt_of_lt_of_le hPmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hPmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg

  -- Pass `hsf` cleanly without rebuilding it!
  have hsum : taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
    taggedSum_mono_core P tags hsf htags hfg

  have hf_bound : Lf < taggedSum P tags f alpha + eps / 2 := by
    have hleft := (abs_lt.mp hPf).1
    linarith
  have hg_bound : taggedSum P tags g alpha < Lg + eps / 2 := by
    have hright := (abs_lt.mp hPg).2
    linarith
  linarith


/--
For a tag chosen inside the `i`-th subinterval, the lower step is bounded above
by the tagged value.

Mathematically:

`inf { f x | x ∈ [xᵢ, xᵢ₊₁] } ≤ f(tᵢ)`

provided `tᵢ ∈ [xᵢ, xᵢ₊₁]`.
-/
lemma lowerStep_le_tag {a b : ℝ} {f : ℝ → ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    {x : ℝ} (hx : x ∈ Partition.subinterval P i) :
    lowerStep P f i ≤ f x := by
  have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono
      (Set.image_mono (subinterval_subset_Icc_core P))
      hfBelow
  unfold lowerStep
  exact csInf_le hcellBelow ⟨x, hx, rfl⟩


/-
  ### Connection between lower sum, upper sum and tagged sum
-/

/--
For a fixed partition, every lower Riemann--Stieltjes sum is bounded above by
every tagged Riemann--Stieltjes sum whose tags are chosen in the corresponding
subintervals.

This is the finite-sum comparison

`L(P,f,α) ≤ S(P,tags,f,α)`.

The proof is pointwise on each subinterval:

* `lowerStep P f i ≤ f (tags i)`;
* `α(xᵢ₊₁) - α(xᵢ) ≥ 0`;
* hence the corresponding products are ordered;
* summing preserves the inequality.
-/
lemma lowerSum_le_taggedSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha := by
  rcases hs with ⟨hab, hfAbove, hfBelow, hmono⟩

  unfold lowerSum taggedSum

  refine Finset.sum_le_sum ?_
  intro i _hi

  have hstep :
      lowerStep P f i ≤ f (tags i) :=
    lowerStep_le_tag P i hfBelow (htags i)

  have hinc :
      0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P
      ⟨hab, hfAbove, hfBelow, hmono⟩

  exact mul_le_mul_of_nonneg_right hstep hinc

/--
For a tag chosen inside the `i`-th subinterval, the tagged value is bounded above
by the upper step.

Mathematically:

`f(tᵢ) ≤ sup { f x | x ∈ [xᵢ, xᵢ₊₁] }`

provided `tᵢ ∈ [xᵢ, xᵢ₊₁]`.
-/
lemma tag_le_upperStep {a b : ℝ} {f : ℝ → ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    {x : ℝ} (hx : x ∈ Partition.subinterval P i) :
    f x ≤ upperStep P f i := by
  have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono
      (Set.image_mono (subinterval_subset_Icc_core P))
      hfAbove
  unfold upperStep
  exact le_csSup hcellAbove ⟨x, hx, rfl⟩


/--
For a fixed partition, every tagged Riemann--Stieltjes sum is bounded above by
the corresponding upper Riemann--Stieltjes sum, provided the tags are chosen in
the corresponding subintervals.

This is the finite-sum comparison

`S(P,tags,f,α) ≤ U(P,f,α)`.

The proof is pointwise on each subinterval:

* `f (tags i) ≤ upperStep P f i`;
* `α(xᵢ₊₁) - α(xᵢ) ≥ 0`;
* hence the corresponding products are ordered;
* summing preserves the inequality.
-/
lemma taggedSum_le_upperSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha := by
  rcases hs with ⟨hab, hfAbove, hfBelow, hmono⟩

  unfold taggedSum upperSum

  refine Finset.sum_le_sum ?_
  intro i _hi

  have hstep :
      f (tags i) ≤ upperStep P f i :=
    tag_le_upperStep P i hfAbove (htags i)

  have hinc :
      0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P
      ⟨hab, hfAbove, hfBelow, hmono⟩

  exact mul_le_mul_of_nonneg_right hstep hinc

end DarbouxRS


/--
A lower Riemann--Stieltjes sum is bounded above by any tagged sum over the same
partition, provided the tags are chosen in the corresponding subintervals.
-/
theorem lowerSum_le_taggedSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha :=
  DarbouxRS.lowerSum_le_taggedSum hs P tags htags

/--
A tagged Riemann--Stieltjes sum is bounded above by the upper sum over the same
partition, provided the tags are chosen in the corresponding subintervals.
-/
theorem taggedSum_le_upperSum {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha :=
  DarbouxRS.taggedSum_le_upperSum hs P tags htags


/--
If the upper and lower Riemann--Stieltjes sums have the same fine-partition
limit `L`, then every tagged Riemann--Stieltjes sum also converges to `L`.

The proof is a squeeze argument:

`lowerSum P f α ≤ taggedSum P tags f α ≤ upperSum P f α`.

Since both lower and upper sums are within `eps` of `L` for sufficiently small
mesh, the tagged sum is also within `eps` of `L`.
-/
theorem rsTaggedCommonLimit_of_rsUpperLowerCommonLimit
    {a b : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : rsUpperLowerCommonLimit a b f alpha L) :
    rsTaggedCommonLimit a b f alpha L := by
  -- Unfold the exported aliases.
  unfold rsUpperLowerCommonLimit at h
  unfold rsTaggedCommonLimit

  rcases h with ⟨hs, hlim⟩

  refine ⟨hs, ?_⟩

  intro eps heps

  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩

  refine ⟨δ, hδ, ?_⟩

  intro P tags htags hmesh

  have hP :
      |upperSum P f alpha - L| < eps ∧
      |lowerSum P f alpha - L| < eps :=
    Hδ P hmesh

  have h_lower :
      lowerSum P f alpha ≤ taggedSum P tags f alpha :=
    DarbouxRS.lowerSum_le_taggedSum hs P tags htags

  have h_upper :
      taggedSum P tags f alpha ≤ upperSum P f alpha :=
    DarbouxRS.taggedSum_le_upperSum hs P tags htags

  have h_upper_abs :
      |upperSum P f alpha - L| < eps :=
    hP.1

  have h_lower_abs :
      |lowerSum P f alpha - L| < eps :=
    hP.2

  apply abs_lt.mpr
  constructor
  · -- lower side: `-eps < taggedSum P tags f alpha - L`
    have h_lower_left :
        -eps < lowerSum P f alpha - L :=
      (abs_lt.mp h_lower_abs).1
    linarith

  · -- upper side: `taggedSum P tags f alpha - L < eps`
    have h_upper_right :
        upperSum P f alpha - L < eps :=
      (abs_lt.mp h_upper_abs).2
    linarith


/- # Design choice for structure RSIntegralWitness
  If upper and lower limit converge to the same limit, then
  the tagged limit also converges to the same limit.
-/
theorem taggedCommonLimit_of_upperLowerCommonLimit
    {a b : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    TaggedCommonLimit a b f alpha L := by
  exact rsTaggedCommonLimit_of_rsUpperLowerCommonLimit h



/--
Constructs the Riemann-Stieltjes integral witness for the sum of two integrable functions.

Given that `f` and `g` are Riemann-Stieltjes integrable with respect to `alpha`,
this definition bundles the exact limit value `(∫ f dα) + (∫ g dα)` together with
the formal proofs that both the Darboux (upper/lower) limits and the tagged limits
of `f + g` converge to this combined sum.

This relies on the subadditivity and superadditivity of partition sums established
in the core lemmas.
-/
noncomputable def rsIntegralWitness_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegralWitness (fun x => f x + g x) alpha a b where
  value := rsIntegral f alpha a b hf + rsIntegral g alpha a b hg
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_integrand_add_core
      (rsIntegral_source_spec hf) (rsIntegral_source_spec hg)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_integrand_add
      (rsIntegral_spec hf) (rsIntegral_spec hg)

/--
The Riemann-Stieltjes integral is additive with respect to the integrand.

If `f` and `g` are Riemann-Stieltjes integrable with respect to `alpha` on `[a, b]`,
then their pointwise sum `f + g` is also Riemann-Stieltjes integrable on `[a, b]`.

This theorem wraps the explicit limit constructed in `rsIntegralWitness_integrand_add`
into the existential `Prop` asserting integrability.
-/
noncomputable def rsIntegrable_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegrable (fun x => f x + g x) alpha a b :=
  ⟨rsIntegralWitness_integrand_add hf hg⟩

/-
 # Theorem 1.2 part 1
-/
theorem rsIntegral_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    rsIntegral (fun x => f x + g x) alpha a b
        (rsIntegrable_integrand_add hf hg) =
      rsIntegral f alpha a b hf + rsIntegral g alpha a b hg := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrand_add hf hg))
    (DarbouxRS.taggedCommonLimit_integrand_add (rsIntegral_spec hf) (rsIntegral_spec hg))


/--
Additivity of the Riemann-Stieltjes integral. (Theorem 1.2, Part 1)

If `f` and `g` are Riemann-Stieltjes integrable with respect to `alpha` on `[a, b]`,
then the integral of their sum `f + g` evaluates exactly to the sum of their individual integrals.

Mathematically:
`∫ (f + g) dα = ∫ f dα + ∫ g dα`

*Proof Idea:*

Earlier, we constructed `rsIntegrable_integrand_add`, which proved that the tagged sums
of `f + g` converge to the value `(∫ f dα) + (∫ g dα)`. Because the limit of a
Riemann-Stieltjes sum is strictly unique (`taggedCommonLimit_unique`), the formally
extracted integral of `f + g` must be mathematically equal to this combined sum.
-/
noncomputable def rsIntegralWitness_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegralWitness (fun x => c * f x) alpha a b where
  value := c * rsIntegral f alpha a b hf
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_const_mul_core
      (c := c) (rsIntegral_source_spec hf)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_const_mul_core
      (c := c) (rsIntegral_spec hf)

/--
The Riemann-Stieltjes integral is closed under scalar multiplication.

If a function `f` is Riemann-Stieltjes integrable with respect to `alpha` on `[a, b]`,
then for any real constant `c`, the scaled function `x ↦ c * f(x)` is also
Riemann-Stieltjes integrable on `[a, b]`.

This theorem wraps the explicit limit constructed in `rsIntegralWitness_integrand_const_mul`
(which proves the limit is `c * ∫ f dα`) into the existential `Prop` asserting that
the integral exists.
-/
noncomputable def rsIntegrable_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegrable (fun x => c * f x) alpha a b :=
  ⟨rsIntegralWitness_integrand_const_mul (c := c) hf⟩


/--  # Theorem 1.2 part 2
Homogeneity of the Riemann-Stieltjes integral. (Theorem 1.2, Part 2)

If `f` is Riemann-Stieltjes integrable with respect to `alpha` on `[a, b]`,
then the integral of the scaled function `c * f` evaluates exactly to `c` times
the integral of `f`.

Mathematically:
`∫ (c * f) dα = c * ∫ f dα`

*Proof Idea:*
Just as with the addition theorem, this proof relies on the strict uniqueness of limits.
We previously proved in `taggedCommonLimit_const_mul_core` that the tagged Riemann-Stieltjes
sums of `c * f` naturally converge to the value `c * (∫ f dα)`. By invoking the uniqueness
of the tagged limit (`taggedCommonLimit_unique`), we formally conclude that the extracted
integral of `c * f` must be exactly equal to this value.

Combined with Part 1 (additivity), this establishes that the Riemann-Stieltjes integral
is a linear operator with respect to the integrand!
-/
theorem rsIntegral_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    rsIntegral (fun x => c * f x) alpha a b
        (rsIntegrable_integrand_const_mul (c := c) hf) =
      c * rsIntegral f alpha a b hf := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrand_const_mul (c := c) hf))
    (DarbouxRS.taggedCommonLimit_const_mul_core (c := c) (rsIntegral_spec hf))


/- # Theorem 1.2 part 3
Monotonicity of the Riemann-Stieltjes integral. (Theorem 1.2, Part 3)

If `f` and `g` are Riemann-Stieltjes integrable with respect to `alpha` on `[a, b]`,
and `f(x) ≤ g(x)` for all `x ∈ [a, b]`, then the integral of `f` is less than
or equal to the integral of `g`.

Mathematically:
`f ≤ g  ⟹  ∫ f dα ≤ ∫ g dα`

*Proof Idea:*
Because the integrator `alpha` is monotonically increasing (which is guaranteed by
the underlying integrability hypotheses), the partition weights `Δα` are always non-negative.
This means that every individual tagged Riemann-Stieltjes sum naturally preserves
the function inequality `f(t_i) * Δα_i ≤ g(t_i) * Δα_i`.

Since the integrals are defined as the limits of these tagged sums, we simply
invoke `taggedCommonLimit_mono_core` to demonstrate that limits of ordered
sequences preserve their mathematical ordering.
-/
theorem rsIntegral_integrand_mono {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    rsIntegral f alpha a b hf ≤ rsIntegral g alpha a b hg :=
  DarbouxRS.taggedCommonLimit_mono_core (rsIntegral_spec hf) (rsIntegral_spec hg) hfg


end Thm_1_2





noncomputable section Darboux_fundamental_result




/-- A partition P' is a refinement of P if every point in P is also in P'. -/
def IsRefinement {a b : ℝ} (P P' : Partition a b) : Prop :=
  ∀ i : Fin (P.n + 1), ∃ j : Fin (P'.n + 1), P.pts i = P'.pts j

structure Refinement {a b : ℝ} (P P' : Partition a b) where
  index : Fin (P.n + 1) → Fin (P'.n + 1)
  index_spec : ∀ i, P.pts i = P'.pts (index i)
  strictMono_index : StrictMono index


namespace Refinement

noncomputable def block {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') (i : Fin P.n) : Finset (Fin P'.n) :=
  let lo : ℕ := (R.index i.castSucc).val
  let hi : ℕ := (R.index i.succ).val
  ((Finset.range (hi - lo)).attach.image
    (fun t =>
      ⟨lo + t.1, by
        have hmono :
            (R.index i.castSucc).val < (R.index i.succ).val := by
          exact R.strictMono_index Fin.castSucc_lt_succ

        have ht : t.1 < hi - lo := by
          simpa using Finset.mem_range.mp t.2

        have hhi : hi ≤ P'.n := by
          exact Nat.le_of_lt_succ (R.index i.succ).isLt

        omega⟩))

end Refinement


lemma lowerStep_le_of_subinterval_subset
    {a b : ℝ} {f : ℝ → ℝ}
    (P P' : Partition a b)
    (i : Fin P.n) (j : Fin P'.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    (hsub : Partition.subinterval P' j ⊆ Partition.subinterval P i) :
    lowerStep P f i ≤ lowerStep P' f j := by
  have hOldBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P))
      hfBelow

  have hNewNonempty : (f '' Partition.subinterval P' j).Nonempty := by
    refine ⟨f (P'.pts j.castSucc), ?_⟩
    refine ⟨P'.pts j.castSucc, ?_, rfl⟩
    constructor
    · exact le_rfl
    · exact le_of_lt (P'.strict_mono Fin.castSucc_lt_succ)

  unfold lowerStep
  refine le_csInf hNewNonempty ?_
  rintro y ⟨x, hx, rfl⟩
  exact csInf_le hOldBelow ⟨x, hsub hx, rfl⟩


lemma upperStep_le_of_subinterval_subset
    {a b : ℝ} {f : ℝ → ℝ}
    (P P' : Partition a b)
    (i : Fin P.n) (j : Fin P'.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    (hsub : Partition.subinterval P' j ⊆ Partition.subinterval P i) :
    upperStep P' f j ≤ upperStep P f i := by
  have hOldAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P))
      hfAbove

  have hNewNonempty : (f '' Partition.subinterval P' j).Nonempty := by
    refine ⟨f (P'.pts j.castSucc), ?_⟩
    refine ⟨P'.pts j.castSucc, ?_, rfl⟩
    constructor
    · exact le_rfl
    · exact le_of_lt (P'.strict_mono Fin.castSucc_lt_succ)

  unfold upperStep
  refine csSup_le hNewNonempty ?_
  rintro y ⟨x, hx, rfl⟩
  exact le_csSup hOldAbove ⟨x, hsub hx, rfl⟩


lemma Refinement.subinterval_subset_of_mem_block
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n}
    (hj : j ∈ R.block i) :
    Partition.subinterval P' j ⊆ Partition.subinterval P i := by
  classical

  unfold Refinement.block at hj
  dsimp only at hj

  rcases Finset.mem_image.mp hj with ⟨t, _htmem, htj⟩

  -- `t` is an element of the attached range, so `t.1` lies in the range.
  have ht_lt :
      t.1 <
        (R.index i.succ).val - (R.index i.castSucc).val := by
    exact Finset.mem_range.mp t.2

  -- The image equality says that the value of `j` is `lo + t`.
  have hjval :
      j.val = (R.index i.castSucc).val + t.1 := by
    exact (congrArg Fin.val htj).symm

  -- Left endpoint inequality:
  -- `R.index i ≤ j`.
  have hleft :
      R.index i.castSucc ≤ j.castSucc := by
    change (R.index i.castSucc).val ≤ j.val
    rw [hjval]
    omega

  -- Right endpoint inequality:
  -- `j + 1 ≤ R.index (i+1)`.
  have hright :
      j.succ ≤ R.index i.succ := by
    change j.val + 1 ≤ (R.index i.succ).val
    rw [hjval]
    omega

  intro x hx
  constructor
  · -- old left endpoint ≤ x
    have hpts_left :
        P'.pts (R.index i.castSucc) ≤ P'.pts j.castSucc :=
      P'.strict_mono.monotone hleft

    calc
      P.pts i.castSucc = P'.pts (R.index i.castSucc) :=
        R.index_spec i.castSucc
      _ ≤ P'.pts j.castSucc :=
        hpts_left
      _ ≤ x :=
        hx.1

  · -- x ≤ old right endpoint
    have hpts_right :
        P'.pts j.succ ≤ P'.pts (R.index i.succ) :=
      P'.strict_mono.monotone hright

    calc
      x ≤ P'.pts j.succ :=
        hx.2
      _ ≤ P'.pts (R.index i.succ) :=
        hpts_right
      _ = P.pts i.succ :=
        (R.index_spec i.succ).symm


-- lemma sum_range_sub_from (u : ℕ → ℝ) (m d : ℕ) :
--     (∑ t ∈ Finset.range d, (u (m + (t + 1)) - u (m + t)))
--       =
--     u (m + d) - u m := by
--   induction d with
--   | zero =>
--       simp
--   | succ d ih =>
--       rw [Finset.sum_range_succ, ih]
--       ring


lemma sum_range_sub_from (u : ℕ → ℝ) (m d : ℕ) :
    (∑ t ∈ Finset.range d, (u (m + (t + 1)) - u (m + t)))
      =
    u (m + d) - u m := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      ring


lemma Refinement.sum_block_increment
    {a b : ℝ} {α : ℝ → ℝ}
    {P P' : Partition a b}
    (R : Refinement P P')
    (i : Fin P.n) :
    Finset.sum (R.block i)
      (fun j => α (P'.pts j.succ) - α (P'.pts j.castSucc))
      =
    α (P.pts i.succ) - α (P.pts i.castSucc) := by
  classical

  let lo : ℕ := (R.index i.castSucc).val
  let hi : ℕ := (R.index i.succ).val
  let d : ℕ := hi - lo

  have hmono_fin :
      R.index i.castSucc < R.index i.succ :=
    R.strictMono_index Fin.castSucc_lt_succ

  have hmono : lo < hi := by
    exact hmono_fin

  have hhi_le : hi ≤ P'.n := by
    exact Nat.le_of_lt_succ (R.index i.succ).isLt

  have hlo_lt_succ : lo < P'.n + 1 := by
    exact (R.index i.castSucc).isLt

  have hhi_lt_succ : hi < P'.n + 1 := by
    exact (R.index i.succ).isLt

  have hlo_add_d : lo + d = hi := by
    dsimp [d]
    omega

  let u : ℕ → ℝ := fun k =>
    if hk : k < P'.n + 1 then
      α (P'.pts ⟨k, hk⟩)
    else
      0

  have htel :
      (∑ t ∈ Finset.range d,
        (u (lo + (t + 1)) - u (lo + t)))
        =
      u (lo + d) - u lo :=
    sum_range_sub_from u lo d

  have hsum_image :
      (∑ j ∈ R.block i,
        (α (P'.pts j.succ) - α (P'.pts j.castSucc)))
        =
      ∑ t ∈ (Finset.range d).attach,
        (α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).castSucc))) := by
    unfold Refinement.block
    dsimp [lo, hi, d]

    rw [Finset.sum_image]
    · -- Main goal: compare the two sums over the attached range.
      refine Finset.sum_congr rfl ?_
      intro t ht

      apply congrArg₂ (fun x y : ℝ => x - y)
      · -- right endpoint: `(⟨lo + t, _⟩ : Fin P'.n).succ`
        -- equals the `Fin (P'.n + 1)` with value `lo + t + 1`
        apply congrArg (fun z => α (P'.pts z))
        apply Fin.ext
        simp [Fin.succ, Nat.add_assoc]

      · -- left endpoint: `(⟨lo + t, _⟩ : Fin P'.n).castSucc`
        -- equals the `Fin (P'.n + 1)` with value `lo + t`
        apply congrArg (fun z => α (P'.pts z))
        apply Fin.ext
        simp [Fin.castSucc]

    · -- Side goal: injectivity of the map used in `Finset.image`.
      intro x _hx y _hy hxy
      apply Subtype.ext
      have hval :
          lo + x.1 = lo + y.1 := by
        exact congrArg Fin.val hxy
      omega


  have hsum_attach :
      Finset.sum ((Finset.range d).attach)
        (fun t =>
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).castSucc)))
        =
      Finset.sum (Finset.range d)
        (fun t => u (lo + (t + 1)) - u (lo + t)) := by

    let G : ℕ → ℝ :=
      fun t => u (lo + (t + 1)) - u (lo + t)

    have h₁ :
        Finset.sum ((Finset.range d).attach)
          (fun t =>
            α (P'.pts
              ((⟨lo + t.1, by
                have ht : t.1 < d := by
                  exact Finset.mem_range.mp t.2
                have hlt_hi : lo + t.1 < hi := by
                  dsimp [d] at ht
                  omega
                exact lt_of_lt_of_le hlt_hi hhi_le
              ⟩ : Fin P'.n).succ))
            -
            α (P'.pts
              ((⟨lo + t.1, by
                have ht : t.1 < d := by
                  exact Finset.mem_range.mp t.2
                have hlt_hi : lo + t.1 < hi := by
                  dsimp [d] at ht
                  omega
                exact lt_of_lt_of_le hlt_hi hhi_le
              ⟩ : Fin P'.n).castSucc)))
          =
        Finset.sum ((Finset.range d).attach)
          (fun t => G t.1) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem

      have htlt : t.1 < d := by
        exact Finset.mem_range.mp t.2

      have hleft_valid : lo + t.1 < P'.n + 1 := by
        have hlt_hi : lo + t.1 < hi := by
          dsimp [d] at htlt
          omega
        omega

      have hright_valid : lo + (t.1 + 1) < P'.n + 1 := by
        have hle_hi : lo + (t.1 + 1) ≤ hi := by
          dsimp [d] at htlt
          omega
        omega

      dsimp [G, u]
      rw [dif_pos hright_valid, dif_pos hleft_valid]

      apply congrArg₂ Sub.sub
      · -- right endpoint
        apply congrArg (fun y : ℝ => α y)
        apply congrArg (fun z : Fin (P'.n + 1) => P'.pts z)
        apply Fin.ext
        simp
        omega

      · -- left endpoint
        apply congrArg (fun y : ℝ => α y)
        apply congrArg (fun z : Fin (P'.n + 1) => P'.pts z)
        apply Fin.ext
        simp

    have h₂ :
        Finset.sum ((Finset.range d).attach)
          (fun t => G t.1)
          =
        Finset.sum (Finset.range d) G := by
      simpa [G] using
        (Finset.sum_attach (s := Finset.range d) (f := G))

    calc
      Finset.sum ((Finset.range d).attach)
        (fun t =>
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).castSucc)))
          =
        Finset.sum ((Finset.range d).attach)
          (fun t => G t.1) := h₁
      _ =
        Finset.sum (Finset.range d) G := h₂
      _ =
        Finset.sum (Finset.range d)
          (fun t => u (lo + (t + 1)) - u (lo + t)) := by
        rfl

  have hu_lo :
      u lo = α (P'.pts (R.index i.castSucc)) := by
    have hfin :
        (⟨lo, hlo_lt_succ⟩ : Fin (P'.n + 1)) =
          R.index i.castSucc := by
      apply Fin.ext
      dsimp [lo]

    dsimp [u]
    rw [dif_pos hlo_lt_succ]


  have hu_hi :
      u hi = α (P'.pts (R.index i.succ)) := by
    have hfin :
        (⟨hi, hhi_lt_succ⟩ : Fin (P'.n + 1)) =
          R.index i.succ := by
      apply Fin.ext
      dsimp [hi]

    dsimp [u]
    rw [dif_pos hhi_lt_succ]


  calc
    (∑ j ∈ R.block i,
      (α (P'.pts j.succ) - α (P'.pts j.castSucc)))
        =
      (∑ t ∈ (Finset.range d).attach,
        (α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).castSucc)))) := by
        exact hsum_image

    _ =
      (∑ t ∈ Finset.range d,
        (u (lo + (t + 1)) - u (lo + t))) := by
        exact hsum_attach

    _ = u (lo + d) - u lo := by
        exact htel

    _ = u hi - u lo := by
        rw [hlo_add_d]

    _ =
      α (P'.pts (R.index i.succ))
        -
      α (P'.pts (R.index i.castSucc)) := by
        rw [hu_hi, hu_lo]

    _ =
      α (P.pts i.succ) - α (P.pts i.castSucc) := by
        rw [← R.index_spec i.succ, ← R.index_spec i.castSucc]

lemma Refinement.mem_block_iff
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n} :
    j ∈ R.block i ↔
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val := by
  classical
  unfold Refinement.block
  dsimp
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨t, _htmem, htj⟩

    have htlt :
        t.1 < (R.index i.succ).val - (R.index i.castSucc).val := by
      exact Finset.mem_range.mp t.2

    have hjval :
        j.val = (R.index i.castSucc).val + t.1 := by
      exact (congrArg Fin.val htj).symm

    constructor
    · rw [hjval]
      omega
    · rw [hjval]
      omega

  · intro hj
    rcases hj with ⟨hlo, hhi⟩

    let tnat : ℕ := j.val - (R.index i.castSucc).val

    have htlt :
        tnat < (R.index i.succ).val - (R.index i.castSucc).val := by
      dsimp [tnat]
      omega

    let t :
        {x // x ∈ Finset.range
          ((R.index i.succ).val - (R.index i.castSucc).val)} :=
      ⟨tnat, Finset.mem_range.mpr htlt⟩

    apply Finset.mem_image.mpr
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · apply Fin.ext
      dsimp [t, tnat]
      omega

lemma Refinement.block_disjoint
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i k : Fin P.n} (hik : i ≠ k) :
    Disjoint (R.block i) (R.block k) := by
  classical

  refine Finset.disjoint_left.mpr ?_
  intro j hji hjk

  have hji' :
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val :=
    (Refinement.mem_block_iff R (i := i) (j := j)).mp hji

  have hjk' :
      (R.index k.castSucc).val ≤ j.val ∧
      j.val < (R.index k.succ).val :=
    (Refinement.mem_block_iff R (i := k) (j := j)).mp hjk

  rcases lt_or_gt_of_ne hik with hiklt | hkilt

  · -- case `i < k`
    have hbase : i.succ ≤ k.castSucc := by
      change i.val + 1 ≤ k.val
      exact Nat.succ_le_of_lt hiklt

    have hidx :
        R.index i.succ ≤ R.index k.castSucc :=
      R.strictMono_index.monotone hbase

    have hidx_val :
        (R.index i.succ).val ≤ (R.index k.castSucc).val := by
      exact hidx

    omega

  · -- case `k < i`
    have hbase : k.succ ≤ i.castSucc := by
      change k.val + 1 ≤ i.val
      exact Nat.succ_le_of_lt hkilt

    have hidx :
        R.index k.succ ≤ R.index i.castSucc :=
      R.strictMono_index.monotone hbase

    have hidx_val :
        (R.index k.succ).val ≤ (R.index i.castSucc).val := by
      exact hidx

    omega


lemma Refinement.index_zero
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') :
    R.index (0 : Fin (P.n + 1)) = (0 : Fin (P'.n + 1)) := by
  by_contra hne

  have hne' :
      (0 : Fin (P'.n + 1)) ≠ R.index (0 : Fin (P.n + 1)) := by
    intro h
    exact hne h.symm

  have hlt :
      (0 : Fin (P'.n + 1)) < R.index (0 : Fin (P.n + 1)) := by
    exact lt_of_le_of_ne (Fin.zero_le _) hne'

  have hpts_lt :
      P'.pts (0 : Fin (P'.n + 1)) <
        P'.pts (R.index (0 : Fin (P.n + 1))) :=
    P'.strict_mono hlt

  have : a < a := by
    calc
      a = P'.pts (0 : Fin (P'.n + 1)) := P'.pts_start.symm
      _ < P'.pts (R.index (0 : Fin (P.n + 1))) := hpts_lt
      _ = P.pts (0 : Fin (P.n + 1)) := (R.index_spec 0).symm
      _ = a := P.pts_start

  exact (lt_irrefl a) this


lemma Refinement.index_last
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') :
    R.index (Fin.last P.n) = Fin.last P'.n := by
  by_contra hne

  have hlt :
      R.index (Fin.last P.n) < Fin.last P'.n := by
    exact lt_of_le_of_ne (Fin.le_last _) hne

  have hpts_lt :
      P'.pts (R.index (Fin.last P.n)) <
        P'.pts (Fin.last P'.n) :=
    P'.strict_mono hlt

  have : b < b := by
    calc
      b = P.pts (Fin.last P.n) := P.pts_end.symm
      _ = P'.pts (R.index (Fin.last P.n)) := R.index_spec (Fin.last P.n)
      _ < P'.pts (Fin.last P'.n) := hpts_lt
      _ = b := P'.pts_end

  exact (lt_irrefl b) this

lemma Refinement.exists_mem_block
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    (j : Fin P'.n) :
    ∃ i : Fin P.n, j ∈ R.block i := by
  classical

  let Q : ℕ → Prop :=
    fun q =>
      ∃ hq : q < P.n + 1,
        j.val < (R.index ⟨q, hq⟩).val

  have hQ : ∃ q : ℕ, Q q := by
    refine ⟨P.n, ?_⟩
    dsimp [Q]
    refine ⟨by omega, ?_⟩

    have hlast_fin :
        (⟨P.n, by omega⟩ : Fin (P.n + 1)) = Fin.last P.n := by
      apply Fin.ext
      simp

    have hlast_val :
        (R.index (⟨P.n, by omega⟩ : Fin (P.n + 1))).val = P'.n := by
      rw [hlast_fin, Refinement.index_last R]
      rfl

    rw [hlast_val]
    exact j.isLt

  let q : ℕ := Nat.find hQ

  have hqspec : Q q := Nat.find_spec hQ

  rcases hqspec with ⟨hq_bound, hj_lt_q⟩

  have hq_pos : 0 < q := by
    by_contra hnot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hnot

    have hfin0 :
        (⟨q, hq_bound⟩ : Fin (P.n + 1)) =
          (0 : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [hq0]

    have : j.val < 0 := by
      calc
        j.val < (R.index (⟨q, hq_bound⟩ : Fin (P.n + 1))).val := hj_lt_q
        _ = (R.index (0 : Fin (P.n + 1))).val := by
          rw [hfin0]
        _ = 0 := by
          rw [Refinement.index_zero R]
          rfl

    omega

  have hprev_lt_q : q - 1 < q := by
    omega

  have hnot_prev : ¬ Q (q - 1) := by
    exact Nat.find_min hQ hprev_lt_q

  have hprev_bound : q - 1 < P.n + 1 := by
    omega

  have hprev_le :
      (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val ≤ j.val := by
    by_contra hnot_le
    have hlt :
        j.val <
          (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val :=
      Nat.lt_of_not_ge hnot_le

    exact hnot_prev ⟨hprev_bound, hlt⟩

  let i : Fin P.n := ⟨q - 1, by omega⟩

  refine ⟨i, ?_⟩

  apply (Refinement.mem_block_iff R (i := i) (j := j)).mpr
  constructor
  · have hcast :
        i.castSucc =
          (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]

    simpa [hcast] using hprev_le

  · have hsucc :
        i.succ =
          (⟨q, hq_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]
      omega

    simpa [hsucc] using hj_lt_q


lemma Refinement.biUnion_block_eq_univ
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') :
    (Finset.univ.biUnion fun i : Fin P.n => R.block i)
      =
    (Finset.univ : Finset (Fin P'.n)) := by
  classical

  ext j
  constructor
  · intro _hj
    exact Finset.mem_univ j

  · intro _hj
    rcases Refinement.exists_mem_block R j with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩



lemma Refinement.sum_blocks_eq_sum_univ
    {a b : ℝ}
    {P P' : Partition a b}
    (R : Refinement P P')
    (g : Fin P'.n → ℝ) :
    (∑ i : Fin P.n, ∑ j ∈ R.block i, g j)
      =
    ∑ j : Fin P'.n, g j := by
  classical

  change
    Finset.sum (Finset.univ : Finset (Fin P.n))
      (fun i => Finset.sum (R.block i) g)
      =
    Finset.sum (Finset.univ : Finset (Fin P'.n)) g

  have hsum :
      Finset.sum
        ((Finset.univ : Finset (Fin P.n)).biUnion
          (fun i => R.block i))
        g
        =
      Finset.sum (Finset.univ : Finset (Fin P.n))
        (fun i => Finset.sum (R.block i) g) := by
    apply Finset.sum_biUnion
    intro i _hi k _hk hik
    exact Refinement.block_disjoint R hik

  calc
    Finset.sum (Finset.univ : Finset (Fin P.n))
      (fun i => Finset.sum (R.block i) g)
        =
      Finset.sum
        ((Finset.univ : Finset (Fin P.n)).biUnion
          (fun i => R.block i))
        g := hsum.symm
    _ =
      Finset.sum (Finset.univ : Finset (Fin P'.n)) g := by
        rw [Refinement.biUnion_block_eq_univ R]




lemma lowerSum_le_of_refinement {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    {P P' : Partition a b}
    (R : Refinement P P') :
    lowerSum P f α ≤ lowerSum P' f α := by
  classical
  rcases hs with ⟨hab, hfAbove, hfBelow, hαmono⟩

  unfold lowerSum

  calc
    (∑ i : Fin P.n,
      lowerStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)))
        =
      ∑ i : Fin P.n,
        lowerStep P f i *
          (∑ j ∈  R.block i,
            (α (P'.pts j.succ) - α (P'.pts j.castSucc))) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [R.sum_block_increment i]

    _ =
      ∑ i : Fin P.n,
        ∑ j ∈  R.block i,
          lowerStep P f i *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Finset.mul_sum]

    _ ≤
      ∑ i : Fin P.n,
        ∑ j ∈  R.block i,
          lowerStep P' f j *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        refine Finset.sum_le_sum ?_
        intro j hj

        have hsub :
            Partition.subinterval P' j ⊆ Partition.subinterval P i :=
          R.subinterval_subset_of_mem_block hj

        have hstep :
            lowerStep P f i ≤ lowerStep P' f j :=
          lowerStep_le_of_subinterval_subset P P' i j hfBelow hsub

        have hinc :
            0 ≤ α (P'.pts j.succ) - α (P'.pts j.castSucc) :=
          DarbouxRS.partition_increment_nonneg_of_source_core P'
            ⟨hab, hfAbove, hfBelow, hαmono⟩

        exact mul_le_mul_of_nonneg_right hstep hinc

    _ =
      ∑ j : Fin P'.n,
        lowerStep P' f j *
          (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        rw [R.sum_blocks_eq_sum_univ]

    _ = lowerSum P' f α := by
        rfl

lemma upperSum_le_of_refinement {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    {P P' : Partition a b}
    (R : Refinement P P') :
    upperSum P' f α ≤ upperSum P f α := by
  classical
  rcases hs with ⟨hab, hfAbove, hfBelow, hαmono⟩

  unfold upperSum

  calc
    (∑ j : Fin P'.n,
      upperStep P' f j *
        (α (P'.pts j.succ) - α (P'.pts j.castSucc)))
        =
      ∑ i : Fin P.n,
        ∑ j ∈ R.block i,
          upperStep P' f j *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        rw [← R.sum_blocks_eq_sum_univ]

    _ ≤
      ∑ i : Fin P.n,
        ∑ j ∈ R.block i,
          upperStep P f i *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        refine Finset.sum_le_sum ?_
        intro j hj

        have hsub :
            Partition.subinterval P' j ⊆ Partition.subinterval P i :=
          R.subinterval_subset_of_mem_block hj

        have hstep :
            upperStep P' f j ≤ upperStep P f i :=
          upperStep_le_of_subinterval_subset P P' i j hfAbove hsub

        have hinc :
            0 ≤ α (P'.pts j.succ) - α (P'.pts j.castSucc) :=
          DarbouxRS.partition_increment_nonneg_of_source_core P'
            ⟨hab, hfAbove, hfBelow, hαmono⟩

        exact mul_le_mul_of_nonneg_right hstep hinc

    _ =
      ∑ i : Fin P.n,
        upperStep P f i *
          (∑ j ∈ R.block i,
            (α (P'.pts j.succ) - α (P'.pts j.castSucc))) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Finset.mul_sum]

    _ =
      ∑ i : Fin P.n,
        upperStep P f i *
          (α (P.pts i.succ) - α (P.pts i.castSucc)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [R.sum_block_increment i]

    _ = upperSum P f α := by
        rfl




namespace Partition

def carrier {a b : ℝ} (P : Partition a b) : Finset ℝ :=
  Finset.univ.image P.pts

lemma pts_mem_carrier {a b : ℝ} (P : Partition a b) (i : Fin (P.n + 1)) :
    P.pts i ∈ P.carrier := by
  unfold carrier
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

lemma start_mem_carrier {a b : ℝ} (P : Partition a b) :
    a ∈ P.carrier := by
  simpa [P.pts_start] using
    (P.pts_mem_carrier (0 : Fin (P.n + 1)))

lemma end_mem_carrier {a b : ℝ} (P : Partition a b) :
    b ∈ P.carrier := by
  simpa [P.pts_end] using
    (P.pts_mem_carrier (Fin.last P.n))

lemma carrier_subset_Icc {a b : ℝ} (P : Partition a b) :
    ↑P.carrier ⊆ Set.Icc a b := by
  intro x hx
  unfold carrier at hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  exact DarbouxRS.partition_pts_mem_Icc_core P

end Partition

noncomputable def Refinement.of_exists
    {a b : ℝ} {P P' : Partition a b}
    (h : ∀ i : Fin (P.n + 1),
      ∃ j : Fin (P'.n + 1), P.pts i = P'.pts j) :
    Refinement P P' where
  index := fun i => Classical.choose (h i)
  index_spec := fun i => Classical.choose_spec (h i)
  strictMono_index := by
    intro i j hij
    by_contra hnot

    have hji :
        Classical.choose (h j) ≤ Classical.choose (h i) :=
      le_of_not_gt hnot

    have hP'le :
        P'.pts (Classical.choose (h j)) ≤
        P'.pts (Classical.choose (h i)) :=
      P'.strict_mono.monotone hji

    have hi :
        P.pts i = P'.pts (Classical.choose (h i)) :=
      Classical.choose_spec (h i)

    have hj :
        P.pts j = P'.pts (Classical.choose (h j)) :=
      Classical.choose_spec (h j)

    have hPle : P.pts j ≤ P.pts i := by
      calc
        P.pts j = P'.pts (Classical.choose (h j)) := hj
        _ ≤ P'.pts (Classical.choose (h i)) := hP'le
        _ = P.pts i := hi.symm

    exact not_le_of_gt (P.strict_mono hij) hPle


/--
Build a partition from a finite set of points containing `a` and `b`,
contained in `[a,b]`, by sorting the set increasingly.
-/
noncomputable def Partition.ofFinset
    {a b : ℝ} (hab : a < b)
    (s : Finset ℝ)
    (ha : a ∈ s) (hb : b ∈ s)
    (hsub : ↑s ⊆ Set.Icc a b) :
    Partition a b := by
  classical

  have hpair : ({a, b} : Finset ℝ) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb

  have hpair_card : ({a, b} : Finset ℝ).card = 2 := by
    simp [ne_of_lt hab]

  have hcard_ge_two : 2 ≤ s.card := by
    calc
      2 = ({a, b} : Finset ℝ).card := hpair_card.symm
      _ ≤ s.card := Finset.card_le_card hpair

  have hcard_pos : 0 < s.card := by omega

  have hcard_eq : s.card - 1 + 1 = s.card := by
    omega

  have hn : 0 < s.card - 1 := by
    omega

  let e : Fin s.card ≃o s := s.orderIsoOfFin (k := s.card) rfl

  refine
  { n := s.card - 1
    hn := hn
    pts := fun i => (e (Fin.cast hcard_eq i)).1
    pts_start := ?_
    pts_end := ?_
    strict_mono := ?_ }

  · -- first point is `a`
    let i0 : Fin s.card :=
      Fin.cast hcard_eq (0 : Fin (s.card - 1 + 1))

    obtain ⟨ia, hia⟩ := e.surjective ⟨a, ha⟩

    have hi0_le : i0 ≤ ia := by
      change i0.val ≤ ia.val
      simp [i0]

    have hleft : (e i0).1 ≤ a := by
      calc
        (e i0).1 ≤ (e ia).1 := e.monotone hi0_le
        _ = a := congrArg Subtype.val hia

    have hright : a ≤ (e i0).1 := by
      exact (hsub (e i0).2).1

    change (e (Fin.cast hcard_eq (0 : Fin (s.card - 1 + 1)))).1 = a
    exact le_antisymm hleft hright

  · -- last point is `b`
    let ilast : Fin s.card :=
      Fin.cast hcard_eq (Fin.last (s.card - 1))

    obtain ⟨ib, hib⟩ := e.surjective ⟨b, hb⟩

    have hib_le : ib ≤ ilast := by
      change ib.val ≤ ilast.val
      simp [ilast]
      exact Nat.le_pred_of_lt ib.isLt

    have hleft : b ≤ (e ilast).1 := by
      calc
        b = (e ib).1 := (congrArg Subtype.val hib).symm
        _ ≤ (e ilast).1 := e.monotone hib_le

    have hright : (e ilast).1 ≤ b := by
      exact (hsub (e ilast).2).2

    change
      (e (Fin.cast hcard_eq (Fin.last (s.card - 1)))).1 = b
    exact le_antisymm hright hleft

  · -- strict monotonicity
    intro i j hij
    change
      (e (Fin.cast hcard_eq i)).1 <
      (e (Fin.cast hcard_eq j)).1

    have hcast :
        Fin.cast hcard_eq i < Fin.cast hcard_eq j := by
      change i.val < j.val
      exact hij

    exact e.strictMono hcast

lemma Partition.ofFinset_contains
    {a b : ℝ} (hab : a < b)
    (s : Finset ℝ)
    (ha : a ∈ s) (hb : b ∈ s)
    (hsub : ↑s ⊆ Set.Icc a b)
    {x : ℝ} (hx : x ∈ s) :
    ∃ j : Fin ((Partition.ofFinset hab s ha hb hsub).n + 1),
      (Partition.ofFinset hab s ha hb hsub).pts j = x := by
  classical

  have hpair : ({a, b} : Finset ℝ) ⊆ s := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb

  have hpair_card : ({a, b} : Finset ℝ).card = 2 := by
    simp [ne_of_lt hab]

  have hcard_ge_two : 2 ≤ s.card := by
    calc
      2 = ({a, b} : Finset ℝ).card := hpair_card.symm
      _ ≤ s.card := Finset.card_le_card hpair

  have hcard_eq : s.card - 1 + 1 = s.card := by
    omega

  let e : Fin s.card ≃o s := s.orderIsoOfFin (k := s.card) rfl

  obtain ⟨ix, hix⟩ := e.surjective ⟨x, hx⟩

  let j : Fin (s.card - 1 + 1) :=
    Fin.cast hcard_eq.symm ix

  refine ⟨j, ?_⟩

  change (e (Fin.cast hcard_eq j)).1 = x

  have hcast : Fin.cast hcard_eq j = ix := by
    ext
    simp [j]

  rw [hcast]
  exact congrArg Subtype.val hix


lemma partition_endpoint_lt {a b : ℝ} (P : Partition a b) :
    a < b := by
  have hzero_last : (0 : Fin (P.n + 1)) < Fin.last P.n := by
    change 0 < P.n
    exact P.hn

  calc
    a = P.pts 0 := P.pts_start.symm
    _ < P.pts (Fin.last P.n) := P.strict_mono hzero_last
    _ = b := P.pts_end


lemma exists_common_refinement {a b : ℝ} (P1 P2 : Partition a b) :
    ∃ P : Partition a b,
      ∃ _R1 : Refinement P1 P,
        ∃ _R2 : Refinement P2 P,
          True := by
  classical

  have hab : a < b := partition_endpoint_lt P1

  let s : Finset ℝ := P1.carrier ∪ P2.carrier

  have ha : a ∈ s := by
    exact Finset.mem_union_left _ P1.start_mem_carrier

  have hb : b ∈ s := by
    exact Finset.mem_union_left _ P1.end_mem_carrier

  have hsub : ↑s ⊆ Set.Icc a b := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · exact P1.carrier_subset_Icc hx1
    · exact P2.carrier_subset_Icc hx2

  let P : Partition a b :=
    Partition.ofFinset hab s ha hb hsub

  have hP1_exists :
      ∀ i : Fin (P1.n + 1),
        ∃ j : Fin (P.n + 1), P1.pts i = P.pts j := by
    intro i
    have hx : P1.pts i ∈ s := by
      exact Finset.mem_union_left _ (P1.pts_mem_carrier i)

    rcases Partition.ofFinset_contains hab s ha hb hsub hx with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

  have hP2_exists :
      ∀ i : Fin (P2.n + 1),
        ∃ j : Fin (P.n + 1), P2.pts i = P.pts j := by
    intro i
    have hx : P2.pts i ∈ s := by
      exact Finset.mem_union_right _ (P2.pts_mem_carrier i)

    rcases Partition.ofFinset_contains hab s ha hb hsub hx with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

  let R1 : Refinement P1 P :=
    Refinement.of_exists hP1_exists

  let R2 : Refinement P2 P :=
    Refinement.of_exists hP2_exists

  exact ⟨P, R1, R2, trivial⟩


-----------------------------------------------------------------------------
--  The Fundamental Darboux Inequality
-----------------------------------------------------------------------------

/--
Any lower sum is bounded above by any upper sum on the same interval.
Proven by channeling both sums through their common refinement.
-/
lemma lowerSum_le_upperSum_any {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α) (P1 P2 : Partition a b) :
    lowerSum P1 f α ≤ upperSum P2 f α := by
  rcases exists_common_refinement P1 P2 with ⟨Q, R1, R2, _⟩

  have h1 : lowerSum P1 f α ≤ lowerSum Q f α :=
    lowerSum_le_of_refinement hs R1

  have h2 : lowerSum Q f α ≤ upperSum Q f α :=
    DarbouxRS.lowerSum_le_upperSum_core Q hs

  have h3 : upperSum Q f α ≤ upperSum P2 f α :=
    upperSum_le_of_refinement hs R2

  exact le_trans h1 (le_trans h2 h3)


end Darboux_fundamental_result
