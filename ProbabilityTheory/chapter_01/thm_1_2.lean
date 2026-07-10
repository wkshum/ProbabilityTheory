import ProbabilityTheory.chapter_01.def_1_2

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

  -- FIX: Define `tags` to exactly match `Fin P.n → ℝ` using left endpoints
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


end DarbouxRS







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
