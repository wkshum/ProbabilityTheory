import ProbabilityTheory.chapter_01.def_1_2
import ProbabilityTheory.chapter_01.thm_1_2

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open Set MeasureTheory
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

/-!
# Riemann--Stieltjes integral with differentiable integrator

If `α` has continuous derivative `α'`, then

  ∫ f dα = ∫ f(x) * α'(x) dx.

The proof follows the tagged-sum route:

1. Show that the ordinary interval integral is the RS integral with respect to
   the identity integrator.
2. For each partition cell, use the mean value theorem to choose a point `cᵢ`
   such that
     `α xᵢ₊₁ - α xᵢ = α' cᵢ * (xᵢ₊₁ - xᵢ)`.
3. Compare the tagged RS sum for `(f, α)` with the tagged RS sum for
   `(fun x => f x * α' x, id)`.
4. Use uniform continuity of `α'` to make the difference small.
-/

/-! ## Basic consequences and squeeze lemma -/

/--
If a Riemann--Stieltjes integral witness exists on `[a, b]`, then the interval is
strictly nondegenerate: `a < b`.

This is not a new analytic fact; it simply unpacks the `SourceHypotheses` stored
inside the chosen `RSIntegralWitness`.  In the current development,
`RSIntegrable f α a b` is defined as nonemptiness of `RSIntegralWitness f α a b`,
and each witness contains a Darboux upper/lower common-limit proof.  The first
field of the corresponding `SourceHypotheses` is exactly `a < b`.
-/
lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨w⟩
  exact w.source_limit.1.1


/--
A tagged Riemann--Stieltjes sum lies between the lower and upper
Riemann--Stieltjes sums over the same partition.

More precisely, if the source hypotheses hold and every tag is chosen inside its
corresponding partition subinterval, then

`lowerSum P f α ≤ taggedSum P tags f α ≤ upperSum P f α`.

The proof is cellwise.  On each subinterval, the tag value `f (tags i)` lies
between the infimum `lowerStep P f i` and the supremum `upperStep P f i`.
The monotonicity of the integrator `α` on `[a, b]` implies that every
Riemann--Stieltjes increment

`α (P.pts i.succ) - α (P.pts i.castSucc)`

is nonnegative.  Therefore multiplying the pointwise inequalities by these
increments preserves the order, and summing over all cells gives the result.
-/
lemma taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f α ≤ taggedSum P tags f α ∧
      taggedSum P tags f α ≤ upperSum P f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  constructor
  · unfold lowerSum taggedSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
      BddBelow.mono
        (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
        hBelow
    have hlow_le_tag : lowerStep P f i ≤ f (tags i) := by
      unfold lowerStep
      exact csInf_le hcellBelow ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right hlow_le_tag hinc_nonneg
  · unfold taggedSum upperSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
      BddAbove.mono
        (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
        hAbove
    have htag_le_up : f (tags i) ≤ upperStep P f i := by
      unfold upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right htag_le_up hinc_nonneg



/--
The Darboux upper/lower common-limit formulation implies the tagged-sum
common-limit formulation.

In the present development there are two equivalent ways to express the value of
a Riemann--Stieltjes integral on `[a, b]`:

* `rsUpperLowerCommonLimit a b f α L`: both the upper sums and lower sums tend
  to `L` as the mesh tends to zero;
* `rsTaggedCommonLimit a b f α L`: every tagged Riemann--Stieltjes sum with
  tags chosen in the corresponding subintervals tends to `L` as the mesh tends
  to zero.

This theorem proves the forward implication.  For a fixed sufficiently fine
partition `P`, the previous lemma `taggedSum_between_lower_upper` gives

`lowerSum P f α ≤ taggedSum P tags f α ≤ upperSum P f α`.

If both `lowerSum P f α` and `upperSum P f α` are within `eps` of `L`, then the
tagged sum is squeezed between them and is also within `eps` of `L`.  The proof
is therefore a direct epsilon-delta squeeze argument.
-/
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

/-! ## Oscillation of a partition -/


/--
The total oscillation contribution of `f` over a partition `P`, weighted by the
Riemann--Stieltjes increments of the integrator `α`.

For each subinterval `[xᵢ, xᵢ₊₁]` of the partition, the quantity

`upperStep P f i - lowerStep P f i`

is the oscillation of `f` on that subinterval: the difference between the
supremum and infimum of `f` there.  Multiplying by

`α (P.pts i.succ) - α (P.pts i.castSucc)`

weights this oscillation by the corresponding `α`-increment.  Thus
`partitionOscillation P f α` is

`∑ᵢ (Mᵢ - mᵢ) * (α xᵢ₊₁ - α xᵢ)`.

Under the usual monotonicity hypothesis on `α`, this is exactly the gap between
the upper and lower Riemann--Stieltjes sums:

`upperSum P f α - lowerSum P f α`.

This quantity is useful for Darboux-style integrability arguments.
-/
noncomputable def partitionOscillation {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    (upperStep P f i - lowerStep P f i) *
      (α (P.pts i.succ) - α (P.pts i.castSucc))

lemma upperSum_sub_lowerSum_eq_partitionOscillation {f α : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) :
    upperSum P f α - lowerSum P f α =
      partitionOscillation P f α := by
  unfold partitionOscillation upperSum lowerSum
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
    BddAbove.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
      hAbove
  have hcellBelow : BddBelow (f '' cell) :=
    BddBelow.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
      hBelow
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

lemma abs_sub_le_cell_length_of_mem_subinterval {a b x y : ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hx : x ∈ Partition.subinterval P i)
    (hy : y ∈ Partition.subinterval P i) :
    |x - y| ≤ P.pts i.succ - P.pts i.castSucc := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith


lemma partition_length_le_mesh_core {a b : ℝ}
    (P : Partition a b) (i : Fin P.n) :
    P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup'
    (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
    (by simp : i ∈ (Finset.univ : Finset (Fin P.n)))



/--
The Darboux upper/lower gap can be made arbitrarily small on `[a, b]`.

This auxiliary predicate says that, for every tolerance `eps > 0`, there is a
mesh bound `δ > 0` such that every partition `P` of `[a, b]` with
`P.mesh < δ` satisfies

`upperSum P f α - lowerSum P f α < eps`.

In other words, the upper and lower Riemann--Stieltjes sums become uniformly
close as the mesh of the partition tends to zero.

This is a useful intermediate condition in Darboux-style integrability proofs.
It does not by itself specify the value of the integral; rather, it expresses
that the Darboux gap collapses to zero.  In the proof of the identity-integrator
case, this predicate is established for continuous functions by using uniform
continuity on the compact interval `[a, b]`.
-/
def ClosedIntervalDarbouxGapSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
    P.mesh < δ →
      upperSum P f α - lowerSum P f α < eps


/-! ## A Nat bridge for adjacent-interval intervalIntegral lemmas -/

/--
`ptNat P k` is the `k`-th partition point, read through a natural-number
index.  It is used only to invoke Mathlib telescoping lemmas over
`Finset.range P.n`.
-/
private noncomputable def ptNat {a b : ℝ} (P : Partition a b) (k : ℕ) : ℝ :=
  if hk : k ≤ P.n then
    P.pts ⟨k, Nat.lt_succ_of_le hk⟩
  else
    P.pts (Fin.last P.n)

private lemma ptNat_zero {a b : ℝ} (P : Partition a b) :
    ptNat P 0 = a := by
  unfold ptNat
  rw [dif_pos (Nat.zero_le P.n)]
  simpa using P.pts_start

private lemma ptNat_last {a b : ℝ} (P : Partition a b) :
    ptNat P P.n = b := by
  unfold ptNat
  rw [dif_pos le_rfl]
  have hfin :
      (⟨P.n, Nat.lt_succ_self P.n⟩ : Fin (P.n + 1)) = Fin.last P.n := by
    ext
    simp
  simpa [hfin] using P.pts_end

private lemma ptNat_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P k = P.pts (Fin.castSucc (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (le_of_lt hk)]
  congr


private lemma ptNat_succ_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P (k + 1) = P.pts (Fin.succ (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (Nat.succ_le_of_lt hk)]
  congr

/--
The sum of the lengths of all subintervals in a partition of `[a, b]` is `b - a`.

For a partition

`a = x₀ < x₁ < ... < xₙ = b`,

this lemma proves the telescoping identity

`∑ᵢ (xᵢ₊₁ - xᵢ) = b - a`.

In the formalization, subintervals are indexed by `i : Fin P.n`, so the `i`-th
length is written as

`P.pts i.succ - P.pts i.castSucc`.

The proof uses the auxiliary Nat-indexed function `ptNat P : ℕ → ℝ` in order to
apply Mathlib's Nat-indexed telescoping lemma `Finset.sum_Ico_sub`.  The bridge
lemmas `ptNat_of_lt`, `ptNat_succ_of_lt`, `ptNat_zero`, and `ptNat_last` identify
the Nat-indexed endpoints with the original Fin-indexed partition points.
-/
lemma partition_length_sum {a b : ℝ} (P : Partition a b) :
    (∑ i : Fin P.n, (P.pts i.succ - P.pts i.castSucc)) = b - a := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  have htel0 := Finset.sum_Ico_sub (ptNat P) (Nat.zero_le P.n)
  have hIco : Finset.Ico 0 P.n = Finset.range P.n := by
    ext k
    simp
  rw [hIco] at htel0
  have htel :
      (∑ k ∈ Finset.range P.n, (ptNat P (k + 1) - ptNat P k)) = b - a := by
    simpa [ptNat_zero, ptNat_last] using htel0
  trans (∑ k ∈ Finset.range P.n, (ptNat P (k + 1) - ptNat P k))
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < P.n := Finset.mem_range.mp hk
    rw [ptNat_succ_of_lt P hklt, ptNat_of_lt P hklt]
    simp [hklt]
  · exact htel



/-! ## Source hypotheses for the theorem -/

/--
A convenient constructor for the basic source hypotheses of the
Riemann--Stieltjes integral.

If `a < b`, the integrand `f` is continuous on the compact interval `[a, b]`,
and the integrator `α` is monotone on all of `ℝ`, then the standing
`SourceHypotheses a b f α` hold.

The boundedness assumptions for `f` follow from compactness: a continuous
function on `Set.Icc a b` has compact image, hence its image is both bounded
above and bounded below.  The monotonicity assumption for `α` is restricted from
global monotonicity to monotonicity on `[a, b]` by `Monotone.monotoneOn`.

This lemma is used to package the hypotheses needed for the tagged
Riemann--Stieltjes limit in the proof of the differentiable-integrator reduction.
-/
theorem sourceHypotheses_of_continuous_derivative_integrator {f α : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : Monotone α) :
    SourceHypotheses a b f α := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact (isCompact_Icc.image_of_continuousOn hf).bddAbove
  · exact (isCompact_Icc.image_of_continuousOn hf).bddBelow
  · exact hαmono.monotoneOn (Set.Icc a b)



/--
The product integrand `x ↦ f x * α' x` is continuous on `[a, b]` whenever both
factors are continuous there.

In the differentiable-integrator reduction theorem, the ordinary Riemann
integral that appears on the right-hand side has integrand

`fun x => f x * α' x`.

This lemma packages the standard continuity fact needed to treat that function
as an interval-integrable function with respect to the identity integrator:
continuity on `Set.Icc a b` is closed under pointwise multiplication.
-/
theorem derivative_integrand_continuousOn {f α' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    ContinuousOn (fun x => f x * α' x) (Set.Icc a b) :=
  hf.mul hα'cont


/--
A continuous function on the compact interval `[a, b]` admits a positive uniform
absolute-value bound.

More precisely, if `f` is continuous on `Set.Icc a b`, then there exists a real
constant `C > 0` such that

`|f x| ≤ C`

for every `x ∈ Set.Icc a b`.

The proof uses compactness of `Set.Icc a b`: the image of `[a, b]` under a
continuous function is bounded above and bounded below.  The auxiliary lemma
`exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow` then combines these one-sided
bounds into a single positive bound on `|f|`.

This estimate is used later to control the error between the tagged
Riemann--Stieltjes sum for `(f, α)` and the tagged sum for
`(fun x => f x * α' x, id)`.
-/
theorem exists_pos_abs_bound_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C := by
  exact exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
    (isCompact_Icc.image_of_continuousOn hf).bddAbove
    (isCompact_Icc.image_of_continuousOn hf).bddBelow

/--
A short local wrapper for
`DarbouxRS.tag_mem_Icc_of_tagsInPartition_core`.

The existing Darboux helper theorem says that if `tagsInPartition P tags` holds,
then each tag `tags i` belongs to the global interval `[a, b]`.  This follows
because each tag lies in its own partition subinterval, and every partition
subinterval is contained in `[a, b]`.

This wrapper introduces the shorter name `tag_mem_Icc` for readability in the
proof of Theorem 1.4, where this fact is used repeatedly to apply global
hypotheses such as bounds on `f` or uniform continuity of `α'`.
-/
lemma tag_mem_Icc {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags)
    (i : Fin P.n) :
    tags i ∈ Set.Icc a b :=
  DarbouxRS.tag_mem_Icc_of_tagsInPartition_core P htags i


/-! ## MVT point in each partition cell -/

/--
Mean-value theorem on a single subinterval, expressed using the prescribed
derivative function `α'`.

Assume `u < v`, the small interval `[u, v]` is contained in the ambient interval
`[a, b]`, and `α` has derivative `α' x` at every point `x ∈ [a, b]`.  Then there
exists an interior point `c ∈ (u, v)` such that

`α' c = (α v - α u) / (v - u)`.

In other words, on the subinterval `[u, v]`, the instantaneous rate of change
of `α` at some interior point equals the average rate of change of `α` across
the endpoints.

This is the analytic heart of the differentiable-integrator reduction.  When
`[u, v]` is one cell `[xᵢ, xᵢ₊₁]` of a partition, this theorem produces a point
`cᵢ ∈ (xᵢ, xᵢ₊₁)` such that

`α xᵢ₊₁ - α xᵢ = α' cᵢ * (xᵢ₊₁ - xᵢ)`.

That identity allows each Riemann--Stieltjes increment `Δαᵢ` to be compared with
the ordinary length increment `Δxᵢ` weighted by the derivative `α'`.

The proof is a direct application of Mathlib's mean value theorem
`exists_hasDerivAt_eq_slope`.  The global derivative hypothesis on `[a, b]` is
restricted to `[u, v]` using `hsub`; differentiability on the open interval gives
the MVT hypothesis, and differentiability implies the required continuity on the
closed interval.
-/
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



/--
Mean-value theorem on a single subinterval, rewritten in increment form.

The previous lemma `exists_cell_deriv_eq_increment_slope` gives an interior
point `c ∈ (u, v)` such that

`α' c = (α v - α u) / (v - u)`.

This theorem multiplies that identity by the nonzero length `v - u` and obtains

`α v - α u = α' c * (v - u)`.

This form is the one needed for Riemann--Stieltjes sums: it rewrites the
Stieltjes increment

`α v - α u`

as an ordinary interval length

`v - u`

weighted by the derivative value `α' c` at a suitable mean-value point.  Later,
for each partition cell `[xᵢ, xᵢ₊₁]`, this produces

`α xᵢ₊₁ - α xᵢ = α' cᵢ * (xᵢ₊₁ - xᵢ)`.
-/
theorem exists_cell_increment_eq_deriv_mul_length {α α' : ℝ → ℝ} {a b u v : ℝ}
    (huv : u < v)
    (hsub : Set.Icc u v ⊆ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo u v, α v - α u = α' c * (v - u) := by
  rcases exists_cell_deriv_eq_increment_slope huv hsub hderiv with
    ⟨c, hc, hcslope⟩
  refine ⟨c, hc, ?_⟩
  rw [hcslope]
  exact (div_mul_cancel₀ (α v - α u) (sub_ne_zero.mpr huv.ne')).symm


/--
Mean-value point for the `i`-th cell of a partition.

For a partition cell

`[P.pts i.castSucc, P.pts i.succ]`

and an integrator `α` whose derivative is `α'` on the whole interval `[a, b]`,
this theorem produces a point

`c ∈ Set.Ioo (P.pts i.castSucc) (P.pts i.succ)`

such that the Stieltjes increment over the cell is equal to the derivative at
`c` times the ordinary cell length:

`α (P.pts i.succ) - α (P.pts i.castSucc)
  = α' c * (P.pts i.succ - P.pts i.castSucc)`.

This is the cellwise version of the mean value theorem used in the tagged-sum
comparison.  The proof applies `exists_cell_increment_eq_deriv_mul_length` to
the endpoints of the `i`-th partition subinterval.  The strict inequality
between the endpoints comes from `P.strict_mono`, and the fact that the cell is
contained in `[a, b]` comes from
`DarbouxRS.subinterval_subset_Icc_core`.
-/
theorem cell_mvt_point {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo (P.pts i.castSucc) (P.pts i.succ),
      α (P.pts i.succ) - α (P.pts i.castSucc) =
        α' c * (P.pts i.succ - P.pts i.castSucc) := by
  exact exists_cell_increment_eq_deriv_mul_length
    (P.strict_mono Fin.castSucc_lt_succ)
    (DarbouxRS.subinterval_subset_Icc_core P (i := i))
    hαderiv


/--
The mean-value-theorem tag associated to the `i`-th partition cell.

For each cell of the partition, `cell_mvt_point P i hαderiv` proves the
existence of a point

`c ∈ Set.Ioo (P.pts i.castSucc) (P.pts i.succ)`

such that

`α (P.pts i.succ) - α (P.pts i.castSucc)
  = α' c * (P.pts i.succ - P.pts i.castSucc)`.

The definition `cellMVTTag P hαderiv i` chooses one such point using
`Classical.choose`.

This point is not a tag chosen by the user in the tagged Riemann--Stieltjes sum.
Rather, it is an auxiliary tag supplied by the mean value theorem.  It is used to
rewrite each Stieltjes increment `Δαᵢ` as `α' cᵢ * Δxᵢ`, and then compare
`α' cᵢ` with `α' (tags i)` using uniform continuity of `α'`.

The definition is `noncomputable` because it makes an arbitrary classical choice
from an existence theorem.
-/
noncomputable def cellMVTTag {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) : ℝ :=
  Classical.choose (cell_mvt_point P i hαderiv)

theorem cellMVTTag_mem_Ioo {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈
      Set.Ioo (P.pts i.castSucc) (P.pts i.succ) := by
  unfold cellMVTTag
  exact (Classical.choose_spec (cell_mvt_point P i hαderiv)).1

theorem cellMVTTag_increment_eq {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    α (P.pts i.succ) - α (P.pts i.castSucc) =
      α' (cellMVTTag P hαderiv i) *
        (P.pts i.succ - P.pts i.castSucc) := by
  unfold cellMVTTag
  exact (Classical.choose_spec (cell_mvt_point P i hαderiv)).2

theorem cellMVTTag_mem_subinterval {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈ Partition.subinterval P i := by
  exact Set.Ioo_subset_Icc_self (cellMVTTag_mem_Ioo P hαderiv i)

theorem cellMVTTag_mem_Icc {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈ Set.Icc a b :=
  DarbouxRS.subinterval_subset_Icc_core P
    (cellMVTTag_mem_subinterval P hαderiv i)

theorem tag_mvt_distance_le_mesh {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) {tags : Fin P.n → ℝ}
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    |cellMVTTag P hαderiv i - tags i| ≤ P.mesh := by
  have hcell :
      |cellMVTTag P hαderiv i - tags i| ≤
        P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval P
      (cellMVTTag_mem_subinterval P hαderiv i)
      (htags i)
  exact le_trans hcell (partition_length_le_mesh_core P i)

/-! ## Comparison of the two tagged sums -/


/--
Estimate comparing two tagged sums: the Riemann--Stieltjes tagged sum
with integrator `α`, and the ordinary tagged Riemann sum for the product
integrand `f * α'`.

The statement proves that, for a sufficiently fine partition `P`,

`|taggedSum P tags f α
    - taggedSum P tags (fun x => f x * α' x) (fun x => x)|
  ≤ C * eta * (b - a)`.

Here:

* `tags` are arbitrary valid tags for the partition;
* `hαderiv` says that `α` has derivative `α'` on `[a, b]`;
* `hα'osc` says that `α'` oscillates by at most `eta` between points whose
  distance is less than `delta`;
* `hmesh : P.mesh < delta` ensures that points in the same partition cell are
  close enough to apply `hα'osc`;
* `hbound` gives the uniform bound `|f x| ≤ C` on `[a, b]`.

The proof proceeds cell by cell.

For the `i`-th subinterval, the mean value theorem provides an auxiliary point

`c = cellMVTTag P hαderiv i`

inside the cell such that

`α (P.pts i.succ) - α (P.pts i.castSucc)
  = α' c * (P.pts i.succ - P.pts i.castSucc)`.

Thus the difference between the two `i`-th summands becomes

`f (tags i) * (α' c - α' (tags i))
  * (P.pts i.succ - P.pts i.castSucc)`.

Because both `c` and `tags i` lie in the same cell, their distance is bounded by
the mesh of the partition.  Since the mesh is less than `delta`, the oscillation
hypothesis gives

`|α' c - α' (tags i)| ≤ eta`.

The uniform bound on `f` gives

`|f (tags i)| ≤ C`.

Therefore the absolute value of each cellwise error is bounded by

`C * eta * (P.pts i.succ - P.pts i.castSucc)`.

Summing over all cells and using `partition_length_sum`, namely

`∑ᵢ (P.pts i.succ - P.pts i.castSucc) = b - a`,

gives the desired global estimate.

This is the main analytic estimate in the differentiable-integrator reduction:
it shows that, as the mesh tends to zero and `α'` becomes nearly constant on
each small cell, the Riemann--Stieltjes tagged sums for `∫ f dα` are uniformly
close to the ordinary tagged sums for `∫ f(x) α'(x) dx`.
-/
theorem taggedSum_derivative_identity_abs_le {f α α' : ℝ → ℝ} {a b C eta delta : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < delta → |α' x - α' y| ≤ eta)
    (hmesh : P.mesh < delta)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C)
    (hC : 0 ≤ C) :
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)| ≤
      C * eta * (b - a) := by
  have hsum_rewrite :
      taggedSum P tags f α -
          taggedSum P tags (fun x => f x * α' x) (fun x => x) =
        ∑ i : Fin P.n,
          (f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc)) := by
    unfold taggedSum
    rw [← Finset.sum_sub_distrib]
  calc
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)|
        =
      |∑ i : Fin P.n,
          (f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc))| := by
        rw [hsum_rewrite]
    _ ≤ ∑ i : Fin P.n,
          |f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n,
          C * eta * (P.pts i.succ - P.pts i.castSucc) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        let c := cellMVTTag P hαderiv i
        have hc_eq :
            α (P.pts i.succ) - α (P.pts i.castSucc) =
              α' c * (P.pts i.succ - P.pts i.castSucc) := by
          simpa [c] using cellMVTTag_increment_eq P hαderiv i
        have htagI : tags i ∈ Set.Icc a b := tag_mem_Icc P htags i
        have hcI : c ∈ Set.Icc a b := by
          simpa [c] using cellMVTTag_mem_Icc P hαderiv i
        have hdist : |c - tags i| < delta := by
          have hle : |c - tags i| ≤ P.mesh := by
            simpa [c] using tag_mvt_distance_le_mesh P htags hαderiv i
          exact lt_of_le_of_lt hle hmesh
        have hosc : |α' c - α' (tags i)| ≤ eta :=
          hα'osc c hcI (tags i) htagI hdist
        have hfbound : |f (tags i)| ≤ C := hbound (tags i) htagI
        have hlen_nonneg : 0 ≤ P.pts i.succ - P.pts i.castSucc :=
          sub_nonneg.mpr (le_of_lt (P.strict_mono Fin.castSucc_lt_succ))
        have hprod :
            |f (tags i)| * |α' c - α' (tags i)| *
                (P.pts i.succ - P.pts i.castSucc) ≤
              C * eta * (P.pts i.succ - P.pts i.castSucc) := by
          have hmul₁ :
              |f (tags i)| * |α' c - α' (tags i)| ≤ C * eta :=
            mul_le_mul hfbound hosc (abs_nonneg _) hC
          exact mul_le_mul_of_nonneg_right hmul₁ hlen_nonneg
        have hterm_eq :
            f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
                (f (tags i) * α' (tags i)) *
                  (P.pts i.succ - P.pts i.castSucc) =
              f (tags i) * (α' c - α' (tags i)) *
                (P.pts i.succ - P.pts i.castSucc) := by
          rw [hc_eq]
          ring
        rw [hterm_eq, abs_mul, abs_mul, abs_of_nonneg hlen_nonneg]
        exact hprod
    _ = C * eta * (b - a) := by
        rw [← Finset.mul_sum]
        rw [partition_length_sum P]



/-! ## Ordinary interval integral as RS integral with identity integrator -/

/--
On a single partition cell, the ordinary interval integral is bounded between
the lower and upper Darboux cell contributions for the identity integrator.

For the `i`-th subinterval

`[P.pts i.castSucc, P.pts i.succ]`,

this theorem proves

`lowerStep P g i * (P.pts i.succ - P.pts i.castSucc)
  ≤ ∫ x in P.pts i.castSucc..P.pts i.succ, g x`

and

`∫ x in P.pts i.castSucc..P.pts i.succ, g x
  ≤ upperStep P g i * (P.pts i.succ - P.pts i.castSucc)`.

This is the ordinary Riemann-integral analogue of the basic Darboux estimate:
the integral of a function over a cell is bounded below by the infimum of the
function on that cell times the cell length, and bounded above by the supremum
of the function on that cell times the cell length.

The proof proceeds as follows.

* Since partition points are strictly increasing, the cell endpoints satisfy
  `P.pts i.castSucc ≤ P.pts i.succ`.
* The global continuity hypothesis `hg : ContinuousOn g (Set.Icc a b)` restricts
  to continuity on the `i`-th cell, because every partition cell is contained in
  `[a, b]`.
* Continuity on the cell gives interval integrability of `g`.
* The constants `lowerStep P g i` and `upperStep P g i` are also interval
  integrable.
* By the definitions of `lowerStep` and `upperStep`, every value `g x` on the
  cell satisfies

  `lowerStep P g i ≤ g x ≤ upperStep P g i`.

* Applying monotonicity of the interval integral gives

  `∫ lowerStep ≤ ∫ g ≤ ∫ upperStep`.

* Finally, the integral of a constant over `[u, v]` is the constant multiplied
  by `v - u`, yielding the desired lower and upper cell bounds.

This lemma is used to prove that, when the integrator is the identity function,
ordinary interval integrals lie between the lower and upper
Riemann--Stieltjes sums for every partition.
-/
theorem cell_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) (i : Fin P.n) :
    lowerStep P g i * (P.pts i.succ - P.pts i.castSucc) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x ∧
      ∫ x in P.pts i.castSucc..P.pts i.succ, g x ≤
        upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
  have huv : P.pts i.castSucc ≤ P.pts i.succ :=
    le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
  have hgcell :
      ContinuousOn g (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) :=
    hg.mono (DarbouxRS.subinterval_subset_Icc_core P (i := i))
  have hgi : IntervalIntegrable g volume (P.pts i.castSucc) (P.pts i.succ) :=
    ContinuousOn.intervalIntegrable_of_Icc huv hgcell
  have hconstLower :
      IntervalIntegrable (fun _ : ℝ => lowerStep P g i) volume
        (P.pts i.castSucc) (P.pts i.succ) :=
    continuous_const.intervalIntegrable _ _
  have hconstUpper :
      IntervalIntegrable (fun _ : ℝ => upperStep P g i) volume
        (P.pts i.castSucc) (P.pts i.succ) :=
    continuous_const.intervalIntegrable _ _
  have hcellBelow : BddBelow (g '' Partition.subinterval P i) := by
    simpa [Partition.subinterval] using
      (isCompact_Icc.image_of_continuousOn hgcell).bddBelow
  have hcellAbove : BddAbove (g '' Partition.subinterval P i) := by
    simpa [Partition.subinterval] using
      (isCompact_Icc.image_of_continuousOn hgcell).bddAbove
  have hLowerPoint :
      ∀ x ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ),
        lowerStep P g i ≤ g x := by
    intro x hx
    unfold lowerStep
    exact csInf_le hcellBelow ⟨x, hx, rfl⟩
  have hUpperPoint :
      ∀ x ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ),
        g x ≤ upperStep P g i := by
    intro x hx
    unfold upperStep
    exact le_csSup hcellAbove ⟨x, hx, rfl⟩
  have hLowerIntegral :
      (∫ x in P.pts i.castSucc..P.pts i.succ, lowerStep P g i) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x :=
    intervalIntegral.integral_mono_on huv hconstLower hgi hLowerPoint
  have hUpperIntegral :
      (∫ x in P.pts i.castSucc..P.pts i.succ, g x) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, upperStep P g i :=
    intervalIntegral.integral_mono_on huv hgi hconstUpper hUpperPoint
  constructor
  · calc
      lowerStep P g i * (P.pts i.succ - P.pts i.castSucc)
          = ∫ x in P.pts i.castSucc..P.pts i.succ, lowerStep P g i := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]
      _ ≤ ∫ x in P.pts i.castSucc..P.pts i.succ, g x := hLowerIntegral
  · calc
      ∫ x in P.pts i.castSucc..P.pts i.succ, g x
          ≤ ∫ x in P.pts i.castSucc..P.pts i.succ, upperStep P g i :=
            hUpperIntegral
      _ = upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]

/--
The ordinary interval integral over `[a, b]` is the sum of the ordinary interval
integrals over the cells of a partition.

For a partition

`a = x₀ < x₁ < ... < xₙ = b`,

this lemma proves the additivity formula

`∑ᵢ ∫ x in xᵢ..xᵢ₊₁, g x = ∫ x in a..b, g x`.

In the formal statement, the partition cells are indexed by `i : Fin P.n`, so
the `i`-th cell endpoints are written as

`P.pts i.castSucc` and `P.pts i.succ`.

The proof uses the auxiliary Nat-indexed function `ptNat P : ℕ → ℝ`.  This is
only a bridge to Mathlib's interval-integral additivity theorem
`intervalIntegral.sum_integral_adjacent_intervals`, which is stated for
Nat-indexed adjacent endpoints.  The function `ptNat P` agrees with the
partition points on the valid range:

* `ptNat P 0 = a`,
* `ptNat P P.n = b`,
* if `k < P.n`, then `ptNat P k` is the left endpoint of the `k`-th cell,
* if `k < P.n`, then `ptNat P (k + 1)` is the right endpoint of the `k`-th cell.

The proof has three main steps.

1. Show that `g` is interval-integrable on every Nat-indexed cell
   `[ptNat P k, ptNat P (k + 1)]`.  This follows from continuity of `g` on
   `[a, b]`, restricted to each partition cell.

2. Apply `intervalIntegral.sum_integral_adjacent_intervals` to the Nat-indexed
   endpoints `ptNat P`, obtaining

   `∑ k ∈ Finset.range P.n, ∫ x in ptNat P k..ptNat P (k + 1), g x
     = ∫ x in ptNat P 0..ptNat P P.n, g x`.

   Then `ptNat_zero` and `ptNat_last` rewrite the right-hand side to
   `∫ x in a..b, g x`.

3. Convert the original Fin-indexed sum into the Nat-indexed sum using
   `Finset.sum_fin_eq_sum_range` and the bridge lemmas `ptNat_of_lt` and
   `ptNat_succ_of_lt`.

This lemma is marked `private` because it is a proof-engineering helper for the
identity-integrator case, not part of the external Riemann--Stieltjes API.
-/
private lemma partition_integral_sum {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) :
    (∑ i : Fin P.n,
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x) =
      ∫ x in a..b, g x := by
  classical
  rw [Finset.sum_fin_eq_sum_range]

  have hcellIntNat :
      ∀ k < P.n, IntervalIntegrable g volume (ptNat P k) (ptNat P (k + 1)) := by
    intro k hk
    let i : Fin P.n := ⟨k, hk⟩
    have huv : P.pts i.castSucc ≤ P.pts i.succ :=
      le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
    have hgcell :
        ContinuousOn g (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) :=
      hg.mono (DarbouxRS.subinterval_subset_Icc_core P (i := i))
    have hInt :
        IntervalIntegrable g volume (P.pts i.castSucc) (P.pts i.succ) :=
      ContinuousOn.intervalIntegrable_of_Icc huv hgcell

    have hleft : ptNat P k = P.pts i.castSucc := by
      rw [ptNat_of_lt P hk]

    have hright : ptNat P (k + 1) = P.pts i.succ := by
      rw [ptNat_succ_of_lt P hk]


    simpa [hleft, hright] using hInt

  have hsum0 :=
    intervalIntegral.sum_integral_adjacent_intervals hcellIntNat

  have hsum :
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x) =
        ∫ x in a..b, g x := by
    simpa [ptNat_zero, ptNat_last] using hsum0

  trans
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x)
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < P.n := Finset.mem_range.mp hk
    rw [dif_pos hklt]
    rw [ptNat_of_lt P hklt, ptNat_succ_of_lt P hklt]

  · exact hsum


/--
For the identity integrator, the ordinary interval integral lies between the
lower and upper Riemann--Stieltjes sums of any partition.

When the integrator is the identity function `fun x => x`, the
Riemann--Stieltjes increments are ordinary cell lengths:

`(fun x => x) (P.pts i.succ) - (fun x => x) (P.pts i.castSucc)
  = P.pts i.succ - P.pts i.castSucc`.

Thus the lower and upper Riemann--Stieltjes sums become the usual Darboux lower
and upper sums for the ordinary Riemann integral.

This theorem proves that, for every partition `P`,

`lowerSum P g id ≤ ∫ x in a..b, g x ≤ upperSum P g id`.

The proof combines two ingredients.

1. The cellwise estimate
   `cell_integral_between_lower_upper_id`, which says that on each partition
   cell, the ordinary interval integral of `g` is bounded below by the cell
   infimum times the cell length and bounded above by the cell supremum times
   the cell length.

2. The additivity of the interval integral over adjacent partition cells,
   packaged in `partition_integral_sum`:

   `∑ᵢ ∫ x in P.pts i.castSucc..P.pts i.succ, g x
     = ∫ x in a..b, g x`.

Summing the cellwise lower bounds gives the global lower bound, and summing the
cellwise upper bounds gives the global upper bound.

This result is used to show that, for continuous `g`, the ordinary interval
integral `∫ x in a..b, g x` is the Riemann--Stieltjes integral of `g` with
respect to the identity integrator.
-/
theorem partition_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) :
    lowerSum P g (fun x => x) ≤ ∫ x in a..b, g x ∧
      ∫ x in a..b, g x ≤ upperSum P g (fun x => x) := by
  have hsumIntegral := partition_integral_sum hg P
  have hlowerSum :
      (∑ i : Fin P.n,
          lowerStep P g i * (P.pts i.succ - P.pts i.castSucc)) ≤
        ∑ i : Fin P.n,
          ∫ x in P.pts i.castSucc..P.pts i.succ, g x := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact (cell_integral_between_lower_upper_id hg P i).1
  have hupperSum :
      (∑ i : Fin P.n,
          ∫ x in P.pts i.castSucc..P.pts i.succ, g x) ≤
        ∑ i : Fin P.n,
          upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact (cell_integral_between_lower_upper_id hg P i).2
  constructor
  · calc
      lowerSum P g (fun x => x)
          = ∑ i : Fin P.n,
              lowerStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
            unfold lowerSum
            simp
      _ ≤ ∑ i : Fin P.n,
            ∫ x in P.pts i.castSucc..P.pts i.succ, g x := hlowerSum
      _ = ∫ x in a..b, g x := hsumIntegral
  · calc
      ∫ x in a..b, g x
          = ∑ i : Fin P.n,
              ∫ x in P.pts i.castSucc..P.pts i.succ, g x :=
            hsumIntegral.symm
      _ ≤ ∑ i : Fin P.n,
            upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := hupperSum
      _ = upperSum P g (fun x => x) := by
            unfold upperSum
            simp


/--
For a continuous function `g`, the Darboux upper/lower gap for the identity
integrator can be made arbitrarily small by taking sufficiently fine partitions.

More precisely, if `a < b` and `g` is continuous on `[a, b]`, then for every
`eps > 0` there exists `δ > 0` such that every partition `P` with
`P.mesh < δ` satisfies

`upperSum P g (fun x => x) - lowerSum P g (fun x => x) < eps`.

This is the standard Darboux integrability estimate for continuous functions,
specialized to the identity integrator.  Since the integrator is
`fun x => x`, the Riemann--Stieltjes increments are ordinary cell lengths.

The proof uses uniform continuity of `g` on the compact interval `[a, b]`.

The argument is as follows.

1. Choose a small oscillation tolerance

   `eta = eps / (b - a + 1)`.

   This choice guarantees

   `eta * (b - a) < eps`.

2. Since `g` is continuous on the compact interval `[a, b]`, it is uniformly
   continuous there.  Hence there is `δ > 0` such that whenever two points of
   `[a, b]` are within distance `δ`, their `g`-values differ by at most `eta`.

3. If `P.mesh < δ`, then any two points in the same partition cell are within
   distance less than `δ`.  Therefore the oscillation of `g` on each cell is at
   most `eta`, i.e.

   `upperStep P g i - lowerStep P g i ≤ eta`.

4. Multiplying this cellwise oscillation bound by the nonnegative cell length
   and summing over all cells gives

   `partitionOscillation P g id ≤ eta * (b - a)`,

   using `partition_length_sum` to identify the sum of all cell lengths with
   `b - a`.

5. Finally, `upperSum_sub_lowerSum_eq_partitionOscillation` rewrites the
   Darboux gap as `partitionOscillation P g id`, and the estimate
   `eta * (b - a) < eps` finishes the proof.

This theorem is the key step showing that continuous functions are
Riemann--Stieltjes integrable with respect to the identity integrator, with the
ordinary interval integral as the common Darboux limit.
-/
theorem upper_lower_gap_small_continuous_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    ClosedIntervalDarbouxGapSmall a b g (fun x => x) := by
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
      ∀ i : Fin P.n,
        upperStep P g i - lowerStep P g i ≤ eta := by
    intro i
    refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      P i hAbove hBelow ?_
    intro x hx y hy
    have hxI : x ∈ Set.Icc a b :=
      DarbouxRS.subinterval_subset_Icc_core P hx
    have hyI : y ∈ Set.Icc a b :=
      DarbouxRS.subinterval_subset_Icc_core P hy
    have hxy_len : |x - y| ≤ P.pts i.succ - P.pts i.castSucc :=
      abs_sub_le_cell_length_of_mem_subinterval P hx hy
    have hlen_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh :=
      partition_length_le_mesh_core P i
    have hdist : dist x y < δ := by
      simpa [Real.dist_eq] using
        lt_of_le_of_lt (le_trans hxy_len hlen_mesh) hmesh
    exact le_of_lt (by
      simpa [Real.dist_eq] using Hδ x hxI y hyI hdist)
  have hosc_le :
      partitionOscillation P g (fun x => x) ≤ eta * (b - a) := by
    unfold partitionOscillation
    calc
      (∑ i : Fin P.n,
          (upperStep P g i - lowerStep P g i) *
            ((fun x : ℝ => x) (P.pts i.succ) -
              (fun x : ℝ => x) (P.pts i.castSucc)))
          ≤ ∑ i : Fin P.n,
              eta * (P.pts i.succ - P.pts i.castSucc) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hlen_nonneg : 0 ≤ P.pts i.succ - P.pts i.castSucc :=
              sub_nonneg.mpr (le_of_lt (P.strict_mono Fin.castSucc_lt_succ))
            simpa using mul_le_mul_of_nonneg_right (hstep i) hlen_nonneg
      _ = eta * (b - a) := by
            rw [← Finset.mul_sum, partition_length_sum P]
  calc
    upperSum P g (fun x => x) - lowerSum P g (fun x => x)
        = partitionOscillation P g (fun x => x) :=
          upperSum_sub_lowerSum_eq_partitionOscillation P
    _ ≤ eta * (b - a) := hosc_le
    _ < eps := hsmall_eta_span

/--
For a continuous function `g`, the Darboux upper and lower
Riemann--Stieltjes sums with respect to the identity integrator converge to the
ordinary interval integral.

More precisely, if `a < b` and `g` is continuous on `[a, b]`, then

`rsUpperLowerCommonLimit a b g (fun x => x) (∫ x in a..b, g x)`.

Thus, in the Darboux upper/lower-sum formulation, the Riemann--Stieltjes
integral of `g` with respect to the identity function is exactly the ordinary
interval integral of `g`.

The proof has two main ingredients.

1. `partition_integral_between_lower_upper_id` shows that for every partition
   `P`, the ordinary interval integral is squeezed between the lower and upper
   sums:

   `lowerSum P g id ≤ ∫ x in a..b, g x ≤ upperSum P g id`.

2. `upper_lower_gap_small_continuous_id` shows that, for sufficiently fine
   partitions, the Darboux gap

   `upperSum P g id - lowerSum P g id`

   is arbitrarily small.

Combining these two facts gives an epsilon-delta squeeze argument: if the lower
and upper sums are close to each other and the integral lies between them, then
both the lower sum and the upper sum are close to the integral.

The source hypotheses are also packaged here.  The interval condition is `hab`;
boundedness of `g` follows from continuity on the compact interval `[a, b]`; and
the identity integrator is monotone on `[a, b]`.
-/
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
  rcases upper_lower_gap_small_continuous_id hab hg eps heps with
    ⟨δ, hδ_pos, Hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hbetween := partition_integral_between_lower_upper_id hg P
  have hgap := Hδ P hmesh
  constructor
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith


/--
For a continuous function `g`, the tagged Riemann--Stieltjes sums with respect
to the identity integrator converge to the ordinary interval integral.

More precisely, if `a < b` and `g` is continuous on `[a, b]`, then

`rsTaggedCommonLimit a b g (fun x => x) (∫ x in a..b, g x)`.

This theorem is mainly a wrapper/corollary rather than a new analytic estimate.
The substantial Darboux work is done in
`rsUpperLowerCommonLimit_intervalIntegral_id`, which proves that the upper and
lower Riemann--Stieltjes sums with identity integrator converge to the ordinary
interval integral.  The general theorem
`taggedCommonLimit_of_upperLowerCommonLimit` then converts that Darboux
upper/lower common limit into the tagged-sum common limit.

Conceptually, this theorem packages the standard fact that ordinary Riemann
integration is the special case of Riemann--Stieltjes integration with
integrator `id`.  It is useful later because the differentiable-integrator
reduction compares tagged sums for `(f, α)` with tagged sums for
`(fun x => f x * α' x, id)`.
-/
theorem rsTaggedCommonLimit_intervalIntegral_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsTaggedCommonLimit a b g (fun x => x) (∫ x in a..b, g x) :=
  taggedCommonLimit_of_upperLowerCommonLimit
    (rsUpperLowerCommonLimit_intervalIntegral_id hab hg)


/-! ## Transfer from identity integrator to differentiable integrator -/

/--
Transfer theorem from the identity integrator to a differentiable integrator.

This is one of the main steps in the proof of Theorem 1.4.  It says:

If the tagged sums for the ordinary Riemann integral

`∫ f(x) * α'(x) dx`

are known to converge to `L`, expressed as

`rsTaggedCommonLimit a b (fun x => f x * α' x) (fun x => x) L`,

then the tagged Riemann--Stieltjes sums

`∑ᵢ f(tᵢ) * (α xᵢ₊₁ - α xᵢ)`

also converge to the same value `L`, provided `α` is differentiable with
continuous derivative `α'`.

Mathematically, the idea is to compare two tagged sums over the same partition
and the same tags:

* the Riemann--Stieltjes tagged sum

  `taggedSum P tags f α`,

* the ordinary tagged sum for the derivative-weighted integrand

  `taggedSum P tags (fun x => f x * α' x) (fun x => x)`.

For each partition cell `[xᵢ, xᵢ₊₁]`, the mean value theorem gives a point
`cᵢ` in the cell such that

`α xᵢ₊₁ - α xᵢ = α' cᵢ * (xᵢ₊₁ - xᵢ)`.

Therefore the difference between the two `i`-th summands is

`f(tᵢ) * (α' cᵢ - α' tᵢ) * (xᵢ₊₁ - xᵢ)`.

Since `α'` is continuous on the compact interval `[a, b]`, it is uniformly
continuous.  Thus, when the mesh of the partition is small, the mean-value point
`cᵢ` and the tag `tᵢ` lie close to each other, so

`|α' cᵢ - α' tᵢ|`

is small.  Since `f` is continuous on `[a, b]`, it is bounded there by some
constant `C`.  Summing the cellwise estimates gives the bound proved earlier in

`taggedSum_derivative_identity_abs_le`.

The epsilon proof splits the total error into two pieces:

`|taggedSum P tags f α - L|`
`≤ |taggedSum P tags f α - Sid| + |Sid - L|`,

where

`Sid = taggedSum P tags (fun x => f x * α' x) (fun x => x)`.

The first term is made less than `eps / 2` by the mean-value/uniform-continuity
comparison estimate.  The second term is made less than `eps / 2` by the assumed
tagged convergence of the identity-integrator sums.  Hence the
Riemann--Stieltjes tagged sum converges to the same limit `L`.

This theorem is the bridge that converts the known identity-integrator result
for the ordinary interval integral into the desired result for a differentiable
Riemann--Stieltjes integrator.
-/
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
  let Sid : ℝ := taggedSum P tags (fun x => f x * α' x) (fun x => x)
  have hdiff :
      |taggedSum P tags f α - Sid| < eps / 2 := by
    have hle :
        |taggedSum P tags f α - Sid| ≤ C * eta * (b - a) := by
      simpa [Sid] using
        taggedSum_derivative_identity_abs_le
          (f := f) (α := α) (α' := α') (a := a) (b := b)
          (C := C) (eta := eta) (delta := δA)
          P tags htags hαderiv hα'osc hmeshA hCbound (le_of_lt hCpos)
    exact lt_of_le_of_lt hle hdiff_budget
  have hIdClose : |Sid - L| < eps / 2 := by
    simpa [Sid] using HδI P tags htags hmeshI
  have htriangle :
      |taggedSum P tags f α - L| ≤
        |taggedSum P tags f α - Sid| + |Sid - L| := by
    have hdecomp :
        taggedSum P tags f α - L =
          (taggedSum P tags f α - Sid) + (Sid - L) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |taggedSum P tags f α - L|
        ≤ |taggedSum P tags f α - Sid| + |Sid - L| := htriangle
    _ < eps / 2 + eps / 2 := add_lt_add hdiff hIdClose
    _ = eps := by ring


/--
Tagged-sum convergence for the differentiable-integrator reduction.

This is the final technical theorem before extracting the equality of integral
values.  It proves that, if

* `f` is continuous on `[a, b]`,
* `α` is monotone,
* `α` has derivative `α'` on `[a, b]`,
* `α'` is continuous on `[a, b]`,

then the tagged Riemann--Stieltjes sums for `f` with respect to `α` converge to
the ordinary interval integral

`∫ x in a..b, f x * α' x`.

In symbols, it establishes

`rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x)`.

The proof is a composition of two previously established results.

1. First, the product integrand `fun x => f x * α' x` is continuous on `[a, b]`
   by `derivative_integrand_continuousOn`.  Therefore, by
   `rsTaggedCommonLimit_intervalIntegral_id`, its tagged sums with respect to
   the identity integrator converge to the ordinary interval integral:

   `rsTaggedCommonLimit a b (fun x => f x * α' x) (fun x => x)
      (∫ x in a..b, f x * α' x)`.

2. Then `rsTaggedCommonLimit_derivative_of_identity_tagged_limit` transfers this
   tagged limit from the identity integrator to the differentiable integrator
   `α`.  The transfer uses the mean value theorem on each partition cell and
   uniform continuity of `α'` to show that the Riemann--Stieltjes tagged sums
   for `(f, α)` are close to the ordinary tagged sums for `(f * α', id)`.

Thus this theorem packages the analytic content of the reduction

`∫ f dα = ∫ f(x) α'(x) dx`

at the level of tagged-sum convergence.
-/
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

end Thm_1_4



/--
Theorem 1.4: reduction of the Riemann--Stieltjes integral to an ordinary
interval integral when the integrator has a continuous derivative.

Assume that

* `f` is continuous on `[a, b]`,
* `α` is monotone,
* `α` has derivative `α'` at every point of `[a, b]`,
* `α'` is continuous on `[a, b]`,
* `f` is already known to be Riemann--Stieltjes integrable with respect to `α`.

Then the ordinary interval integrand `fun x => f x * α' x` is interval
integrable, and the value of the Riemann--Stieltjes integral is equal to the
ordinary interval integral:

`rsIntegral f α a b hRS = ∫ x in a..b, f x * α' x`.

Mathematically, this is the familiar formula

`∫ f dα = ∫ f(x) α'(x) dx`.

The proof has three major steps.

1. **Ordinary integrability of the right-hand side.**
   Since both `f` and `α'` are continuous on `[a, b]`, their product
   `fun x => f x * α' x` is continuous on `[a, b]`.  Therefore it is
   interval-integrable on `a..b`.

2. **Tagged-sum convergence to the ordinary integral.**
   The technical theorem `Thm_1_4.rsTaggedCommonLimit_integral_deriv` proves

   `rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x)`.

   This is the analytic heart of the argument.  It compares, on each fine
   partition, the Riemann--Stieltjes tagged sum

   `∑ᵢ f(tᵢ) * (α xᵢ₊₁ - α xᵢ)`

   with the ordinary tagged sum

   `∑ᵢ f(tᵢ) * α' tᵢ * (xᵢ₊₁ - xᵢ)`.

   On each cell, the mean value theorem gives a point `cᵢ` such that

   `α xᵢ₊₁ - α xᵢ = α' cᵢ * (xᵢ₊₁ - xᵢ)`.

   Since `α'` is uniformly continuous on the compact interval `[a, b]`, for
   sufficiently small mesh we have `α' cᵢ ≈ α' tᵢ`.  Since `f` is bounded on
   `[a, b]`, the total difference between the two tagged sums tends to zero.
   Hence the Riemann--Stieltjes tagged sums converge to the ordinary integral
   of `f * α'`.

3. **Uniqueness of the tagged limit.**
   The given hypothesis `hRS : RSIntegrable f α a b` provides the tagged-limit
   characterization of the already-defined value

   `rsIntegral f α a b hRS`.

   The previous step gives another tagged limit for the same tagged sums,
   namely `∫ x in a..b, f x * α' x`.  By uniqueness of tagged limits
   (`taggedCommonLimit_unique`), these two values are equal.

The hypothesis `hRS` is included because, in this development, `rsIntegral` is a
choice from an existing `RSIntegrable` witness.  The theorem identifies that
chosen Riemann--Stieltjes value with the ordinary interval integral.
-/
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
    Thm_1_4.strict_interval_of_rsIntegrable hRS
  have hTagged :
      rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) :=
    Thm_1_4.rsTaggedCommonLimit_integral_deriv
      hstrict hf hαmono hαderiv hα'cont
  refine ⟨hInt, ?_⟩
  exact taggedCommonLimit_unique (rsIntegral_spec hRS) hTagged
