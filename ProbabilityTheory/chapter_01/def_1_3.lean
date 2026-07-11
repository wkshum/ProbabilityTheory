import ProbabilityTheory.chapter_01.def_1_2
import ProbabilityTheory.chapter_01.thm_1_2
import ProbabilityTheory.chapter_01.thm_1_3
import ProbabilityTheory.chapter_01.thm_1_4

/-
  Definition of expectation and variance in terms of Riemann-Stieltjes integral.
-/

noncomputable section

/-- # Definition 1.3
Expectation of a random variable defined via the Riemann-Stieltjes integral
of the identity function `x ↦ x` with respect to the CDF `F` on `[a, b]`.

Note: Although a cumulative distribution function (CDF) is mathematically
always monotonically increasing, we do not explicitly require `Monotone F`
(nor `a < b`) as input arguments. This is because the integrability proof
`h_int : RSIntegrable ...` already relies on `SourceHypotheses`, which
inherently guarantees both `a < b` and `MonotoneOn F (Set.Icc a b)`.
-/
noncomputable def cdfExpectation
    (a b : ℝ) (F : ℝ → ℝ)
    (h_int : RSIntegrable (fun x => x) F a b) : ℝ :=
  rsIntegral (fun x => x) F a b h_int


/-- # Definition 1.3
Variance of a random variable defined via the Riemann-Stieltjes integral
of `(x - μ)²` with respect to the CDF `F` on `[a, b]`, where `μ` is the expectation.
-/
noncomputable def cdfVariance (a b : ℝ) (F : ℝ → ℝ)
    (h_int_exp : RSIntegrable (fun x => x) F a b)
    (h_int_var : RSIntegrable (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b) : ℝ :=
  rsIntegral (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b h_int_var


/--
The variance of a random variable is always non-negative.
This serves as a sanity check for our definition, utilizing the monotonicity
and scalar multiplication theorems of the Riemann-Stieltjes integral.
-/
theorem cdfVariance_nonneg (a b : ℝ) (F : ℝ → ℝ)
    (h_int_exp : RSIntegrable (fun x => x) F a b)
    (h_int_var : RSIntegrable (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b) :
    0 ≤ cdfVariance a b F h_int_exp h_int_var := by
  -- Unfold the definition of variance to expose the integral
  unfold cdfVariance

  -- 1. Construct a proof that the zero function is integrable by multiplying the variance integrand by 0
  have h_zero_int : RSIntegrable (fun x => 0 * (x - cdfExpectation a b F h_int_exp)^2) F a b :=
    rsIntegrable_integrand_const_mul (c := 0) h_int_var

  -- 2. Prove that the integral of this zero function is exactly 0
  have h_zero_eval : rsIntegral (fun x => 0 * (x - cdfExpectation a b F h_int_exp)^2) F a b h_zero_int = 0 := by
    rw [rsIntegral_integrand_const_mul h_int_var]
    exact zero_mul _

  -- 3. Apply your monotonicity theorem: 0 * (x - μ)² ≤ (x - μ)²
  have h_mono : rsIntegral (fun x => 0 * (x - cdfExpectation a b F h_int_exp)^2) F a b h_zero_int ≤
      rsIntegral (fun x => (x - cdfExpectation a b F h_int_exp)^2) F a b h_int_var := by
    apply rsIntegral_integrand_mono h_zero_int h_int_var
    intro x _hx
    rw [zero_mul]
    -- Mathlib's built-in theorem that squares are non-negative
    exact sq_nonneg (x - cdfExpectation a b F h_int_exp)

  -- 4. Substitute `0` into the left side of our inequality
  rw [h_zero_eval] at h_mono
  exact h_mono

end  -- noncomputable section








noncomputable section DiscreteExpectation

namespace DiscreteExpectation

/-- The indicator function 1_{[c, ∞)}(x). Returns 1 if x ≥ c, and 0 otherwise. -/
noncomputable def stepIndicator (c x : ℝ) : ℝ :=
  if c ≤ x then 1 else 0

/--
The cumulative distribution function for a discrete random variable
taking values `c_i` with probabilities `p_i`.
F(x) = ∑ p_i * 1_{[c_i, ∞)}(x)
-/
noncomputable def discreteCDF (m : ℕ) (c p : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin m, p i * stepIndicator (c i) x


-----------------------------------------------------------------------------
-- 1. BASE CASE: The Zero Integrator (Required for Finset Induction)
-----------------------------------------------------------------------------

lemma sourceHypotheses_zero_integrator (a b : ℝ) (hab : a < b) :
    SourceHypotheses a b (fun x => x) (fun _ => 0) := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact ⟨b, by rintro y ⟨x, hx, rfl⟩; exact hx.2⟩
  · exact ⟨a, by rintro y ⟨x, hx, rfl⟩; exact hx.1⟩
  · intro x hx y hy hxy; rfl

theorem taggedCommonLimit_zero (a b : ℝ) (hab : a < b) :
    TaggedCommonLimit a b (fun x => x) (fun _ => 0) 0 := by
  refine ⟨sourceHypotheses_zero_integrator a b hab, ?_⟩
  intro eps heps
  refine ⟨1, zero_lt_one, ?_⟩
  intro P tags htags hmesh
  have hS : taggedSum P tags (fun x => x) (fun x => 0) = 0 := by
    unfold taggedSum; apply Finset.sum_eq_zero; intro i _; ring
  rw [hS, sub_zero, abs_zero]
  exact heps


theorem rsIntegrable_zero (a b : ℝ) (hab : a < b) :
    RSIntegrable (fun x => x) (fun _ => 0) a b := by
  -- 1. Construct the Darboux upper/lower common limit (evaluating to 0)
  have h_ul : UpperLowerCommonLimit a b (fun x => x) (fun x => 0) 0 := by
    refine ⟨sourceHypotheses_zero_integrator a b hab, ?_⟩
    intro eps heps
    -- Since the sum is exactly 0, any delta works. We arbitrarily pick 1.
    refine ⟨1, zero_lt_one, ?_⟩
    intro P _hmesh

    have h_up : upperSum P (fun x => x) (fun x => 0) = 0 := by
      unfold upperSum
      apply Finset.sum_eq_zero
      intro i _
      ring

    have h_low : lowerSum P (fun x => x) (fun x => 0) = 0 := by
      unfold lowerSum
      apply Finset.sum_eq_zero
      intro i _
      ring

    -- Substitute the sums and evaluate |0 - 0| < eps
    rw [h_up, h_low, sub_zero, abs_zero]
    exact ⟨heps, heps⟩

  -- 2. Fetch the Tagged limit (which we already proved evaluates to 0)
  have h_tg : TaggedCommonLimit a b (fun x => x) (fun x => 0) 0 :=
    taggedCommonLimit_zero a b hab

  -- 3. Package them into the `RSIntegralWitness` structure.
  -- The existential `Nonempty` wrapper is satisfied by `⟨...⟩`
  exact ⟨⟨0, h_ul, h_tg⟩⟩

-----------------------------------------------------------------------------
-- 2. FINITE SUM INDUCTION (Bridging Thm 1.3 to arbitrary m)
-----------------------------------------------------------------------------


/-- Integrability of a finite sum of integrators -/
theorem rsIntegrable_integrator_sum_finset {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :  -- Changed to ∀ i
    RSIntegrable (fun x => x) (fun x => ∑ i ∈ s, α i x) a b := by
  induction' s using Finset.induction_on with i s' hi ih
  · simp only [Finset.sum_empty]
    exact rsIntegrable_zero a b hab
  · simp only [Finset.sum_insert hi]
    -- Now we just pass `h i` directly!
    exact rsIntegrable_integrator_add (h i) ih


/-- Proving the limit of the sum is the sum of limits. -/
theorem taggedCommonLimit_integrator_sum_finset {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :
    TaggedCommonLimit a b (fun x => x) (fun x => ∑ i ∈ s, α i x)
      (∑ i ∈ s, rsIntegral (fun x => x) (α i) a b (h i)) := by -- `h i` works perfectly here
  induction' s using Finset.induction_on with i s' hi ih
  · simp only [Finset.sum_empty]
    exact taggedCommonLimit_zero a b hab
  · simp only [Finset.sum_insert hi]
    have H1 := rsIntegral_spec (h i)
    exact taggedCommonLimit_integrator_add H1 ih

/-- Evaluating the finite sum using uniqueness of limits -/
theorem rsIntegral_integrator_sum_finset_eq {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :
    rsIntegral (fun x => x) (fun x => ∑ i ∈ s, α i x) a b
      (rsIntegrable_integrator_sum_finset s α a b hab h) =
    ∑ i ∈ s, rsIntegral (fun x => x) (α i) a b (h i) := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_sum_finset s α a b hab h))
    (taggedCommonLimit_integrator_sum_finset s α a b hab h)

-----------------------------------------------------------------------------
-- 3. THE ANALYTIC STEP FUNCTION HELPER
-----------------------------------------------------------------------------

/--
# Telescoping Sum Strategy for Partitions

This section handles the evaluation of partition increments:
`∑ (F(x_{i+1}) - F(x_i)) = F(b) - F(a)`.

### Mathematical Intuition

In a Riemann-Stieltjes integral, the total weight of the integrator `F` over
the interval `[a, b]` is exactly `F(b) - F(a)`. When we sum the increments
`ΔF_i = F(x_{i+1}) - F(x_i)` over all subintervals in a partition `P`, the
intermediate terms cancel out (telescope), leaving only the boundary points.
For our step function `1_{[c, ∞)}`, this telescoping sum evaluates exactly to
`1 - 0 = 1`, which mathematically represents the total probability mass.

### Formalization Strategy in Lean

Handling telescoping sums directly on `Fin P.n` is notoriously difficult in
dependent type theory. A partition has `n+1` points indexed by `Fin (n+1)`,
but exactly `n` subintervals indexed by `Fin n`. Shifting indices between
`i : Fin n` and `i+1 : Fin (n+1)` creates dependent-type mismatches that
break standard rewrites.

To solve this elegantly, we use the following strategy:
1. *Index Erasing (`g`)*: We define a helper function `g : ℕ → ℝ` that takes
   raw natural numbers. If `i < P.n + 1`, it returns `F(x_i)`; otherwise, it
   returns `0`. This strips away the rigid `Fin` types.
2. *Domain Mapping (`sum_bij`)*: We use `Finset.sum_bij` to map our original
   sum over `Fin P.n` to a standard sum over `Finset.range P.n` (the set of
   natural numbers `0, 1, ..., n-1`).
3. *Mathlib's Heavy Lifting*: Once the sum is over natural numbers, we invoke
   Mathlib's built-in `Finset.sum_range_sub`, which natively computes the
   telescoping sum `g(n) - g(0)`.
4. *Boundary Cleanup*: Finally, we map `g(n)` and `g(0)` back to `F(b)` and
   `F(a)` using the fundamental partition properties `P.pts_end` and `P.pts_start`.
-/


lemma step_mono {c : ℝ} : Monotone (stepIndicator c) := by
  intro x y hxy
  unfold stepIndicator
  split_ifs with h1 h2
  · rfl
  · exfalso; linarith
  · exact zero_le_one
  · rfl

lemma sourceHyp_id_step (c a b : ℝ) (ha : a < c) (hb : c < b) :
    SourceHypotheses a b (fun x => x) (stepIndicator c) := by
  refine ⟨by linarith, ?_, ?_, step_mono.monotoneOn _⟩
  · exact ⟨b, by rintro y ⟨x, hx, rfl⟩; exact hx.2⟩
  · exact ⟨a, by rintro y ⟨x, hx, rfl⟩; exact hx.1⟩


/-- Telescoping sum for partitions -/
lemma partition_telescope {a b : ℝ} (P : Partition a b) (F : ℝ → ℝ) :
    ∑ i : Fin P.n, (F (P.pts i.succ) - F (P.pts i.castSucc)) = F b - F a := by
  let g : ℕ → ℝ := fun i => if h : i < P.n + 1 then F (P.pts ⟨i, h⟩) else 0

  have h_sum : ∑ i : Fin P.n, (F (P.pts i.succ) - F (P.pts i.castSucc)) =
               ∑ i ∈ Finset.range P.n, (g (i + 1) - g i) := by
    apply Finset.sum_bij (fun (i : Fin P.n) _ => i.val)
    · -- 1. hi (mapped elements are in the target finset)
      intro k _
      exact Finset.mem_range.mpr k.isLt
    · -- 2. i_inj (the mapping is injective)
      intro a1 _ a2 _ h
      exact Fin.ext h
    · -- 3. i_surj (the mapping is surjective)
      intro b hb
      refine ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
    · -- 4. h (the terms are equal)
      intro k _
      have h1 : k.val + 1 < P.n + 1 := Nat.succ_lt_succ k.isLt
      have h2 : k.val < P.n + 1 := Nat.lt_succ_of_lt k.isLt

      -- Explicitly change the goal to the unfolded version of `g`
      change F (P.pts k.succ) - F (P.pts k.castSucc) =
        (if h : k.val + 1 < P.n + 1 then F (P.pts ⟨k.val + 1, h⟩) else 0) -
        (if h : k.val < P.n + 1 then F (P.pts ⟨k.val, h⟩) else 0)

      rw [dif_pos h1, dif_pos h2]
      congr

  rw [h_sum, Finset.sum_range_sub]
  have hn : P.n < P.n + 1 := Nat.lt_succ_self P.n
  have h0 : 0 < P.n + 1 := Nat.succ_pos P.n

  -- Explicitly change the goal to the unfolded version of `g`
  change (if h : P.n < P.n + 1 then F (P.pts ⟨P.n, h⟩) else 0) -
         (if h : 0 < P.n + 1 then F (P.pts ⟨0, h⟩) else 0) = F b - F a

  rw [dif_pos hn, dif_pos h0]
  have eq_b : F (P.pts ⟨P.n, hn⟩) = F b := by
    have : (⟨P.n, hn⟩ : Fin (P.n + 1)) = Fin.last P.n := Fin.ext rfl
    rw [this, P.pts_end]
  have eq_a : F (P.pts ⟨0, h0⟩) = F a := by
    have : (⟨0, h0⟩ : Fin (P.n + 1)) = 0 := Fin.ext rfl
    rw [this, P.pts_start]
  rw [eq_b, eq_a]


lemma upperStep_id (P : Partition a b) (i : Fin P.n) :
    upperStep P (fun x => x) i = P.pts i.succ := by
  unfold upperStep Partition.subinterval
  have h_img : (fun x => x) '' Set.Icc (P.pts i.castSucc) (P.pts i.succ) = Set.Icc (P.pts i.castSucc) (P.pts i.succ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [h_img]
  have hab : P.pts i.castSucc ≤ P.pts i.succ := (P.strict_mono (Fin.castSucc_lt_succ)).le
  have H_greatest : IsGreatest (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) (P.pts i.succ) :=
    ⟨⟨hab, le_rfl⟩, fun _ hx => hx.2⟩
  exact IsGreatest.csSup_eq H_greatest

lemma lowerStep_id (P : Partition a b) (i : Fin P.n) :
    lowerStep P (fun x => x) i = P.pts i.castSucc := by
  unfold lowerStep Partition.subinterval
  have h_img : (fun x => x) '' Set.Icc (P.pts i.castSucc) (P.pts i.succ) = Set.Icc (P.pts i.castSucc) (P.pts i.succ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  rw [h_img]
  have hab : P.pts i.castSucc ≤ P.pts i.succ := (P.strict_mono (Fin.castSucc_lt_succ)).le
  have H_least : IsLeast (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) (P.pts i.castSucc) :=
    ⟨⟨le_rfl, hab⟩, fun _ hx => hx.1⟩
  exact IsLeast.csInf_eq H_least

lemma upperStep_mem (P : Partition a b) (i : Fin P.n) :
    upperStep P (fun x => x) i ∈ Partition.subinterval P i := by
  rw [upperStep_id]
  exact ⟨(P.strict_mono (Fin.castSucc_lt_succ )).le, le_rfl⟩

lemma lowerStep_mem (P : Partition a b) (i : Fin P.n) :
    lowerStep P (fun x => x) i ∈ Partition.subinterval P i := by
  rw [lowerStep_id]
  exact ⟨le_rfl, (P.strict_mono (Fin.castSucc_lt_succ )).le⟩


lemma step_bound (P : Partition a b) (c : ℝ) (i : Fin P.n) (x : ℝ)
    (hx : x ∈ Partition.subinterval P i) :
    |x - c| * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) ≤
      P.mesh * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) := by
  let Δ := stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)
  dsimp only [stepIndicator]
  split_ifs with h1 h2
  · ring_nf; rfl
  · rw [sub_zero, mul_one, mul_one]
    have h3 : P.pts i.castSucc < c := not_le.mp h2
    have abs_bound : |x - c| ≤ P.pts i.succ - P.pts i.castSucc :=
      abs_le.mpr ⟨by linarith [hx.1, h1], by linarith [hx.2, h3]⟩

    have H_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
      unfold Partition.mesh
      -- Pass the explicit function so Lean instantly knows the type is ℝ
      exact Finset.le_sup' (fun j => P.pts j.succ - P.pts j.castSucc) (Finset.mem_univ i)

    exact le_trans abs_bound H_mesh
  · exfalso
    have h_strict : P.pts i.castSucc < P.pts i.succ
      := P.strict_mono Fin.castSucc_lt_succ
    linarith

  · ring_nf; rfl



lemma sum_bound_helper (P : Partition a b) (c : ℝ) (ha : a < c) (hb : c < b)
    (vals : Fin P.n → ℝ) (hvals : ∀ i, vals i ∈ Partition.subinterval P i) :
    |∑ i : Fin P.n, vals i * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) - c| ≤ P.mesh := by
  let Δ := fun (i : Fin P.n) => stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)

  have h_tele : ∑ i : Fin P.n, Δ i = 1 := by
    dsimp only [Δ]
    rw [partition_telescope]
    unfold stepIndicator
    have hb_gt : c ≤ b := by linarith
    have ha_lt : ¬(c ≤ a) := by linarith
    simp [hb_gt, ha_lt]

  -- Notice we swapped the sides of the equality!
  have h_c : ∑ i : Fin P.n, c * Δ i = c := by
    rw [← Finset.mul_sum, h_tele, mul_one]

  -- We use `calc` to completely isolate the rewrite steps!
  have h_diff : (∑ i : Fin P.n, vals i * Δ i) - c = ∑ i : Fin P.n, (vals i - c) * Δ i := by
    calc
      (∑ i : Fin P.n, vals i * Δ i) - c
        = (∑ i : Fin P.n, vals i * Δ i) - ∑ i : Fin P.n, c * Δ i := by rw [h_c]
      _ = ∑ i : Fin P.n, (vals i * Δ i - c * Δ i) := by rw [← Finset.sum_sub_distrib]
      _ = ∑ i : Fin P.n, (vals i - c) * Δ i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sub_mul]

  rw [h_diff]

  have h_abs_term : ∀ i : Fin P.n, |(vals i - c) * Δ i| = |vals i - c| * Δ i := by
    intro i
    rw [abs_mul]
    congr 1
    have h_strict : P.pts i.castSucc < P.pts i.succ := P.strict_mono Fin.castSucc_lt_succ
    -- `sub_nonneg.mpr` perfectly translates `A ≤ B` into `0 ≤ B - A`
    have hinc : 0 ≤ Δ i := sub_nonneg.mpr (step_mono h_strict.le)
    exact abs_of_nonneg hinc

  have h_abs : |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |vals i - c| * Δ i := by
    calc
      |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |(vals i - c) * Δ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin P.n, |vals i - c| * Δ i := Finset.sum_congr rfl (fun i _ => h_abs_term i)

  have h_le_mesh : ∑ i : Fin P.n, |vals i - c| * Δ i ≤ ∑ i : Fin P.n, P.mesh * Δ i := by
    apply Finset.sum_le_sum
    intro i _
    exact step_bound P c i (vals i) (hvals i)

  calc
    |∑ i : Fin P.n, (vals i - c) * Δ i| ≤ ∑ i : Fin P.n, |vals i - c| * Δ i := h_abs
    _ ≤ ∑ i : Fin P.n, P.mesh * Δ i := h_le_mesh
    _ = P.mesh := by rw [← Finset.mul_sum, h_tele, mul_one]



theorem taggedCommonLimit_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    TaggedCommonLimit a b (fun x => x) (stepIndicator c) c := by
  refine ⟨sourceHyp_id_step c a b ha hb, ?_⟩
  intro eps heps
  refine ⟨eps, heps, ?_⟩
  intro P tags htags hmesh
  exact lt_of_le_of_lt (sum_bound_helper P c ha hb tags htags) hmesh


/--
 The upper limit and lower limit of a step function, with the step located at `c`,
 are equal,  and is equal to the constant `c`
-/
theorem upperLowerCommonLimit_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    UpperLowerCommonLimit a b (fun x => x) (stepIndicator c) c := by
  refine ⟨sourceHyp_id_step c a b ha hb, ?_⟩
  intro eps heps
  refine ⟨eps, heps, ?_⟩
  intro P hmesh
  constructor
  · exact lt_of_le_of_lt (sum_bound_helper P c ha hb (upperStep P (fun x => x)) (upperStep_mem P)) hmesh
  · exact lt_of_le_of_lt (sum_bound_helper P c ha hb (lowerStep P (fun x => x)) (lowerStep_mem P)) hmesh


/--
  The constant `c` is the witness of the step function at `c`.
-/
noncomputable def rsIntegralWitness_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    RSIntegralWitness (fun x => x) (stepIndicator c) a b where
  value := c
  source_limit := upperLowerCommonLimit_identity_step ha hb
  tagged_limit := taggedCommonLimit_identity_step ha hb

theorem rsIntegrable_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    RSIntegrable (fun x => x) (stepIndicator c) a b :=
  ⟨rsIntegralWitness_identity_step ha hb⟩

/--
 The RS integral of a step function
-/
theorem rsIntegral_identity_step_eq {c a b : ℝ} (ha : a < c) (hb : c < b)
    (h : RSIntegrable (fun x => x) (stepIndicator c) a b) :
    rsIntegral (fun x => x) (stepIndicator c) a b h = c := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec h)
    (taggedCommonLimit_identity_step ha hb)


-----------------------------------------------------------------------------
-- 4. THE MAIN RESULT: Expectation of discreteCDF is a finite sum
-----------------------------------------------------------------------------

/--
The main theorem:
If the integrator is `discreteCDF`, the RS integral is exactly `∑ c_i * p_i`.
-/
theorem discrete_expectation_eq_sum (m : ℕ) (c p : Fin m → ℝ)
    (a b : ℝ) (hab : a < b)
    (hp : ∀ i, 0 ≤ p i)
    (ha : ∀ i, a < c i)
    (hb : ∀ i, c i < b)
    (h_int : RSIntegrable (fun x => x) (discreteCDF m c p) a b) :
    cdfExpectation a b (discreteCDF m c p) h_int = ∑ i : Fin m, c i * p i := by

  -- 1. Prepare the integrability proofs for each term `p_i * 1_c_i`
  have h_step_int : ∀ i, RSIntegrable (fun x => x) (stepIndicator (c i)) a b :=
    fun i => rsIntegrable_identity_step (ha i) (hb i)

  have h_mul_int : ∀ i, RSIntegrable (fun x => x) (fun x => p i * stepIndicator (c i) x) a b :=
    fun i => rsIntegrable_integrator_const_mul (hp i) (h_step_int i)

  -- Now we just pass `h_mul_int` cleanly!
  have h_sum_int : RSIntegrable (fun x => x) (fun x => ∑ i : Fin m, p i * stepIndicator (c i) x) a b :=
    rsIntegrable_integrator_sum_finset Finset.univ _ a b hab h_mul_int

  -- 2. Swap the definition using proof irrelevance
  have h_eq : rsIntegral (fun x => x) (discreteCDF m c p) a b h_int =
              rsIntegral (fun x => x) (fun x => ∑ i : Fin m, p i * stepIndicator (c i) x) a b h_sum_int := by
    congr 1

  unfold cdfExpectation
  rw [h_eq]

  -- 3. Apply the finite sum decomposition theorem (passing h_mul_int)
  rw [rsIntegral_integrator_sum_finset_eq Finset.univ _ a b hab h_mul_int]

  -- 4. Dive into the sum and apply constant multiplication & step evaluation
  apply Finset.sum_congr rfl
  intro i _hi

  have H_mul := rsIntegral_integrator_const_mul_eq (hp i) (h_step_int i)
  rw [H_mul]

  have H_step := rsIntegral_identity_step_eq (ha i) (hb i) (h_step_int i)
  rw [H_step]

  ring


end DiscreteExpectation  -- namespace
end DiscreteExpectation  -- section






section ContinuousExpectation

namespace ContinuousExpectation

/--
Expectation formula for a continuous distribution with differentiable CDF.

Let `F` be the cumulative distribution function on `[a, b]`, and suppose that
`F` is differentiable there with continuous derivative `pdf`.  If the
Riemann--Stieltjes expectation

`cdfExpectation a b F h_int`

is defined as

`∫ x dF(x)`

via the Riemann--Stieltjes integral of the identity function with respect to
`F`, then it is equal to the ordinary interval integral

`∫ x in a..b, x * pdf x`.

In probability notation, this is the familiar formula

`𝔼[X] = ∫ x f_X(x) dx`

when the CDF `F` has density `f_X = F'`.

The proof is a direct application of `thm_1_4` with

* Riemann--Stieltjes integrand `fun x => x`,
* integrator `F`,
* derivative of the integrator `pdf`.

The hypothesis `h_int` is needed because `cdfExpectation` is defined using an
existing `RSIntegrable` witness.
-/
theorem cdfExpectation_eq_integral_pdf
    {a b : ℝ} {F pdf : ℝ → ℝ}
    (hab : a < b)
    (hFmono : Monotone F)
    (hFderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (pdf x) x)
    (hpdf_cont : ContinuousOn pdf (Set.Icc a b))
    (h_int : RSIntegrable (fun x => x) F a b) :
    cdfExpectation a b F h_int = ∫ x in a..b, x * pdf x := by
  have hid_cont : ContinuousOn (fun x : ℝ => x) (Set.Icc a b) :=
    continuous_id.continuousOn
  have h :=
    thm_1_4
      (f := fun x : ℝ => x)
      (α := F)
      (α' := pdf)
      (a := a)
      (b := b)
      (le_of_lt hab)
      hid_cont
      hFmono
      hFderiv
      hpdf_cont
      h_int
  simpa [cdfExpectation] using h.2

/--
Stronger version of `cdfExpectation_eq_integral_pdf`: it also records that the
ordinary density-weighted integrand `fun x => x * pdf x` is interval-integrable.
-/
theorem cdfExpectation_integrable_and_eq_integral_pdf
    {a b : ℝ} {F pdf : ℝ → ℝ}
    (hab : a < b)
    (hFmono : Monotone F)
    (hFderiv : ∀ x ∈ Set.Icc a b, HasDerivAt F (pdf x) x)
    (hpdf_cont : ContinuousOn pdf (Set.Icc a b))
    (h_int : RSIntegrable (fun x => x) F a b) :
    IntervalIntegrable (fun x => x * pdf x) MeasureTheory.volume a b ∧
      cdfExpectation a b F h_int = ∫ x in a..b, x * pdf x := by
  have hid_cont : ContinuousOn (fun x : ℝ => x) (Set.Icc a b) :=
    continuous_id.continuousOn

  have h :
      IntervalIntegrable (fun x => x * pdf x) MeasureTheory.volume a b ∧
        rsIntegral (fun x : ℝ => x) F a b h_int =
          ∫ x in a..b, x * pdf x :=
    thm_1_4
      (f := fun x : ℝ => x)
      (α := F)
      (α' := pdf)
      (a := a)
      (b := b)
      (le_of_lt hab)
      hid_cont
      hFmono
      hFderiv
      hpdf_cont
      h_int

  constructor
  · exact h.1
  · unfold cdfExpectation
    exact h.2




end ContinuousExpectation  -- namespace
end ContinuousExpectation    -- section
