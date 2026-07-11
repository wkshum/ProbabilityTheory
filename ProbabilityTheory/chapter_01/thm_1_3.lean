import ProbabilityTheory.chapter_01.def_1_2


open scoped BigOperators Pointwise
open Finset
open Set


noncomputable section


section Thm_1_3_helper

/-
 If α₁ and α₂ are monotonic, then α₁ + α₂ is also monotonic
-/
theorem sourceHypotheses_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    (h₁ : SourceHypotheses a b f α₁)
    (h₂ : SourceHypotheses a b f α₂) :
    SourceHypotheses a b f (fun x => α₁ x + α₂ x) := by
  rcases h₁ with ⟨hab, hAbove, hBelow, hmono₁⟩
  rcases h₂ with ⟨_hab₂, _hAbove₂, _hBelow₂, hmono₂⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  exact add_le_add (hmono₁ hx hy hxy) (hmono₂ hx hy hxy)


/-
Additivity of upper sum when α can be decomposed as α₁ + α₂
-/
theorem upperSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    upperSum P f (fun x => α₁ x + α₂ x) =
      upperSum P f α₁ + upperSum P f α₂ := by
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-
Additivity of lower sum when α can be decomposed as α₁ + α₂
-/
theorem lowerSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    lowerSum P f (fun x => α₁ x + α₂ x) =
      lowerSum P f α₁ + lowerSum P f α₂ := by
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-
Additivity of tagged sum when α can be decomposed as α₁ + α₂
-/
theorem taggedSum_integrator_add {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f α₁ α₂ : ℝ → ℝ) :
    taggedSum P tags f (fun x => α₁ x + α₂ x) =
      taggedSum P tags f α₁ + taggedSum P tags f α₂ := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-
  Additivity of integrator for the common value of upper and lower limit
-/
theorem upperLowerCommonLimit_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a b f α₁ L₁)
    (h₂ : UpperLowerCommonLimit a b f α₂ L₂) :
    UpperLowerCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P hmesh₁
  have hP₂ := H₂ P hmesh₂
  constructor
  · have hadd :
        upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂) := by
      rw [upperSum_integrator_add]
      ring
    calc
      |upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.1 hP₂.1
        simpa using hlt
  · have hadd :
        lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂) := by
      rw [lowerSum_integrator_add]
      ring
    calc
      |lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.2 hP₂.2
        simpa using hlt

/-
  Additivity of integrator for the tagged common limit
-/
theorem taggedCommonLimit_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f α₁ L₁)
    (h₂ : TaggedCommonLimit a b f α₂ L₂) :
    TaggedCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P tags htags hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hadd :
      taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
        (taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂) := by
    rw [taggedSum_integrator_add]
    ring
  calc
    |taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
        |(taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| :=
      abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| <
            eps / 2 + eps / 2 := add_lt_add hP₁ hP₂
      simpa using hlt

end Thm_1_3_helper



section Theorem_1_3




/- # Theorem 1.3 (Existence of witness)
  If f is RS integrable w.r.t. α₁ and α₂ on the interval [a,b],
  then f is RS integral w.r.t. α₁ + α₂.
-/

/--
Constructs the Riemann-Stieltjes integral witness for the sum of two integrators.

Given that `f` is Riemann-Stieltjes integrable with respect to both `α₁` and `α₂`,
this definition bundles the exact limit value `(∫ f dα₁) + (∫ f dα₂)` together with
the formal proofs that both the Darboux (upper/lower) limits and the tagged limits
of `f` integrated against `α₁ + α₂` converge to this combined sum.

This relies on the fact that `Δ(α₁ + α₂)_i = Δ(α₁)_i + Δ(α₂)_i`, which allows the
underlying Riemann-Stieltjes sums to be split cleanly.
-/
noncomputable def rsIntegralWitness_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegralWitness f (fun x => α₁ x + α₂ x) a b where
  value := rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂
  source_limit :=
    upperLowerCommonLimit_integrator_add
      (rsIntegral_source_spec h₁) (rsIntegral_source_spec h₂)
  tagged_limit :=
    taggedCommonLimit_integrator_add
      (rsIntegral_spec h₁) (rsIntegral_spec h₂)





/--
The Riemann-Stieltjes integrability is additive with respect to the integrator.

If `f` is Riemann-Stieltjes integrable with respect to `α₁` and `α₂` on `[a, b]`,
then `f` is also Riemann-Stieltjes integrable with respect to their pointwise
sum `α₁ + α₂` on `[a, b]`.

This theorem wraps the explicit limit constructed in `rsIntegralWitness_integrator_add`
into the existential `Prop` asserting integrability.
-/
noncomputable def rsIntegrable_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegrable f (fun x => α₁ x + α₂ x) a b :=
  ⟨rsIntegralWitness_integrator_add h₁ h₂⟩


/-
 # Theorem 1.3. (additivity)
 `∫ f d(α₁ + α₂) = ∫ f dα₁ + ∫ f dα₂`

Additivity of the Riemann-Stieltjes integral with respect to the integrator. (Theorem 1.3)

If a function `f` is Riemann-Stieltjes integrable with respect to both `α₁` and `α₂`
on `[a, b]`, then it is also integrable with respect to their sum `α₁ + α₂`, and the
integral evaluates exactly to the sum of the individual integrals.

*Proof Idea:*
This theorem mirrors the additivity of the integrand (Theorem 1.2, Part 1).
At the discrete level of Riemann-Stieltjes sums, the intervals distribute perfectly:
`Δ(α₁ + α₂)_i = Δ(α₁)_i + Δ(α₂)_i`. Therefore, any tagged sum over `α₁ + α₂` splits
exactly into a tagged sum over `α₁` plus a tagged sum over `α₂`.

We previously established that the limit of these combined sums converges to
`(∫ f dα₁) + (∫ f dα₂)` via `taggedCommonLimit_integrator_add`. By invoking the
uniqueness of tagged limits (`taggedCommonLimit_unique`), we mathematically seal
the equality.
-/
theorem rsIntegral_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
  rsIntegral f (fun x => α₁ x + α₂ x) a b (rsIntegrable_integrator_add h₁ h₂) =
    rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_add h₁ h₂))
    (taggedCommonLimit_integrator_add (rsIntegral_spec h₁) (rsIntegral_spec h₂))


/--  # Theorem 1.3. (additivity)
Export Theorem 1.3
-/
theorem thm_1_3 {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    ∃ hsum : RSIntegrable f (fun x => α₁ x + α₂ x) a b,
      rsIntegral f (fun x => α₁ x + α₂ x) a b hsum =
        rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact ⟨rsIntegrable_integrator_add h₁ h₂, rsIntegral_integrator_add h₁ h₂⟩


end Theorem_1_3





section integrator_scalar_multiply

/-!
  # Linearity of the Integrator: Scalar Multiplication

  This section establishes that the Riemann-Stieltjes integral is linear with
  respect to scalar multiplication of the integrator. Specifically, it proves that
  ∫ f d(k * α) = k * ∫ f dα.

  ## Mathematical Context
  In the standard textbook development of the Riemann-Stieltjes integral, the
  integrator `α` is required to be monotonically increasing. This guarantees that
  the width of every partition subinterval `Δα_i = α(x_{i+1}) - α(x_i)` is
  non-negative, which is foundational for bounding the upper and lower sums.

  Because of this, multiplying the integrator `α` by a scalar `k` poses a strict
  analytical constraint: *`k` must be non-negative (`k ≥ 0`)*.
  If `k` were negative, `k * α` would become monotonically decreasing, violating
  the core `SourceHypotheses` of the integral.

  ## Contents of this Section
  1. **Helper Lemmas**: Proofs that upper, lower, and tagged sums scale exactly
     by `k`. Furthermore, we prove that `SourceHypotheses` is preserved under
     multiplication by `k ≥ 0`.

  2. **Limit Theorems**: Proofs that the Darboux upper/lower limits and the
     tagged sum limits converge to `k * L`.

  3. **Main Theorems**:
     - `rsIntegrable_integrator_const_mul`: Given `f` is integrable w.r.t `α`,
       it is also integrable w.r.t `k * α`.
     - `rsIntegral_integrator_const_mul_eq`: The formal equality
       evaluating the integral as `k * ∫ f dα`.

  These theorems are essential for defining the expectation of probability
  distributions, as scaling the CDF by probability weights `p_i ≥ 0` natively
  satisfies this non-negative scalar requirement.
-/




/--
If α is monotonic and k ≥ 0, then k * α is also monotonic.
This is required because the RS integral rigidly requires increasing integrators.
-/
lemma sourceHypotheses_integrator_const_mul {a b : ℝ} {f α : ℝ → ℝ} {k : ℝ}
    (hk : 0 ≤ k) (h : SourceHypotheses a b f α) :
    SourceHypotheses a b f (fun x => k * α x) := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  -- Multiplying an inequality by a non-negative constant preserves it
  exact mul_le_mul_of_nonneg_left (hmono hx hy hxy) hk

lemma upperSum_integrator_const_mul {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (k : ℝ) :
    upperSum P f (fun x => k * α x) = k * upperSum P f α := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma lowerSum_integrator_const_mul {a b : ℝ} (P : Partition a b)
    (f α : ℝ → ℝ) (k : ℝ) :
    lowerSum P f (fun x => k * α x) = k * lowerSum P f α := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma taggedSum_integrator_const_mul {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f α : ℝ → ℝ) (k : ℝ) :
    taggedSum P tags f (fun x => k * α x) = k * taggedSum P tags f α := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring



theorem upperLowerCommonLimit_integrator_const_mul {a b k : ℝ} {f α : ℝ → ℝ}
    {L : ℝ} (hk : 0 ≤ k)
    (h : UpperLowerCommonLimit a b f α L) :
    UpperLowerCommonLimit a b f (fun x => k * α x) (k * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_integrator_const_mul hk hs, ?_⟩
  intro eps heps
  let C : ℝ := |k| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg k]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  constructor
  · have hEq : upperSum P f (fun x => k * α x) - k * L = k * (upperSum P f α - L) := by
      rw [upperSum_integrator_const_mul P f α k]
      ring
    rw [hEq, abs_mul]
    have hmul₁ : |k| * |upperSum P f α - L| ≤ |k| * (eps / C) :=
      mul_le_mul_of_nonneg_left (le_of_lt hP.1) (abs_nonneg k)
    have hmul₂ : |k| * (eps / C) < C * (eps / C) := mul_lt_mul_of_pos_right (lt_add_one |k|) hscale
    have hCmul : C * (eps / C) = eps := by field_simp [ne_of_gt hCpos]
    exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)
  · have hEq : lowerSum P f (fun x => k * α x) - k * L = k * (lowerSum P f α - L) := by
      rw [lowerSum_integrator_const_mul P f α k]
      ring
    rw [hEq, abs_mul]
    have hmul₁ : |k| * |lowerSum P f α - L| ≤ |k| * (eps / C) :=
      mul_le_mul_of_nonneg_left (le_of_lt hP.2) (abs_nonneg k)
    have hmul₂ : |k| * (eps / C) < C * (eps / C) := mul_lt_mul_of_pos_right (lt_add_one |k|) hscale
    have hCmul : C * (eps / C) = eps := by field_simp [ne_of_gt hCpos]
    exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

theorem taggedCommonLimit_integrator_const_mul {a b k : ℝ} {f α : ℝ → ℝ}
    {L : ℝ} (hk : 0 ≤ k)
    (h : TaggedCommonLimit a b f α L) :
    TaggedCommonLimit a b f (fun x => k * α x) (k * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_integrator_const_mul hk hs, ?_⟩
  intro eps heps
  let C : ℝ := |k| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg k]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  have hEq : taggedSum P tags f (fun x => k * α x) - k * L = k * (taggedSum P tags f α - L) := by
    rw [taggedSum_integrator_const_mul P tags f α k]
    ring
  rw [hEq, abs_mul]
  have hmul₁ : |k| * |taggedSum P tags f α - L| ≤ |k| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt hP) (abs_nonneg k)
  have hmul₂ : |k| * (eps / C) < C * (eps / C) := mul_lt_mul_of_pos_right (lt_add_one |k|) hscale
  have hCmul : C * (eps / C) = eps := by field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)


/--
The expectation of a discrete random variable is equal to ∑ c_i * p_i.
We choose boundaries `a` and `b` such that all probability masses `c_i`
fall strictly inside the open interval `(a, b)`.
-/
noncomputable def rsIntegralWitness_integrator_const_mul {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    RSIntegralWitness f (fun x => k * α x) a b where
  value := k * rsIntegral f α a b h
  source_limit := upperLowerCommonLimit_integrator_const_mul hk (rsIntegral_source_spec h)
  tagged_limit := taggedCommonLimit_integrator_const_mul hk (rsIntegral_spec h)



/-- The Integrability Prop for scalar multiplication of the integrator. -/
theorem rsIntegrable_integrator_const_mul {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    RSIntegrable f (fun x => k * α x) a b :=
  ⟨rsIntegralWitness_integrator_const_mul hk h⟩

/-- The Evaluation Theorem: ∫ f d(kα) = k ∫ f dα. -/
theorem rsIntegral_integrator_const_mul_eq {f α : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 ≤ k) (h : RSIntegrable f α a b) :
    rsIntegral f (fun x => k * α x) a b (rsIntegrable_integrator_const_mul hk h) =
      k * rsIntegral f α a b h := by
  -- We prove equality by invoking the uniqueness of the tagged limits!
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_const_mul hk h))
    (taggedCommonLimit_integrator_const_mul hk (rsIntegral_spec h))

end integrator_scalar_multiply
