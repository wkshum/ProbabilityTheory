import ToyApollo.Output.thm_7_9_truncation_support

open Filter MeasureTheory Set

noncomputable section

/-!
Monotone-convergence support for Theorem 7.9.

This file owns the source step that the nonnegative truncations of `|g|`
increase pointwise to `|g|`, and therefore their Lebesgue-Stieltjes
`lintegral`s converge to the whole-line `lintegral`.
-/

lemma thm_7_9_nat_Icc_subset {n m : ℕ} (hnm : n ≤ m) :
    Icc (-(n : ℝ)) (n : ℝ) ⊆ Icc (-(m : ℝ)) (m : ℝ) := by
  intro x hx
  have hnmR : (n : ℝ) ≤ m := by
    exact_mod_cast hnm
  constructor
  · exact le_trans (neg_le_neg hnmR) hx.1
  · exact le_trans hx.2 hnmR

lemma thm_7_9_abs_trunc_nonneg (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ thm_7_9_trunc (fun y => |g y|) n x := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · simp [thm_7_9_trunc, hx]
  · simp [thm_7_9_trunc, hx]

theorem thm_7_9_abs_trunc_monotone (g : ℝ → ℝ) (x : ℝ) :
    Monotone (fun n : ℕ => thm_7_9_trunc (fun y => |g y|) n x) := by
  intro n m hnm
  by_cases hn : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · have hm : x ∈ Icc (-(m : ℝ)) (m : ℝ) :=
      thm_7_9_nat_Icc_subset hnm hn
    simp [thm_7_9_trunc, hn, hm]
  · by_cases hm : x ∈ Icc (-(m : ℝ)) (m : ℝ)
    · simp [thm_7_9_trunc, hn, hm]
    · simp [thm_7_9_trunc, hn, hm]

theorem thm_7_9_ennreal_abs_trunc_monotone (g : ℝ → ℝ) (x : ℝ) :
    Monotone (fun n : ℕ =>
      ENNReal.ofReal (thm_7_9_trunc (fun y => |g y|) n x)) := by
  intro n m hnm
  exact ENNReal.ofReal_le_ofReal
    (thm_7_9_abs_trunc_monotone g x hnm)

theorem thm_7_9_ennreal_abs_trunc_aemeasurable
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) :
    AEMeasurable
      (fun x : ℝ => ENNReal.ofReal
        (thm_7_9_trunc (fun y => |g y|) n x)) μ := by
  exact ((thm_7_9_trunc_measurable hg.abs n).ennreal_ofReal).aemeasurable

theorem thm_7_9_ennreal_abs_trunc_tendsto (g : ℝ → ℝ) (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal (thm_7_9_trunc (fun y => |g y|) n x))
      atTop (nhds (ENNReal.ofReal |g x|)) := by
  have hEq :
      (fun _ : ℕ => ENNReal.ofReal |g x|) =ᶠ[atTop]
        fun n : ℕ =>
          ENNReal.ofReal (thm_7_9_trunc (fun y => |g y|) n x) :=
    (thm_7_9_trunc_eventually_eq_self (fun y => |g y|) x).mono
      fun _ hn => by simp [hn]
  exact Filter.Tendsto.congr' hEq tendsto_const_nhds

theorem thm_7_9_lintegral_abs_trunc_tendsto
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ x : ℝ,
          ENNReal.ofReal (thm_7_9_trunc (fun y => |g y|) n x) ∂μ)
      atTop
      (nhds (∫⁻ x : ℝ, ENNReal.ofReal |g x| ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone ?hmeas ?hmono ?htendsto
  · intro n
    exact thm_7_9_ennreal_abs_trunc_aemeasurable μ hg n
  · filter_upwards with x
    exact thm_7_9_ennreal_abs_trunc_monotone g x
  · filter_upwards with x
    exact thm_7_9_ennreal_abs_trunc_tendsto g x

/-- A finite absolute truncation has Lebesgue-Stieltjes integral bounded by the
whole-line absolute integral. -/
theorem thm_7_9_integral_abs_trunc_le_integral_abs
    (μ : Measure ℝ) {g : ℝ → ℝ}
    (hg : Measurable g)
    (hAbs : Integrable (fun x => |g x|) μ) (n : ℕ) :
    (∫ x : ℝ, thm_7_9_trunc (fun y => |g y|) n x ∂μ) ≤
      ∫ x : ℝ, |g x| ∂μ := by
  have hMeas : Measurable (thm_7_9_trunc (fun y => |g y|) n) :=
    thm_7_9_trunc_measurable hg.abs n
  have hNormBound :
      ∀ᵐ x ∂μ, ‖thm_7_9_trunc (fun y => |g y|) n x‖ ≤ |g x| := by
    filter_upwards with x
    simpa [Real.norm_eq_abs, abs_abs] using
      thm_7_9_trunc_abs_le (fun y => |g y|) n x
  have hTruncInt : Integrable (thm_7_9_trunc (fun y => |g y|) n) μ :=
    Integrable.mono' hAbs hMeas.aestronglyMeasurable hNormBound
  refine integral_mono hTruncInt hAbs ?_
  intro x
  have hnon : 0 ≤ thm_7_9_trunc (fun y => |g y|) n x :=
    thm_7_9_abs_trunc_nonneg g n x
  have hle_abs :
      |thm_7_9_trunc (fun y => |g y|) n x| ≤ |g x| := by
    simpa [abs_abs] using thm_7_9_trunc_abs_le (fun y => |g y|) n x
  simpa [abs_of_nonneg hnon] using hle_abs
