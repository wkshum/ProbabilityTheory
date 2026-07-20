import ToyApollo.Output.thm_7_9_truncation_support

open Filter MeasureTheory Set

noncomputable section

/-!
Dominated-convergence support for the signed truncations in Theorem 7.9.

This file owns only the Lebesgue-Stieltjes DCT step: if `|g|` is integrable,
then the integrals of the symmetric truncations of `g` converge to the whole
integral of `g`. It does not identify finite LS and RS truncation values.
-/

theorem thm_7_9_integral_trunc_tendsto
    (μ : Measure ℝ) {g : ℝ → ℝ}
    (hg : Measurable g)
    (hAbs : Integrable (fun x => |g x|) μ) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ, thm_7_9_trunc g n x ∂μ)
      atTop
      (nhds (∫ x : ℝ, g x ∂μ)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : ℝ => |g x|) ?hmeas hAbs ?hbound ?hlim
  · intro n
    exact (thm_7_9_trunc_measurable hg n).aestronglyMeasurable
  · intro n
    filter_upwards with x
    simpa [Real.norm_eq_abs] using thm_7_9_trunc_abs_le g n x
  · filter_upwards with x
    exact thm_7_9_trunc_tendsto_self g x
