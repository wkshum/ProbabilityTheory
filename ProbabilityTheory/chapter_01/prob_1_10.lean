import Mathlib

open MeasureTheory Set

/-
\textbf{1.10.} Let $X$ be a random variable whose value is nonnegative real numbers. Suppose the cdf $F_X(x)=P(X\le x)$ satisfies $x(1-F(x))\to 0$ as $x\to \infty$. Derive the following formula for the expectation of $X$:
\[
E[X]=\int_0^{\infty} (1-F_X(x))\, dx.
\]

In measure-theoretic terms, if `μ` is a probability measure supported on `[0,∞)` with CDF
`F(t) = μ((-∞, t])`, then `1 - F(t) = μ((t, ∞)) = μ(Ioi t)`, so the formula reads:

  `∫ x ∂μ = ∫ t in (0,∞), μ(Ioi t).toReal`

This is an instance of the layer-cake / Cavalieri's principle / tail-probability formula.
-/
theorem prob_1_10
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio 0) = 0)
    (hboundary :
      Filter.Tendsto (fun x : ℝ => x * (1 - (μ (Iic x)).toReal)) Filter.atTop
        (nhds 0)) :
    ∫ x, x ∂μ = ∫ t in Ioi 0, (μ (Ioi t)).toReal := by
  convert MeasureTheory.integral_eq_lintegral_of_nonneg_ae _ _ using 1;
  · convert MeasureTheory.integral_eq_lintegral_of_nonneg_ae _ _ using 1;
    · rw [ MeasureTheory.lintegral_eq_lintegral_meas_lt ];
      · simp +decide [ Set.Ioi_def ];
      · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hsupp ] with x hx using le_of_not_gt hx;
      · exact measurable_id.aemeasurable;
    · exact Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg;
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.ennreal_toReal _;
      convert ( Antitone.measurable ( show Antitone fun t => μ ( Set.Ioi t ) from fun x y hxy => MeasureTheory.measure_mono <| Set.Ioi_subset_Ioi hxy ) ) using 1;
  · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hsupp ] with x hx using le_of_not_gt hx;
  · exact measurable_id.aestronglyMeasurable
