import Mathlib

/-
TASK ID: prob_1_3
TYPE: Problem
SOURCE PLAN: 39_chap1_problems
TASK CONTENT:
\textbf{1.3.} Suppose $X$ and $Y$ are independent random variables with Gamma distributions having the same scale parameter:
\begin{enumerate}[label=(\alph*)]
    \item Prove that the sum $X+Y$ is also Gamma distributed with the same scale parameter.
    \item Prove that $X/(X+Y)\sim \operatorname{Beta}(\alpha_1,\alpha_2)$.
    \item Show that the Beta distribution $\operatorname{Beta}(\alpha_1,\alpha_2)$ has expected value $\frac{\alpha_1}{\alpha_1+\alpha_2}$.
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW
open MeasureTheory ProbabilityTheory Real Set Filter Topology Complex

noncomputable section

open scoped ENNReal NNReal

/-- Source-side density for the sum of two independent same-scale Gamma variables. -/
noncomputable def gammaSumConvolutionDensity (α₁ α₂ β : ℝ) : ℝ → ℝ :=
  fun x => ∫ y in Ioo (0 : ℝ) x, gammaPDFReal α₁ β y * gammaPDFReal α₂ β (x - y)

/-- Source-side density for the ratio `X / (X + Y)` obtained from the Gamma joint density
under the change of variables `(u, s) ↦ (u*s, (1-u)*s)`. -/
noncomputable def gammaRatioTransformDensity (α₁ α₂ β : ℝ) : ℝ → ℝ :=
  fun u => ∫ s in Ioi (0 : ℝ),
    s * gammaPDFReal α₁ β (u * s) * gammaPDFReal α₂ β ((1 - u) * s)

/-- The beta density vanishes strictly to the left of its support. -/
lemma betaPDFReal_eq_zero_of_neg {α₁ α₂ u : ℝ} (hu : u < 0) :
    betaPDFReal α₁ α₂ u = 0 := by
  simp [betaPDFReal, hu.not_gt]

/-- The beta density vanishes strictly to the right of its support. -/
lemma betaPDFReal_eq_zero_of_one_lt {α₁ α₂ u : ℝ} (hu : 1 < u) :
    betaPDFReal α₁ α₂ u = 0 := by
  simp [betaPDFReal, not_lt_of_ge hu.le]

/-- The ratio-transform density vanishes strictly to the left of the ratio support. -/
lemma gammaRatioTransformDensity_eq_zero_of_neg {α₁ α₂ β u : ℝ} (hu : u < 0) :
    gammaRatioTransformDensity α₁ α₂ β u = 0 := by
  unfold gammaRatioTransformDensity
  refine integral_eq_zero_of_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hus : u * s < 0 := mul_neg_of_neg_of_pos hu hs
  have hnot : ¬ 0 ≤ u * s := not_le.mpr hus
  simp [gammaPDFReal, hnot]

/-- The ratio-transform density vanishes strictly to the right of the ratio support. -/
lemma gammaRatioTransformDensity_eq_zero_of_one_lt {α₁ α₂ β u : ℝ} (hu : 1 < u) :
    gammaRatioTransformDensity α₁ α₂ β u = 0 := by
  unfold gammaRatioTransformDensity
  refine integral_eq_zero_of_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have h1u : 1 - u < 0 := by linarith
  have hprod : (1 - u) * s < 0 := mul_neg_of_neg_of_pos h1u hs
  have hnot : ¬ 0 ≤ (1 - u) * s := not_le.mpr hprod
  simp [gammaPDFReal, hnot]

/-- Proof-bodied strict-left support case of the Gamma-ratio-to-Beta bridge. -/
lemma gammaRatioTransformDensity_eq_betaPDFReal_of_neg {α₁ α₂ β u : ℝ} (hu : u < 0) :
    gammaRatioTransformDensity α₁ α₂ β u = betaPDFReal α₁ α₂ u := by
  rw [gammaRatioTransformDensity_eq_zero_of_neg hu, betaPDFReal_eq_zero_of_neg hu]

/-- Proof-bodied strict-right support case of the Gamma-ratio-to-Beta bridge. -/
lemma gammaRatioTransformDensity_eq_betaPDFReal_of_one_lt {α₁ α₂ β u : ℝ} (hu : 1 < u) :
    gammaRatioTransformDensity α₁ α₂ β u = betaPDFReal α₁ α₂ u := by
  rw [gammaRatioTransformDensity_eq_zero_of_one_lt hu, betaPDFReal_eq_zero_of_one_lt hu]

/-- The Gamma density vanishes strictly to the left of its support. -/
lemma gammaPDFReal_eq_zero_of_neg {α β x : ℝ} (hx : x < 0) :
    gammaPDFReal α β x = 0 := by
  have hnot : ¬0 ≤ x := not_le.mpr hx
  simp [gammaPDFReal, hnot]

/-- The open-interval Gamma convolution density vanishes strictly to the left of support. -/
lemma gammaSumConvolutionDensity_eq_zero_of_neg {α₁ α₂ β x : ℝ} (hx : x < 0) :
    gammaSumConvolutionDensity α₁ α₂ β x = 0 := by
  unfold gammaSumConvolutionDensity
  have hIoo : Ioo (0 : ℝ) x = ∅ := by
    rw [Set.Ioo_eq_empty_iff]
    exact not_lt_of_ge hx.le
  simp [hIoo]

/--
If the Gamma convolution bridge is proved on the strict interior `0 < x`, then it gives
the endpoint-compatible a.e. density statement. The endpoint `x = 0` is intentionally
excluded by the a.e. quantifier because the current pointwise statement is false there.
-/
lemma gammaSumConvolutionDensity_ae_eq_gammaPDFReal_of_pos
    {α₁ α₂ β : ℝ}
    (hpos :
      ∀ x : ℝ,
        0 < x →
          gammaSumConvolutionDensity α₁ α₂ β x =
            gammaPDFReal (α₁ + α₂) β x) :
    gammaSumConvolutionDensity α₁ α₂ β =ᵐ[volume]
      gammaPDFReal (α₁ + α₂) β := by
  have hne_zero : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne_zero] with x hx_ne_zero
  rcases lt_or_gt_of_ne hx_ne_zero with hx_neg | hx_pos
  · rw [gammaSumConvolutionDensity_eq_zero_of_neg hx_neg, gammaPDFReal_eq_zero_of_neg hx_neg]
  · exact hpos x hx_pos

/-- On the strict positive support, the Gamma-convolution integrand reduces to the
standard finite-interval Beta kernel times constants. -/
lemma gammaSumConvolutionDensity_integrand_eq_betaKernel
    {α₁ α₂ β x y : ℝ} (hy : y ∈ Ioo (0 : ℝ) x) :
    gammaPDFReal α₁ β y * gammaPDFReal α₂ β (x - y)
      =
    ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
      Real.exp (-(β * x))) *
      (y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) := by
  have hy0 : 0 < y := hy.1
  have hxy0 : 0 < x - y := by linarith [hy.2]
  rw [gammaPDFReal, if_pos hy0.le, gammaPDFReal, if_pos hxy0.le]
  have hexp : Real.exp (-(β * y)) * Real.exp (-(β * (x - y))) =
      Real.exp (-(β * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (β ^ α₁ / Real.Gamma α₁ * y ^ (α₁ - 1) * Real.exp (-(β * y))) *
        (β ^ α₂ / Real.Gamma α₂ * (x - y) ^ (α₂ - 1) *
          Real.exp (-(β * (x - y))))
        =
        ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
          (Real.exp (-(β * y)) * Real.exp (-(β * (x - y))))) *
          (y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) := by
          ring
    _ = ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
          Real.exp (-(β * x))) *
          (y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) := by
          rw [hexp]

/-- The convolution bridge is reduced to the finite-interval Beta-kernel integral. -/
lemma gammaSumConvolutionDensity_eq_const_mul_betaKernelIntegral
    {α₁ α₂ β x : ℝ} :
    gammaSumConvolutionDensity α₁ α₂ β x =
      ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        Real.exp (-(β * x))) *
        (∫ y in Ioo (0 : ℝ) x, y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) := by
  unfold gammaSumConvolutionDensity
  calc
    (∫ y in Ioo (0 : ℝ) x, gammaPDFReal α₁ β y * gammaPDFReal α₂ β (x - y))
        =
        ∫ y in Ioo (0 : ℝ) x,
          ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
            Real.exp (-(β * x))) *
            (y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
          intro y hy
          exact gammaSumConvolutionDensity_integrand_eq_betaKernel hy
    _ = ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        Real.exp (-(β * x))) *
        (∫ y in Ioo (0 : ℝ) x, y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) := by
          rw [integral_const_mul]

/-- Constant simplification after applying the finite-interval Beta scaling identity. -/
lemma gammaSumConvolutionDensity_betaScale_constants
    {α₁ α₂ β x : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
      ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        Real.exp (-(β * x))) *
        (x ^ (α₁ + α₂ - 1) * ProbabilityTheory.beta α₁ α₂) =
      β ^ (α₁ + α₂) / Real.Gamma (α₁ + α₂) *
        x ^ (α₁ + α₂ - 1) * Real.exp (-(β * x)) := by
  unfold ProbabilityTheory.beta
  have hpow : β ^ α₁ * β ^ α₂ = β ^ (α₁ + α₂) := by
    rw [rpow_add hβ]
  have hΓ₁ : Real.Gamma α₁ ≠ 0 := (Real.Gamma_pos_of_pos hα₁).ne'
  have hΓ₂ : Real.Gamma α₂ ≠ 0 := (Real.Gamma_pos_of_pos hα₂).ne'
  have hΓsum : Real.Gamma (α₁ + α₂) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hα₁ hα₂)).ne'
  field_simp [hΓ₁, hΓ₂, hΓsum]
  ring_nf at hpow ⊢
  rw [hpow]

/--
Gamma convolution strict-interior bridge reduced to the finite-interval Beta scaling
integral. This is the remaining small theorem gap on the Gamma side.
-/
lemma gammaSumConvolutionDensity_eq_gammaPDFReal_of_betaScaleIntegral
    {α₁ α₂ β x : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hx : 0 < x)
    (hscale :
      (∫ y in Ioo (0 : ℝ) x, y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) =
        x ^ (α₁ + α₂ - 1) * ProbabilityTheory.beta α₁ α₂) :
    gammaSumConvolutionDensity α₁ α₂ β x =
      gammaPDFReal (α₁ + α₂) β x := by
  calc
    gammaSumConvolutionDensity α₁ α₂ β x =
      ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        Real.exp (-(β * x))) *
        (∫ y in Ioo (0 : ℝ) x, y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) := by
        exact gammaSumConvolutionDensity_eq_const_mul_betaKernelIntegral
    _ = ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        Real.exp (-(β * x))) *
        (x ^ (α₁ + α₂ - 1) * ProbabilityTheory.beta α₁ α₂) := by
        rw [hscale]
    _ = β ^ (α₁ + α₂) / Real.Gamma (α₁ + α₂) *
        x ^ (α₁ + α₂ - 1) * Real.exp (-(β * x)) := by
        exact gammaSumConvolutionDensity_betaScale_constants hα₁ hα₂ hβ
    _ = gammaPDFReal (α₁ + α₂) β x := by
        rw [gammaPDFReal, if_pos hx.le]

/-- On the positive finite interval, the complex Beta-integral kernel is the real kernel
embedded into `ℂ`. -/
lemma finite_interval_beta_scale_integrand_complex_eq_of_mem_Ioo
    {α₁ α₂ x y : ℝ} (hy : y ∈ Ioo (0 : ℝ) x) :
    (y : ℂ) ^ ((α₁ : ℂ) - 1) * ((x : ℂ) - y) ^ ((α₂ : ℂ) - 1)
      = ((y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1) : ℝ) : ℂ) := by
  have hy0 : 0 < y := hy.1
  have hxy0 : 0 < x - y := by linarith [hy.2]
  have hα₁cast : ((α₁ : ℂ) - 1) = ((α₁ - 1 : ℝ) : ℂ) := by norm_num
  have hα₂cast : ((α₂ : ℂ) - 1) = ((α₂ - 1 : ℝ) : ℂ) := by norm_num
  have hxysub : ((x : ℂ) - y) = ((x - y : ℝ) : ℂ) := by norm_num
  rw [hα₁cast, hα₂cast, hxysub]
  rw [← Complex.ofReal_cpow hy0.le (α₁ - 1),
    ← Complex.ofReal_cpow hxy0.le (α₂ - 1)]
  norm_num [Complex.ofReal_mul]

/-- Taking the real part of Mathlib's complex scaled Beta integral recovers the real
finite-interval kernel integral. -/
lemma finite_interval_beta_scale_integral_complex_re_eq_real_integral
    {α₁ α₂ x : ℝ} :
      (∫ y in Ioo (0 : ℝ) x,
          (y : ℂ) ^ ((α₁ : ℂ) - 1) * ((x : ℂ) - y) ^ ((α₂ : ℂ) - 1)).re =
        (∫ y in Ioo (0 : ℝ) x,
          (y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1) : ℝ)) := by
  have hcomplex :
      (∫ y in Ioo (0 : ℝ) x,
          (y : ℂ) ^ ((α₁ : ℂ) - 1) * ((x : ℂ) - y) ^ ((α₂ : ℂ) - 1)) =
        ∫ y in Ioo (0 : ℝ) x,
          ((y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1) : ℝ) : ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
    intro y hy
    exact finite_interval_beta_scale_integrand_complex_eq_of_mem_Ioo hy
  rw [hcomplex]
  let f : ℝ → ℝ := fun y => y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)
  have hrealcast :
      (∫ y : ℝ, ((f y : ℝ) : ℂ) ∂(volume.restrict (Ioo (0 : ℝ) x))) =
        (↑(∫ y : ℝ, f y ∂(volume.restrict (Ioo (0 : ℝ) x))) : ℂ) := by
    exact integral_ofReal (X := ℝ) (μ := volume.restrict (Ioo (0 : ℝ) x))
      (𝕜 := ℂ) (f := f)
  change (∫ y : ℝ, ((f y : ℝ) : ℂ) ∂(volume.restrict (Ioo (0 : ℝ) x))).re =
    ∫ y : ℝ, f y ∂(volume.restrict (Ioo (0 : ℝ) x))
  rw [hrealcast]
  exact Complex.ofReal_re _

/-- Finite-interval Beta scaling identity for the Gamma convolution kernel. -/
lemma finite_interval_beta_scale_integral
    {α₁ α₂ x : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hx : 0 < x) :
    (∫ y in Set.Ioo (0 : ℝ) x,
        y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) =
      x ^ (α₁ + α₂ - 1) * ProbabilityTheory.beta α₁ α₂ := by
  have hscaled :=
    Complex.betaIntegral_scaled (s := (α₁ : ℂ)) (t := (α₂ : ℂ)) (a := x) hx
  rw [intervalIntegral.integral_of_le hx.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at hscaled
  have hre := congrArg Complex.re hscaled
  rw [finite_interval_beta_scale_integral_complex_re_eq_real_integral] at hre
  have hright :
      ((x : ℂ) ^ ((α₁ : ℂ) + (α₂ : ℂ) - 1) *
          Complex.betaIntegral (α₁ : ℂ) (α₂ : ℂ)).re =
        x ^ (α₁ + α₂ - 1) * ProbabilityTheory.beta α₁ α₂ := by
    have hsumcast :
        ((α₁ : ℂ) + (α₂ : ℂ) - 1) = ((α₁ + α₂ - 1 : ℝ) : ℂ) := by
      norm_num
    have hxpow :
        (x : ℂ) ^ ((α₁ : ℂ) + (α₂ : ℂ) - 1) =
          (↑(x ^ (α₁ + α₂ - 1)) : ℂ) := by
      rw [hsumcast]
      exact (Complex.ofReal_cpow hx.le (α₁ + α₂ - 1)).symm
    rw [hxpow, Complex.re_ofReal_mul]
    rw [ProbabilityTheory.beta_eq_betaIntegralReal α₁ α₂ hα₁ hα₂]
  rw [hright] at hre
  exact hre

/-- Proof-bodied strict-interior Gamma convolution bridge. -/
lemma gammaSumConvolutionDensity_eq_gammaPDFReal_of_pos
    {α₁ α₂ β x : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hx : 0 < x) :
    gammaSumConvolutionDensity α₁ α₂ β x =
      gammaPDFReal (α₁ + α₂) β x :=
  gammaSumConvolutionDensity_eq_gammaPDFReal_of_betaScaleIntegral
    hα₁ hα₂ hβ hx (finite_interval_beta_scale_integral hα₁ hα₂ hx)

/-- The Gamma convolution density agrees a.e. with the Gamma density after adding
shape parameters. -/
lemma gammaSumConvolutionDensity_ae_eq_gammaPDFReal
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
  gammaSumConvolutionDensity α₁ α₂ β =ᵐ[volume]
      gammaPDFReal (α₁ + α₂) β :=
  gammaSumConvolutionDensity_ae_eq_gammaPDFReal_of_pos
    (fun _ hx => gammaSumConvolutionDensity_eq_gammaPDFReal_of_pos hα₁ hα₂ hβ hx)

/-- On the strict ratio support, the Gamma-ratio transform integrand reduces to a
single Gamma-kernel integral times the Beta-shape factors. -/
lemma gammaRatioTransformDensity_integrand_eq_interior
    {α₁ α₂ β u s : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hs0 : 0 < s) :
    s * gammaPDFReal α₁ β (u * s) * gammaPDFReal α₂ β ((1 - u) * s)
      =
    ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
      u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)) *
      (s ^ (α₁ + α₂ - 1) * Real.exp (-(β * s))) := by
  have h1u : 0 < 1 - u := by linarith
  have hus : 0 ≤ u * s := (mul_pos hu0 hs0).le
  have h1us : 0 ≤ (1 - u) * s := (mul_pos h1u hs0).le
  rw [gammaPDFReal, if_pos hus, gammaPDFReal, if_pos h1us]
  have hrpow1 : (u * s) ^ (α₁ - 1) = u ^ (α₁ - 1) * s ^ (α₁ - 1) := by
    rw [mul_rpow hu0.le hs0.le]
  have hrpow2 : ((1 - u) * s) ^ (α₂ - 1) =
      (1 - u) ^ (α₂ - 1) * s ^ (α₂ - 1) := by
    rw [mul_rpow h1u.le hs0.le]
  have hexp : Real.exp (-(β * (u * s))) * Real.exp (-(β * ((1 - u) * s))) =
      Real.exp (-(β * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hrpow1, hrpow2]
  have hs_rpow : s * s ^ (α₁ - 1) * s ^ (α₂ - 1) = s ^ (α₁ + α₂ - 1) := by
    calc
      s * s ^ (α₁ - 1) * s ^ (α₂ - 1)
          = s ^ (1 : ℝ) * s ^ (α₁ - 1) * s ^ (α₂ - 1) := by rw [rpow_one]
      _ = s ^ ((1 : ℝ) + (α₁ - 1)) * s ^ (α₂ - 1) := by
          rw [← rpow_add hs0]
      _ = s ^ (((1 : ℝ) + (α₁ - 1)) + (α₂ - 1)) := by
          rw [← rpow_add hs0]
      _ = s ^ (α₁ + α₂ - 1) := by
          congr 1
          ring
  calc
    s * (β ^ α₁ / Real.Gamma α₁ * (u ^ (α₁ - 1) * s ^ (α₁ - 1)) *
          Real.exp (-(β * (u * s)))) *
        (β ^ α₂ / Real.Gamma α₂ * ((1 - u) ^ (α₂ - 1) * s ^ (α₂ - 1)) *
          Real.exp (-(β * ((1 - u) * s))))
        =
        (β ^ α₁ / Real.Gamma α₁ * (β ^ α₂ / Real.Gamma α₂) *
          u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)) *
          ((s * s ^ (α₁ - 1) * s ^ (α₂ - 1)) *
            (Real.exp (-(β * (u * s))) * Real.exp (-(β * ((1 - u) * s))))) := by
          ring
    _ = (β ^ α₁ / Real.Gamma α₁ * (β ^ α₂ / Real.Gamma α₂) *
          u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)) *
          (s ^ (α₁ + α₂ - 1) * Real.exp (-(β * s))) := by
          rw [hs_rpow, hexp]

/-- The strict-interior ratio bridge reduced to Mathlib's Gamma integral. -/
lemma gammaRatioTransformDensity_eq_const_mul_gammaIntegral
    {α₁ α₂ β u : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hu0 : 0 < u) (hu1 : u < 1) :
    gammaRatioTransformDensity α₁ α₂ β u =
      ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)) *
        ((1 / β) ^ (α₁ + α₂) * Real.Gamma (α₁ + α₂)) := by
  unfold gammaRatioTransformDensity
  let C : ℝ :=
    (β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
      u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)
  calc
    (∫ s in Ioi (0 : ℝ),
        s * gammaPDFReal α₁ β (u * s) * gammaPDFReal α₂ β ((1 - u) * s))
        =
        ∫ s in Ioi (0 : ℝ),
          C * (s ^ (α₁ + α₂ - 1) * Real.exp (-(β * s))) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro s hs
          exact gammaRatioTransformDensity_integrand_eq_interior hu0 hu1 hs
    _ = C * ∫ s in Ioi (0 : ℝ),
          s ^ (α₁ + α₂ - 1) * Real.exp (-(β * s)) := by
          rw [integral_const_mul]
    _ = C * ((1 / β) ^ (α₁ + α₂) * Real.Gamma (α₁ + α₂)) := by
          rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (a := α₁ + α₂) (r := β)
            (add_pos hα₁ hα₂) hβ]
    _ = ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)) *
        ((1 / β) ^ (α₁ + α₂) * Real.Gamma (α₁ + α₂)) := rfl

/-- Constant simplification for the strict-interior ratio bridge. -/
lemma gammaRatioTransformDensity_beta_constants
    {α₁ α₂ β u : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)) *
        ((1 / β) ^ (α₁ + α₂) * Real.Gamma (α₁ + α₂)) =
      (1 / ProbabilityTheory.beta α₁ α₂) * u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1) := by
  unfold ProbabilityTheory.beta
  have hpow : β ^ α₁ * β ^ α₂ * (1 / β) ^ (α₁ + α₂) = 1 := by
    rw [← rpow_add hβ, one_div, inv_rpow hβ.le]
    exact mul_inv_cancel₀ (rpow_pos_of_pos hβ (α₁ + α₂)).ne'
  have hΓ₁ : Real.Gamma α₁ ≠ 0 := (Real.Gamma_pos_of_pos hα₁).ne'
  have hΓ₂ : Real.Gamma α₂ ≠ 0 := (Real.Gamma_pos_of_pos hα₂).ne'
  have hΓsum : Real.Gamma (α₁ + α₂) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hα₁ hα₂)).ne'
  field_simp [hΓ₁, hΓ₂, hΓsum]
  ring_nf at hpow ⊢
  rw [hpow]
  simp

/-- Proof-bodied strict-interior Gamma-ratio-to-Beta bridge. -/
lemma gammaRatioTransformDensity_eq_betaPDFReal_of_interior
    {α₁ α₂ β u : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hu0 : 0 < u) (hu1 : u < 1) :
    gammaRatioTransformDensity α₁ α₂ β u = betaPDFReal α₁ α₂ u := by
  calc
    gammaRatioTransformDensity α₁ α₂ β u =
      ((β ^ α₁ / Real.Gamma α₁) * (β ^ α₂ / Real.Gamma α₂) *
        u ^ (α₁ - 1) * (1 - u) ^ (α₂ - 1)) *
        ((1 / β) ^ (α₁ + α₂) * Real.Gamma (α₁ + α₂)) := by
        exact gammaRatioTransformDensity_eq_const_mul_gammaIntegral hα₁ hα₂ hβ hu0 hu1
    _ = (1 / ProbabilityTheory.beta α₁ α₂) * u ^ (α₁ - 1) *
        (1 - u) ^ (α₂ - 1) := by
        exact gammaRatioTransformDensity_beta_constants hα₁ hα₂ hβ
    _ = betaPDFReal α₁ α₂ u := by
        rw [betaPDFReal, if_pos ⟨hu0, hu1⟩]

/--
If the ratio bridge is proved on the strict interior `0 < u < 1`, then it gives the
endpoint-compatible a.e. density statement. The endpoints `u = 0` and `u = 1` are
intentionally excluded by the a.e. quantifier because the current pointwise statement
uses incompatible endpoint conventions.
-/
lemma gammaRatioTransformDensity_ae_eq_betaPDFReal_of_interior
    {α₁ α₂ β : ℝ}
    (hinterior :
      ∀ u : ℝ,
        0 < u →
          u < 1 →
            gammaRatioTransformDensity α₁ α₂ β u =
              betaPDFReal α₁ α₂ u) :
    gammaRatioTransformDensity α₁ α₂ β =ᵐ[volume] betaPDFReal α₁ α₂ := by
  have hne_zero : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hne_one : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne_zero, hne_one] with u hu_ne_zero hu_ne_one
  by_cases hu_neg : u < 0
  · exact gammaRatioTransformDensity_eq_betaPDFReal_of_neg hu_neg
  by_cases hu_one_lt : 1 < u
  · exact gammaRatioTransformDensity_eq_betaPDFReal_of_one_lt hu_one_lt
  have hzero_lt : 0 < u := lt_of_le_of_ne (not_lt.mp hu_neg) hu_ne_zero.symm
  have hlt_one : u < 1 := lt_of_le_of_ne (not_lt.mp hu_one_lt) hu_ne_one
  exact hinterior u hzero_lt hlt_one

/-- The ratio-transform density agrees a.e. with the Beta density; the endpoint mismatch
is confined to null singleton sets. -/
lemma gammaRatioTransformDensity_ae_eq_betaPDFReal
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    gammaRatioTransformDensity α₁ α₂ β =ᵐ[volume] betaPDFReal α₁ α₂ := by
  exact gammaRatioTransformDensity_ae_eq_betaPDFReal_of_interior
    (fun u hu0 hu1 =>
      gammaRatioTransformDensity_eq_betaPDFReal_of_interior hα₁ hα₂ hβ hu0 hu1)

/-- Endpoint counterexample for the current pointwise Gamma-convolution target. -/
lemma gammaSumConvolutionDensity_half_half_one_at_zero :
    gammaSumConvolutionDensity (1 / 2 : ℝ) (1 / 2 : ℝ) 1 0 = 0 := by
  simp [gammaSumConvolutionDensity]

/-- Mathlib's Gamma density is nonzero at zero for shape one and rate one. -/
lemma gammaPDFReal_one_one_at_zero :
    gammaPDFReal (1 : ℝ) 1 0 = 1 := by
  norm_num [gammaPDFReal]

/-- The current pointwise convolution statement is false at the endpoint `x = 0`. -/
lemma gammaSumConvolutionDensity_half_half_one_at_zero_ne_gammaPDFReal :
    gammaSumConvolutionDensity (1 / 2 : ℝ) (1 / 2 : ℝ) 1 0 ≠
      gammaPDFReal ((1 / 2 : ℝ) + (1 / 2 : ℝ)) 1 0 := by
  norm_num [gammaSumConvolutionDensity, gammaPDFReal]

lemma integral_Ioi_s_mul_exp_neg :
    (∫ s in Ioi (0 : ℝ), s * Real.exp (-s)) = (1 : ℝ) := by
  have h :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1)
      (by norm_num) (by norm_num)
  norm_num [Real.Gamma_add_one, Real.Gamma_one] at h
  simpa using h

lemma integral_Ioi_if_nonneg_s_mul_exp_neg :
    (∫ s in Ioi (0 : ℝ), if 0 ≤ s then s * Real.exp (-s) else 0) = (1 : ℝ) := by
  calc
    (∫ s in Ioi (0 : ℝ), if 0 ≤ s then s * Real.exp (-s) else 0)
        = (∫ s in Ioi (0 : ℝ), s * Real.exp (-s)) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro s hs
            have hs0 : 0 < s := by simpa [Set.mem_Ioi] using hs
            simp [hs0.le]
    _ = 1 := integral_Ioi_s_mul_exp_neg

/-- Endpoint counterexample for the current pointwise Gamma-ratio/Beta target. -/
lemma gammaRatioTransformDensity_one_one_one_at_zero :
    gammaRatioTransformDensity 1 1 1 0 = 1 := by
  unfold gammaRatioTransformDensity
  simp only [gammaPDFReal]
  norm_num
  exact integral_Ioi_if_nonneg_s_mul_exp_neg

/-- The beta density is zero at the left endpoint under its strict support convention. -/
lemma betaPDFReal_one_one_at_zero :
    betaPDFReal 1 1 0 = 0 := by
  norm_num [betaPDFReal]

/-- The current pointwise ratio-to-Beta statement is false at the endpoint `u = 0`. -/
lemma gammaRatioTransformDensity_one_one_one_at_zero_ne_betaPDFReal :
    gammaRatioTransformDensity 1 1 1 0 ≠ betaPDFReal 1 1 0 := by
  rw [gammaRatioTransformDensity_one_one_one_at_zero, betaPDFReal_one_one_at_zero]
  norm_num

/-- The Gamma density obtained in part (a) after adding the two shape parameters. -/
noncomputable def gammaSumDensity (α₁ α₂ β : ℝ) : ℝ → ℝ :=
  gammaSumConvolutionDensity α₁ α₂ β

/-- The Beta density obtained in part (b) for the ratio `X / (X + Y)`. -/
noncomputable def betaRatioDensity (α₁ α₂ β : ℝ) : ℝ → ℝ :=
  gammaRatioTransformDensity α₁ α₂ β

/--
The old all-points density reading of parts (a) and (b). This is retained only as
statement-decision evidence: the lemmas below prove that this candidate is false for
the current density representatives.
-/
def prob_1_3_pointwiseDensityABCandidate (α₁ α₂ β : ℝ) : Prop :=
  (∀ x : ℝ, gammaSumDensity α₁ α₂ β x = gammaPDFReal (α₁ + α₂) β x) ∧
  (∀ u : ℝ, betaRatioDensity α₁ α₂ β u = betaPDFReal α₁ α₂ u)

/--
Minimal endpoint-compatible density statement candidate: the two source density
representatives agree with the Gamma/Beta targets a.e., and part (c) keeps its
theorem-level expectation formula.
-/
def prob_1_3_aeDensityCandidate (α₁ α₂ β : ℝ) : Prop :=
  (gammaSumDensity α₁ α₂ β =ᵐ[volume] gammaPDFReal (α₁ + α₂) β) ∧
  (betaRatioDensity α₁ α₂ β =ᵐ[volume] betaPDFReal α₁ α₂) ∧
  (∫ x, x * betaPDFReal α₁ α₂ x = α₁ / (α₁ + α₂))

/--
Law-level density-measure candidate induced by the a.e. density representatives. This
is a measure-level replacement for the old all-points density reading; it still uses
the source-side convolution and ratio-transform density representatives.
-/
def prob_1_3_lawLevelDensityCandidate (α₁ α₂ β : ℝ) : Prop :=
  ((volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (gammaSumDensity α₁ α₂ β x)) =
    (volume : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (gammaPDFReal (α₁ + α₂) β x))) ∧
  ((volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (betaRatioDensity α₁ α₂ β u)) =
    (volume : Measure ℝ).withDensity (fun u => ENNReal.ofReal (betaPDFReal α₁ α₂ u))) ∧
  (∫ x, x * betaPDFReal α₁ α₂ x = α₁ / (α₁ + α₂))

/-- The Gamma endpoint already refutes the old all-points density candidate. -/
lemma prob_1_3_pointwiseDensityABCandidate_false_gamma_endpoint :
    ¬ prob_1_3_pointwiseDensityABCandidate (1 / 2 : ℝ) (1 / 2 : ℝ) 1 := by
  intro h
  exact gammaSumConvolutionDensity_half_half_one_at_zero_ne_gammaPDFReal (by
    simpa [gammaSumDensity] using h.1 0)

/-- The ratio endpoint separately refutes the old all-points density candidate. -/
lemma prob_1_3_pointwiseDensityABCandidate_false_ratio_endpoint :
    ¬ prob_1_3_pointwiseDensityABCandidate 1 1 1 := by
  intro h
  exact gammaRatioTransformDensity_one_one_one_at_zero_ne_betaPDFReal (by
    simpa [betaRatioDensity] using h.2 0)

/- The beta function ratio identity used for the expectation computation. -/
lemma beta_succ_div_beta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β / beta α β = α / (α + β) := by
  unfold beta
  field_simp
  rw [add_right_comm, Real.Gamma_add_one (by positivity), Real.Gamma_add_one (by positivity)]
  ring

/-- Part (c): the Beta expectation formula. -/
theorem prob_1_3c {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ∫ x, x * betaPDFReal α₁ α₂ x = α₁ / (α₁ + α₂) := by
  show ∫ x, x * betaPDFReal α₁ α₂ x = α₁ / (α₁ + α₂)
  exact
    (by
      suffices
          h_simp :
            ∫ x in Set.Ioo 0 1,
                x * (1 / ProbabilityTheory.beta α₁ α₂) * x ^ (α₁ - 1) * (1 - x) ^ (α₂ - 1) =
              α₁ / (α₁ + α₂) by
        rw [← h_simp, ← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator, betaPDFReal]
        simp only [mul_assoc]
      suffices
          h_simp :
            (∫ x in Set.Ioo (0 : ℝ) 1, x ^ α₁ * (1 - x) ^ (α₂ - 1)) = beta (α₁ + 1) α₂ by
        convert congr_arg (fun x : ℝ => x * (1 / beta α₁ α₂)) h_simp using 1 <;> ring
        ·
          rw [← MeasureTheory.integral_const_mul]
          refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => _
          rw [show x ^ α₁ = x * x ^ (-1 + α₁) by
            rw [← Real.rpow_one_add' hx.1.le]
            ring
            linarith]
          ring
        ·
          have := beta_succ_div_beta hα₁ hα₂
          ring_nf at *
          aesop
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le]
      ·
        have h_beta :
            ∀ u v : ℝ, 0 < u → 0 < v →
              ∫ x in (0)..1, x ^ (u - 1) * (1 - x) ^ (v - 1) = Complex.re (Complex.betaIntegral u v) := by
          intro u v hu hv
          rw [intervalIntegral.integral_of_le zero_le_one]
          simp +decide [Complex.betaIntegral]
          rw [intervalIntegral.integral_of_le zero_le_one]
          convert integral_ofReal.symm
          norm_num [Complex.ofReal_cpow, hu.le, hv.le]
          convert Complex.ofReal_re _
          convert integral_ofReal using 1
          norm_num [Complex.ofReal_cpow, hu.le, hv.le]
          exact
            MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by
              rw [Complex.ofReal_cpow (by linarith [hx.1]), Complex.ofReal_cpow (by linarith [hx.2])]
              norm_num [Complex.ofReal_sub, Complex.ofReal_one]
        convert h_beta (α₁ + 1) α₂ (by positivity) (by positivity) using 1
        · norm_num
        ·
          convert ProbabilityTheory.beta_eq_betaIntegralReal (α₁ + 1) α₂ using 1
          exact ⟨fun h => fun _ _ => h, fun h => h (by positivity) (by positivity)⟩
      · norm_num)

/--
Endpoint-compatible support theorem for the current source/statement issue.

This is deliberately not the original pointwise `prob_1_3` theorem. It records the
local theorem-level progress that remains compatible with the endpoint counterexamples:
strict-interior bridge proofs would be sufficient for the a.e. density statements,
while the Beta expectation part is already proof-bodied.
-/
theorem prob_1_3_endpoint_compatible_ae_support
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hGammaInterior :
      ∀ x : ℝ,
        0 < x →
          gammaSumDensity α₁ α₂ β x =
            gammaPDFReal (α₁ + α₂) β x)
    (hRatioInterior :
      ∀ u : ℝ,
        0 < u →
          u < 1 →
            betaRatioDensity α₁ α₂ β u =
              betaPDFReal α₁ α₂ u) :
    (gammaSumDensity α₁ α₂ β =ᵐ[volume] gammaPDFReal (α₁ + α₂) β) ∧
    (betaRatioDensity α₁ α₂ β =ᵐ[volume] betaPDFReal α₁ α₂) ∧
    (∫ x, x * betaPDFReal α₁ α₂ x = α₁ / (α₁ + α₂)) := by
  refine ⟨?_, ?_, prob_1_3c hα₁ hα₂⟩
  · unfold gammaSumDensity at hGammaInterior ⊢
    exact gammaSumConvolutionDensity_ae_eq_gammaPDFReal_of_pos hGammaInterior
  · unfold betaRatioDensity at hRatioInterior ⊢
    exact gammaRatioTransformDensity_ae_eq_betaPDFReal_of_interior hRatioInterior

/-- Named a.e. density candidate obtained from strict-interior bridge proofs. -/
theorem prob_1_3_aeDensityCandidate_of_strictInterior
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hGammaInterior :
      ∀ x : ℝ,
        0 < x →
          gammaSumDensity α₁ α₂ β x =
            gammaPDFReal (α₁ + α₂) β x)
    (hRatioInterior :
      ∀ u : ℝ,
        0 < u →
          u < 1 →
            betaRatioDensity α₁ α₂ β u =
              betaPDFReal α₁ α₂ u) :
    prob_1_3_aeDensityCandidate α₁ α₂ β :=
  prob_1_3_endpoint_compatible_ae_support hα₁ hα₂ hGammaInterior hRatioInterior

/--
Updated a.e. support theorem after discharging the ratio strict-interior bridge locally:
only the Gamma-convolution strict-interior equality remains as an external premise.
-/
theorem prob_1_3_endpoint_compatible_ae_support_of_gammaInterior
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hGammaInterior :
      ∀ x : ℝ,
        0 < x →
          gammaSumDensity α₁ α₂ β x =
            gammaPDFReal (α₁ + α₂) β x) :
    (gammaSumDensity α₁ α₂ β =ᵐ[volume] gammaPDFReal (α₁ + α₂) β) ∧
    (betaRatioDensity α₁ α₂ β =ᵐ[volume] betaPDFReal α₁ α₂) ∧
    (∫ x, x * betaPDFReal α₁ α₂ x = α₁ / (α₁ + α₂)) := by
  refine ⟨?_, ?_, prob_1_3c hα₁ hα₂⟩
  · unfold gammaSumDensity at hGammaInterior ⊢
    exact gammaSumConvolutionDensity_ae_eq_gammaPDFReal_of_pos hGammaInterior
  · unfold betaRatioDensity
    exact gammaRatioTransformDensity_ae_eq_betaPDFReal hα₁ hα₂ hβ

/-- Named a.e. density candidate requiring only the remaining Gamma interior bridge. -/
theorem prob_1_3_aeDensityCandidate_of_gammaInterior
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hGammaInterior :
      ∀ x : ℝ,
        0 < x →
          gammaSumDensity α₁ α₂ β x =
            gammaPDFReal (α₁ + α₂) β x) :
    prob_1_3_aeDensityCandidate α₁ α₂ β :=
  prob_1_3_endpoint_compatible_ae_support_of_gammaInterior hα₁ hα₂ hβ hGammaInterior

/--
A.e. density candidate reduced to the smallest current Gamma-side gap: the finite
interval Beta scaling identity for each `0 < x`.
-/
theorem prob_1_3_aeDensityCandidate_of_betaScaleIntegral
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hBetaScale :
      ∀ x : ℝ,
        0 < x →
          (∫ y in Ioo (0 : ℝ) x, y ^ (α₁ - 1) * (x - y) ^ (α₂ - 1)) =
            x ^ (α₁ + α₂ - 1) * ProbabilityTheory.beta α₁ α₂) :
    prob_1_3_aeDensityCandidate α₁ α₂ β := by
  refine prob_1_3_aeDensityCandidate_of_gammaInterior hα₁ hα₂ hβ ?_
  intro x hx
  unfold gammaSumDensity
  exact gammaSumConvolutionDensity_eq_gammaPDFReal_of_betaScaleIntegral
    hα₁ hα₂ hβ hx (hBetaScale x hx)

/--
A.e. density candidate after discharging both strict-interior density bridges locally.
The original all-points density reading is still refuted by the endpoint counterexamples
above; this theorem is the endpoint-compatible replacement candidate.
-/
theorem prob_1_3_aeDensityCandidate_of_pos
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    prob_1_3_aeDensityCandidate α₁ α₂ β := by
  refine ⟨?_, ?_, prob_1_3c hα₁ hα₂⟩
  · unfold gammaSumDensity
    exact gammaSumConvolutionDensity_ae_eq_gammaPDFReal hα₁ hα₂ hβ
  · unfold betaRatioDensity
    exact gammaRatioTransformDensity_ae_eq_betaPDFReal hα₁ hα₂ hβ

/-- A.e. equal real density representatives induce the same `withDensity` measure. -/
lemma volume_withDensity_ofReal_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x)) =
      (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (g x)) := by
  exact MeasureTheory.withDensity_congr_ae (hfg.mono fun x hx => by simp [hx])

/-- The a.e. density candidate formally implies the law-level density-measure candidate. -/
theorem prob_1_3_lawLevelDensityCandidate_of_aeDensityCandidate
    {α₁ α₂ β : ℝ}
    (h : prob_1_3_aeDensityCandidate α₁ α₂ β) :
    prob_1_3_lawLevelDensityCandidate α₁ α₂ β := by
  rcases h with ⟨hGamma, hRatio, hMean⟩
  exact ⟨volume_withDensity_ofReal_congr_ae hGamma,
    volume_withDensity_ofReal_congr_ae hRatio, hMean⟩

/--
Law-level candidate obtained from the same strict-interior bridge proofs. This is
still support evidence, not a proof of the original false all-points theorem.
-/
theorem prob_1_3_lawLevelDensityCandidate_of_strictInterior
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hGammaInterior :
      ∀ x : ℝ,
        0 < x →
          gammaSumDensity α₁ α₂ β x =
            gammaPDFReal (α₁ + α₂) β x)
    (hRatioInterior :
      ∀ u : ℝ,
        0 < u →
          u < 1 →
            betaRatioDensity α₁ α₂ β u =
              betaPDFReal α₁ α₂ u) :
    prob_1_3_lawLevelDensityCandidate α₁ α₂ β :=
  prob_1_3_lawLevelDensityCandidate_of_aeDensityCandidate
    (prob_1_3_aeDensityCandidate_of_strictInterior hα₁ hα₂ hGammaInterior hRatioInterior)

/-- Law-level candidate obtained after discharging both strict-interior density bridges locally. -/
theorem prob_1_3_lawLevelDensityCandidate_of_pos
    {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    prob_1_3_lawLevelDensityCandidate α₁ α₂ β :=
  prob_1_3_lawLevelDensityCandidate_of_aeDensityCandidate
    (prob_1_3_aeDensityCandidate_of_pos hα₁ hα₂ hβ)

/-- Problem 1.3, stated at the law/density-measure level.

The older all-points density reading is refuted above at endpoints under the
strict-support density conventions.  This theorem keeps the source-side
convolution and ratio-transform densities, but states the distribution claims
through the induced density measures, where a.e.-equal representatives give the
same law. -/
theorem prob_1_3 {α₁ α₂ β : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    prob_1_3_lawLevelDensityCandidate α₁ α₂ β :=
  prob_1_3_lawLevelDensityCandidate_of_pos hα₁ hα₂ hβ
