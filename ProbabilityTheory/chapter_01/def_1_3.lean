import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The measure induced by a monotone cdf-like integrator. -/
def cdfMeasure (F : ℝ → ℝ) (hF : Monotone F) : Measure ℝ :=
  hF.stieltjesFunction.measure

/-- The cdf-side expectation exists as a finite Bochner integral. -/
def CdfHasExpectation (F : ℝ → ℝ) (hF : Monotone F) : Prop :=
  Integrable (fun x : ℝ => x) (cdfMeasure F hF)

/-- The cdf-side variance integral exists once the mean value is fixed. -/
def CdfHasVariance (F : ℝ → ℝ) (hF : Monotone F) (m : ℝ) : Prop :=
  Integrable (fun x : ℝ => (x - m) ^ 2) (cdfMeasure F hF)

/-- Expectation defined from a cdf via its Stieltjes measure, guarded by existence. -/
noncomputable def cdfExpectation (F : ℝ → ℝ) (hF : Monotone F)
    (_hMean : CdfHasExpectation F hF) : ℝ :=
  ∫ x, x ∂cdfMeasure F hF

/-- Variance defined from a cdf via its Stieltjes measure, guarded by existence. -/
noncomputable def cdfVariance (F : ℝ → ℝ) (hF : Monotone F) (m : ℝ)
    (_hVar : CdfHasVariance F hF m) : ℝ :=
  ∫ x, (x - m) ^ 2 ∂cdfMeasure F hF

/-- The density-side expectation exists as an ordinary integral. -/
def DensityHasExpectation (fX : ℝ → ℝ) : Prop :=
  Integrable (fun x : ℝ => x * fX x) volume

/-- The density-side variance integral exists once the mean value is fixed. -/
def DensityHasVariance (fX : ℝ → ℝ) (m : ℝ) : Prop :=
  Integrable (fun x : ℝ => (x - m) ^ 2 * fX x) volume

/-- Ordinary expectation formula when the cdf admits a density. -/
noncomputable def expectationFromDensity (fX : ℝ → ℝ)
    (_hMean : DensityHasExpectation fX) : ℝ :=
  ∫ x, x * fX x

/-- Ordinary variance formula when the cdf admits a density. -/
noncomputable def varianceFromDensity (fX : ℝ → ℝ) (m : ℝ)
    (_hVar : DensityHasVariance fX m) : ℝ :=
  ∫ x, (x - m) ^ 2 * fX x

/-- Source-facing statement that the cdf measure has ordinary density `fX`. -/
structure CdfDensity (F : ℝ → ℝ) (hF : Monotone F) (fX : ℝ → ℝ) : Prop where
  measure_eq : cdfMeasure F hF = volume.withDensity (fun x => ENNReal.ofReal (fX x))
  density_aemeasurable : AEMeasurable (fun x => ENNReal.ofReal (fX x)) volume
  density_nonnegative : ∀ᵐ x ∂volume, 0 ≤ fX x

/-- Density simplification of the cdf expectation. -/
theorem cdfExpectation_eq_expectationFromDensity {F fX : ℝ → ℝ} {hF : Monotone F}
    (hMean : CdfHasExpectation F hF)
    (hDensityMean : DensityHasExpectation fX)
    (hDensity : CdfDensity F hF fX) :
    cdfExpectation F hF hMean = expectationFromDensity fX hDensityMean := by
  rw [cdfExpectation, expectationFromDensity, hDensity.measure_eq]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDensity.density_aemeasurable]
  · apply integral_congr_ae
    filter_upwards [hDensity.density_nonnegative] with x hx
    simp [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- Density simplification of the cdf variance around the same mean. -/
theorem cdfVariance_eq_varianceFromDensity {F fX : ℝ → ℝ} {hF : Monotone F} {m : ℝ}
    (hVar : CdfHasVariance F hF m)
    (hDensityVar : DensityHasVariance fX m)
    (hDensity : CdfDensity F hF fX) :
    cdfVariance F hF m hVar = varianceFromDensity fX m hDensityVar := by
  rw [cdfVariance, varianceFromDensity, hDensity.measure_eq]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDensity.density_aemeasurable]
  · apply integral_congr_ae
    filter_upwards [hDensity.density_nonnegative] with x hx
    simp [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- Packaged expectation/variance data associated to a cdf,
with existence guards. -/
structure CdfMomentData (F : ℝ → ℝ) (hF : Monotone F) where
  expectation_integrable : CdfHasExpectation F hF
  expectation : ℝ
  expectation_eq : expectation = cdfExpectation F hF expectation_integrable
  variance_integrable : CdfHasVariance F hF expectation
  variance : ℝ
  variance_eq : variance = cdfVariance F hF expectation variance_integrable

/--  # Definition 1.3 Expectation and variance
Exported definition for Definition 1.3. -/
noncomputable def def_1_3 (F : ℝ → ℝ) (hF : Monotone F)
    (hMean : CdfHasExpectation F hF)
    (hVar : CdfHasVariance F hF (cdfExpectation F hF hMean))
    : CdfMomentData F hF where
  expectation_integrable := hMean
  expectation := cdfExpectation F hF hMean
  expectation_eq := rfl
  variance_integrable := hVar
  variance := cdfVariance F hF (cdfExpectation F hF hMean) hVar
  variance_eq := rfl
