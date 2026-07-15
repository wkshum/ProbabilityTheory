import Mathlib
import ToyApollo.Output.def_4_4_complex_number
import ToyApollo.Output.def_4_4_complex_operations
import ToyApollo.Output.def_4_4_complex_random_variable

/-!
Definition 4.4: polar form for complex numbers and complex random variables.
-/

/-- Radius of a complex number in polar form. -/
noncomputable def complexRadius (z : ℂ) : ℝ :=
  complex_abs z

/-- Argument of a complex number in the principal branch. -/
noncomputable def complexArgument (z : ℂ) : ℝ :=
  Complex.arg z

/-- Package the radius and argument of a complex number. -/
noncomputable def complexPolarData (z : ℂ) : ℝ × ℝ :=
  (complexRadius z, complexArgument z)

/-- Reconstruct a complex number from radius and angle. -/
noncomputable def complexOfPolar (r θ : ℝ) : ℂ :=
  Complex.mk (r * Real.cos θ) (r * Real.sin θ)

/-- Whether the principal-branch argument should be treated as genuinely defined. -/
def complexArgumentDefined (z : ℂ) : Prop :=
  z ≠ 0

/-- The phase of a complex number, viewed in the quotient `ℝ / (2πℤ)`. -/
noncomputable def complexPhase (z : ℂ) : Real.Angle :=
  (complexArgument z : Real.Angle)

/-- Polar data of a complex-valued random variable. -/
noncomputable def complexPolarRV {Ω : Type*} (Z : Ω → ℂ) : Ω → (ℝ × ℝ) :=
  fun ω => complexPolarData (Z ω)

/-- The phase of a complex-valued random variable in `ℝ / (2πℤ)`. -/
noncomputable def complexPhaseRV {Ω : Type*} (Z : Ω → ℂ) : Ω → Real.Angle :=
  fun ω => complexPhase (Z ω)

theorem complexArgument_undefined_at_zero : ¬ complexArgumentDefined 0 := by
  simp [complexArgumentDefined]

theorem complexOfPolar_eq_mul_exp (r θ : ℝ) :
    complexOfPolar r θ = (r : ℂ) * Complex.exp (θ * Complex.I) := by
  apply Complex.ext <;>
    simp [complexOfPolar, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      mul_add]

theorem complexOfPolar_periodic_two_pi (r θ : ℝ) :
    complexOfPolar r (θ + 2 * Real.pi) = complexOfPolar r θ := by
  apply Complex.ext <;> simp [complexOfPolar, Real.sin_add, Real.cos_add]

theorem complexOfPolar_mul (r₁ θ₁ r₂ θ₂ : ℝ) :
    complexOfPolar r₁ θ₁ * complexOfPolar r₂ θ₂ =
      complexOfPolar (r₁ * r₂) (θ₁ + θ₂) := by
  apply Complex.ext
  · simp [complexOfPolar, Real.cos_add, Real.sin_add, sub_eq_add_neg, mul_add,
      mul_left_comm, mul_comm]
    ring
  · simp [complexOfPolar, Real.cos_add, Real.sin_add, sub_eq_add_neg, mul_add,
      mul_left_comm, mul_comm]
    ring
