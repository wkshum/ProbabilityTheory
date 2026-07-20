import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-

 # Lebesgue integral of complex-valued function

-/

/-
\begin{defbox}{6.6 (Complex Lebesgue Integral)}
Suppose $Z(\omega)=X(\omega)+iY(\omega)$, where $X(\omega)$ and $Y(\omega)$ are the real and imaginary parts of $Z(\omega)$, respectively. If both $X$ and $Y$ are integrable, then we say that $Z$ is \textit{integrable} and define the Lebesgue integral of $Z$ by
\[
\int Z\, d\mu \triangleq \int X\, d\mu + i\int Y\, d\mu
\]
and write $Z \in L^1(\mu)$. The integral of $Z$ is not defined if $X$ or $Y$ is not integrable.
\end{defbox}
-/

open MeasureTheory

/-- A complex-valued function is textbook-integrable exactly when its real and
imaginary parts are Lebesgue integrable. -/
def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  Integrable (fun ω => (Z ω).re) μ ∧ Integrable (fun ω => (Z ω).im) μ

/-- The componentwise textbook predicate is equivalent to Mathlib's standard
complex Bochner integrability predicate. -/
theorem complexTextbookIntegrable_iff_integrable_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) :
    complexTextbookIntegrable μ Z ↔ Integrable Z μ := by
  unfold complexTextbookIntegrable
  exact (MeasureTheory.Integrable.re_im_iff (μ := μ) (f := Z))

/-- Textbook complex integral: undefined if either component is not integrable. -/
noncomputable def complexTextbookIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Option ℂ := by
  classical
  exact
    if hZ : complexTextbookIntegrable μ Z then
      some
        (Complex.ofReal (∫ ω, (Z ω).re ∂μ) +
          Complex.I * Complex.ofReal (∫ ω, (Z ω).im ∂μ))
    else
      none

/-- Task-level alias for Definition 6.6. -/
noncomputable def def_6_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) :
    Option ℂ :=
  complexTextbookIntegral μ Z

theorem complexTextbookIntegral_eq_none_of_not_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : ¬ complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = none := by
  classical
  simp [complexTextbookIntegral, hZ]

theorem complexTextbookIntegral_eq_some_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : complexTextbookIntegrable μ Z) :
    ∃ w : ℂ, complexTextbookIntegral μ Z = some w := by
  refine ⟨∫ ω, Z ω ∂μ, ?_⟩
  have hZ' : Integrable Z μ :=
    (complexTextbookIntegrable_iff_integrable_core μ Z).mp hZ
  unfold complexTextbookIntegral
  rw [dif_pos hZ]
  apply congrArg some
  simpa [mul_comm] using (integral_re_add_im hZ')
/-- On the integrable branch, the textbook componentwise value agrees with
Mathlib's standard complex Bochner integral. -/
theorem complexTextbookIntegral_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  have hZ' : Integrable Z μ :=
    (complexTextbookIntegrable_iff_integrable_core μ Z).mp hZ
  unfold complexTextbookIntegral
  rw [dif_pos hZ]
  apply congrArg some
  simpa [mul_comm] using (integral_re_add_im hZ')
