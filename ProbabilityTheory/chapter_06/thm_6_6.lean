import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import ProbabilityTheory.chapter_06.def_6_6

/-

 # Theorem 6.6 an equivalent condition of integrability

-/

/-
\begin{thmbox}{6.6}
An $\bar{\mathbb{R}}$-valued or $\mathbb{C}$-valued measurable function $X$ is integrable if and only if $\int |X|\, d\mu$ is finite.
\end{thmbox}

\textit{Proof} We first consider an $\bar{\mathbb{R}}$-valued function $X$. If $X$ is integrable, then by definition $\int X^+$ and $\int X^-$ are finite. This implies $\int |X|=\int X^+ + \int X^-$ is finite (by the linear property of Lebesgue integral for nonnegative function). Conversely, suppose $\int |X|$ is finite. Since $X^+ \le |X|$ and $X^- \le |X|$, by the monotonic property in Theorem 6.3, both $\int X^+$ and $\int X^-$ are finite, and hence $X$ is integrable.

Let $Z(\omega)=X(\omega)+iY(\omega)$ denote a complex-valued function. Suppose $Z$ is integrable, i.e., both its real and imaginary parts are integrable. Using the triangle inequality of complex numbers $|x+iy|\le |x|+|y|$ and the monotonic property of real integral, we obtain
\[
\int |Z| = \int |X+iY|
\le \int |X|+|Y|
= \int |X|+\int |Y| < \infty.
\]

Conversely, suppose $\int |Z|$ is finite. Since $|X(\omega)|\le |Z(\omega)|$ for all $\omega \in \Omega$, we obtain $\int |X|<\infty$. Similarly, we have $\int |Y|<\infty$. This proves that $Z$ is integrable. \hfill $\square
-/

open MeasureTheory

namespace Thm66Support

open Def66RealSupport

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤

noncomputable def realAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  posLIntegral μ X + negLIntegral μ X

noncomputable def realPartAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal |(Z ω).re| ∂μ

noncomputable def imagPartAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal |(Z ω).im| ∂μ

def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  realPartAbsIntegral μ Z < ⊤ ∧ imagPartAbsIntegral μ Z < ⊤

noncomputable def complexAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂μ

theorem textbookIntegrable_iff_realAbsIntegral_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) :
    textbookIntegrable μ X ↔ realAbsIntegral μ X < ⊤ := by
  constructor
  · intro hX
    simpa [textbookIntegrable, realAbsIntegral] using (ENNReal.add_lt_top.mpr hX)
  · intro hAbs
    constructor
    · exact lt_of_le_of_lt (le_add_of_nonneg_right bot_le) (by simpa [realAbsIntegral] using hAbs)
    · exact lt_of_le_of_lt (le_add_of_nonneg_left bot_le) (by simpa [realAbsIntegral] using hAbs)


theorem complexTextbookIntegrable_iff_complexAbsIntegral_lt_top {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) (hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ complexAbsIntegral μ Z < ⊤ := by
  constructor
  · intro hZ
    have h_pointwise :
        (fun ω => ENNReal.ofReal ‖Z ω‖) ≤
          fun ω => ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im| := by
      intro ω
      simpa [ENNReal.ofReal_add, abs_nonneg, add_comm, add_left_comm, add_assoc] using
        ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im (Z ω))
    have h_meas_re : Measurable fun ω => ENNReal.ofReal |(Z ω).re| := by
      apply Measurable.ennreal_ofReal
      simpa [Function.comp_def] using
        continuous_abs.measurable.comp
          (Complex.continuous_re.measurable.comp hZm)
    have h_rhs_top :
        ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ < ⊤ := by
      have hsum :
          ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ =
            realPartAbsIntegral μ Z + imagPartAbsIntegral μ Z := by
        rw [lintegral_add_left h_meas_re]
        rfl
      rw [hsum]
      exact ENNReal.add_lt_top.mpr hZ
    exact lt_of_le_of_lt (lintegral_mono h_pointwise) h_rhs_top
  · intro hAbs
    constructor
    · refine lt_of_le_of_lt ?_ hAbs
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm (Z ω))
    · refine lt_of_le_of_lt ?_ hAbs
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm (Z ω))


end Thm66Support



/--
## Theorem 6.6, `EReal` branch:
an extended-real-valued measurable function is
integrable iff the integral of its absolute value is finite.
-/
theorem thm_6_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal)
    (_hXm : Measurable X) :
    ((∫⁻ ω, (X ω).toENNReal ∂μ) < ⊤ ∧
        (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤) ↔
      (∫⁻ ω, (X ω).toENNReal ∂μ) + (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤ := by
  simp only [ENNReal.add_lt_top]

/--   ## Theorem 6.6  Complex version
Complex companion to Theorem 6.6: a complex-valued measurable function is
integrable iff the integral of its norm is finite.
-/
theorem thm_6_6_complex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ)
    (hZm : Measurable Z) :
    ((∫⁻ ω, ENNReal.ofReal |(Z ω).re| ∂μ) < ⊤ ∧
        (∫⁻ ω, ENNReal.ofReal |(Z ω).im| ∂μ) < ⊤) ↔
      (∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂μ) < ⊤ := by
  simpa [Thm66Support.complexTextbookIntegrable, Thm66Support.complexAbsIntegral,
    Thm66Support.realPartAbsIntegral, Thm66Support.imagPartAbsIntegral]
    using Thm66Support.complexTextbookIntegrable_iff_complexAbsIntegral_lt_top μ Z hZm
