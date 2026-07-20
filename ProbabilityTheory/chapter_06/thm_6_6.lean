import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import ProbabilityTheory.chapter_06.thm_6_3

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

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤

noncomputable def realAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, (X ω).abs ∂μ

theorem ereal_abs_eq_pos_add_neg (x : EReal) :
    x.abs = x.toENNReal + (-x).toENNReal := by
  induction x
  · simp [EReal.abs_bot]
  · rename_i x
    rcases le_total 0 x with hx | hx
    · simp [EReal.abs_def, abs_of_nonneg hx, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr hx)]
    · simp [EReal.abs_def, abs_of_nonpos hx, ENNReal.ofReal_of_nonpos hx]
  · simp [EReal.abs_top, EReal.toENNReal_top]

theorem toENNReal_le_abs (x : EReal) : x.toENNReal ≤ x.abs := by
  rw [ereal_abs_eq_pos_add_neg]
  exact le_add_of_nonneg_right bot_le

theorem neg_toENNReal_le_abs (x : EReal) : (-x).toENNReal ≤ x.abs := by
  rw [ereal_abs_eq_pos_add_neg]
  exact le_add_of_nonneg_left bot_le

theorem realAbsIntegral_eq_parts {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) (hXm : Measurable X) :
    realAbsIntegral μ X = posLIntegral μ X + negLIntegral μ X := by
  change (∫⁻ ω, (X ω).abs ∂μ) =
    (∫⁻ ω, (X ω).toENNReal ∂μ) + (∫⁻ ω, (-X ω).toENNReal ∂μ)
  rw [lintegral_congr (fun ω => ereal_abs_eq_pos_add_neg (X ω)),
    lintegral_add_left hXm.ereal_toENNReal]

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
    (μ : Measure Ω) (X : Ω → EReal) (hXm : Measurable X) :
    textbookIntegrable μ X ↔ realAbsIntegral μ X < ⊤ := by
  constructor
  · intro hX
    rw [realAbsIntegral_eq_parts μ X hXm]
    exact ENNReal.add_lt_top.mpr hX
  · intro hAbs
    constructor
    · change (∫⁻ ω, (X ω).toENNReal ∂μ) < ⊤
      exact lt_of_le_of_lt
        (thm_6_3 μ (fun ω => toENNReal_le_abs (X ω)))
        (by simpa [realAbsIntegral] using hAbs)
    · change (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤
      exact lt_of_le_of_lt
        (thm_6_3 μ (fun ω => neg_toENNReal_le_abs (X ω)))
        (by simpa [realAbsIntegral] using hAbs)

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
        continuous_abs.measurable.comp (Complex.continuous_re.measurable.comp hZm)
    have h_rhs_top :
        ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ < ⊤ := by
      have hsum :
          ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ =
            realPartAbsIntegral μ Z + imagPartAbsIntegral μ Z := by
        rw [lintegral_add_left h_meas_re]
        · simp [realPartAbsIntegral, imagPartAbsIntegral]
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
Theorem 6.6, `EReal` branch: an extended-real-valued measurable function is
integrable iff the integral of its absolute value is finite.
-/
theorem thm_6_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal)
    (hXm : Measurable X) :
    ((∫⁻ ω, (X ω).toENNReal ∂μ) < ⊤ ∧
        (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤) ↔
      (∫⁻ ω, (X ω).abs ∂μ) < ⊤ := by
  simpa [Thm66Support.textbookIntegrable, Thm66Support.realAbsIntegral,
    Thm66Support.posLIntegral, Thm66Support.negLIntegral, Thm66Support.posPart, Thm66Support.negPart]
    using Thm66Support.textbookIntegrable_iff_realAbsIntegral_lt_top μ X hXm

/--
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
