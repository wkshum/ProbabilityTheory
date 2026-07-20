import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-

 # Theorem 8.4 Layercake theorem

-/


/-
\begin{thmbox}{8.4}
For any nonnegative random variable $Y$, we can compute the expectation $E[Y]$ by
\[
\int_0^{\infty} P(Y\ge u)\, du.
\]
If the cumulative distribution function is $F_Y$, we have
\[
E[Y]=\int_0^{\infty} (1-F_Y(u))\, du.
\]
\end{thmbox}

\textit{Proof} We write $\int_0^{\infty} P(Y\ge u)\, du$ as a double integral
\[
\int_0^{\infty} P(Y\ge u)\, du
=
\int_{[0,\infty)} \int_{\Omega} 1_{\{y\ge u\}}\, dP(y)\, d\lambda(u),
\]
where $\lambda$ is the Lebesgue measure on $\mathbb{R}$. By the Tonelli theorem, we obtain
\[
\int_0^{\infty} P(Y\ge u)\, du
=
\int_{\Omega}\int_{[0,\infty)} 1_{\{y\ge u\}}\, d\lambda(u)\, dP(y)
=
\int_{\Omega} y\, dP(y)
=
E[Y].
\]
\hfill $\square$
-/


open MeasureTheory Set

noncomputable section

/-- The layer-cake / tail-probability formula for a nonnegative integrable random variable, together
with the textbook cdf rewrite when the cdf is presented as `FY u = P(Y < u)`. -/
theorem thm_8_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_meas : Measurable Y) (hY_int : Integrable Y P) (hY_nn : 0 ≤ᵐ[P] Y) :
    (∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, P.real {ω : Ω | u ≤ Y ω}) ∧
      ∀ FY : ℝ → ℝ, (∀ u : ℝ, FY u = P.real {ω : Ω | Y ω < u}) →
        ∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, (1 - FY u) := by
  have h_layer :
      ∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, P.real {ω : Ω | u ≤ Y ω} :=
    MeasureTheory.Integrable.integral_eq_integral_meas_le hY_int hY_nn
  refine ⟨h_layer, ?_⟩
  intro FY hFY
  rw [h_layer]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hs : MeasurableSet {ω : Ω | Y ω < u} :=
    measurableSet_lt hY_meas measurable_const
  have hcompl : P.real {ω : Ω | u ≤ Y ω} = 1 - P.real {ω : Ω | Y ω < u} := by
    simpa [Set.compl_setOf, not_lt] using
      (MeasureTheory.probReal_compl_eq_one_sub (μ := P) hs)
  rw [hcompl, hFY u]
