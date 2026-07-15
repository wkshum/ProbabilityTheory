import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.BorelCantelli

/-

  # Borel's zero one law

-/


/-
\begin{thmbox}{5.10 (Borel's Zero--One Law)}
Suppose $(A_i)_{i=1}^{\infty}$ is a sequence of independent events in a probability space $(\Omega,\mathcal{F},P)$. Then
\[
P(A_i\ \text{i.o.})=
\begin{cases}
1 & \text{if } \sum_{i=1}^{\infty} P(A_i)=\infty,\\
0 & \text{if } \sum_{i=1}^{\infty} P(A_i)<\infty.
\end{cases}
\]
\end{thmbox}
-/

-- WRITE FINAL LEAN CODE BELOW
open Filter
open scoped ENNReal Topology

/-- ## Theorem 5.10 Borel's zero-one law
for independent measurable events in a probability space,
the probability of occurring infinitely often is
completely determined by whether the probability series
diverges or converges.
-/
theorem thm_5_10 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P) :
    P (limsup A atTop) = if (∑' n, P (A n)) = ∞ then 1 else 0 := by
  by_cases h_series : (∑' n, P (A n)) = ∞
  · simp [h_series, ProbabilityTheory.measure_limsup_eq_one (μ := P) h_meas h_indep h_series]
  · simp [h_series, MeasureTheory.measure_limsup_atTop_eq_zero (μ := P) (s := A) h_series]
