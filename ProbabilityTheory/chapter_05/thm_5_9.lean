import Mathlib.Probability.BorelCantelli
import ProbabilityTheory.chapter_05.thm_5_6

/-

  # Theorem 5.9 Second Borel Cantelli Lemma

-/

/-
\begin{thmbox}{5.9 (Borel--Cantelli (BC) Lemma 2)}
If $(A_i)_{i=1}^{\infty}$ is a sequence of independent events in a probability space $(\Omega,\mathcal{F},P)$ such that $\sum_{i=1}^{\infty} P(A_i)=\infty$, then
\[
P(\limsup_i A_i)=P(A_i\ i.o.)=1.
\]
\end{thmbox}

\textit{Proof} Consider the complement of the event $\limsup_i A_i$
\[
(\limsup_i A_i)^c=\left(\bigcap_{k=1}^{\infty}\bigcup_{j=k}^{\infty} A_j\right)^c=\bigcup_{k=1}^{\infty}\bigcap_{j=k}^{\infty} A_j^c.
\]

We want to show that $P\left(\cup_{k=1}^{\infty}\cap_{j=k}^{\infty} A_j^c\right)=0$. It suffices to prove that $P\left(\cap_{j=k}^{\infty} A_j^c\right)=0$ for all $k$.

We use the inequality $1-x \le e^{-x}$, which holds for all $x \in \mathbb{R}$. For any $k$, consider an integer $m$ larger than $k$
\[
P\left(\bigcap_{j=k}^{m} A_j^c\right)=\prod_{j=k}^{m} P(A_j^c)=\prod_{j=k}^{m} (1-P(A_j)) \le \prod_{j=k}^{m} e^{-P(A_j)}=e^{-\sum_{j=k}^{m} P(A_j)}.
\]

In the first equality above, we use the property that $A_k^c,\ldots,A_m^c$ are independent events (Theorem 5.6). Since $\sum_{i=1}^{\infty} P(A_i)$ is a divergent series, we have $\sum_{j=k}^{m} P(A_j) \to \infty$ as $m \to \infty$. Therefore, using continuity from above, we obtain $P\left(\cap_{j=k}^{\infty} A_j^c\right)=0$. Since it is true for all $k$, we prove $P\left(\cup_{k=1}^{\infty}\cap_{j=k}^{\infty} A_j^c\right)=0$. \hfill $\square
-/

-- WRITE FINAL LEAN CODE BELOW
open Filter
open scoped ENNReal Topology

/--  ## Theorem 5.9 Borel-Cantelli Lemma 2
for independent measurable events in a probability
space, divergence of the probability series forces the limsup event to have
probability one.

We keep the statement at the event level and use Mathlib's
`ProbabilityTheory.measure_limsup_eq_one` for the proof.
-/
theorem thm_5_9 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P)
    (h_series : (∑' n, P (A n)) = ∞) :
    P (limsup A atTop) = 1 := by
  simpa using ProbabilityTheory.measure_limsup_eq_one (μ := P) h_meas h_indep h_series
