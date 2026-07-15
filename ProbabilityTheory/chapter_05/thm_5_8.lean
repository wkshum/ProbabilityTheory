import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ProbabilityTheory.chapter_03.def_3_8

/-

  # Theorem 5.8 The first Borel-Cantelli lemma

-/

/-
\begin{thmbox}{5.8 (Borel--Cantelli (BC) Lemma 1)}
If $A_i$ are events in a probability space $(\Omega,\mathcal{F},P)$, for $i \ge 1$, satisfying $\sum_{i=1}^{\infty} P(A_i)<\infty$, then
\[
P(\limsup_i A_i)=P(A_i\ i.o.)=0.
\]
\end{thmbox}

\textit{Proof} We can write the limsup of $A_i$'s as an intersection
\[
\limsup_i A_i=\bigcap_{k=1}^{\infty} E_k,
\]
where $E_k$ is the event $E_k \triangleq \cup_{j=k}^{\infty} A_j$. Since $E_1 \supseteq E_2 \supseteq E_3 \supseteq \cdots$ is a decreasing sequence of events, by the upper semi-continuity of measure, it suffices to prove that the probability $P(E_k)$ approaches $0$ as $k \to \infty$.

Since the probability measure $P$ satisfies the $\sigma$-subadditivity property (Definition 3.8), we get
\[
P(E_k)=P\left(\cup_{j=k}^{\infty} A_j\right)\le \sum_{j=k}^{\infty} P(A_j).
\]

Since $\sum_{j=1}^{\infty} P(A_j)$ is a convergence series, the limit $\lim_{k \to \infty} \sum_{j=k}^{\infty} P(A_j)$ must be zero. This implies $P(E_k) \searrow 0$ as $k \to \infty$. \hfill $\square
-/

open Filter
open scoped ENNReal Topology

/-- ## Theorem 5.8 BC lemma 1
Borel-Cantelli Lemma 1: if the series of the probabilities of the events `A n`
is summable in `ℝ≥0∞`, then the limsup event has probability zero.

We keep the textbook shape by stating the result for a sequence of events in a
probability space, while delegating the technical proof to Mathlib's
`MeasureTheory.measure_limsup_atTop_eq_zero`.
-/
theorem thm_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_series : (∑' n, P (A n)) ≠ ∞) :
    P (limsup A atTop) = 0 := by
  simpa using MeasureTheory.measure_limsup_atTop_eq_zero (μ := P) (s := A) h_series
