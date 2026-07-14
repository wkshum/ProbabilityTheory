import Mathlib.Tactic
import ProbabilityTheory.Chapter_02.def_2_5

/-

 Theorem 2.2 Monotonicity of measure function

-/

/-
\begin{thmbox}{2.2 (Monotonicity)}
Let $(\Omega,\mathcal{F},\mu)$ be a measure space, and suppose $A$ and $B$ are $\mathcal{F}$-measurable sets such that $A\subseteq B$. Then $\mu(A)\le \mu(B)$.
\end{thmbox}

\textit{Proof} Since $A$ and $B\setminus A$ are disjoint and $B=A\cup (B\setminus A)$, we have
\[
\mu(B)=\mu(A)+\mu(B\setminus A).
\]
Since $\mu(B\setminus A)$ is nonnegative, it follows that $\mu(B)\ge \mu(A)$. \hfill $\square$
-/

open MeasureTheory Set

/-- Exported theorem for monotonicity of measures. -/
theorem thm_2_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Set Ω}
  (hAB : A ⊆ B) :
    μ A ≤ μ B := by
  exact measure_mono hAB
