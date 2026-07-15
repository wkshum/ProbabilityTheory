import Mathlib.Tactic
import ProbabilityTheory.chapter_02.def_2_5

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
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    μ A ≤ μ B := by
  have h_disj : Disjoint A (B \ A) := disjoint_sdiff_right
  have h_union : A ∪ (B \ A) = B := union_sdiff_cancel hAB
  have h_diff_meas : MeasurableSet (B \ A) := hB.diff hA
  have h_add : μ B = μ A + μ (B \ A) := by
    calc
      μ B = μ (A ∪ (B \ A)) := by rw [h_union]
      _ = μ A + μ (B \ A) := measure_union h_disj h_diff_meas
  rw [h_add]
  exact le_add_right le_rfl
