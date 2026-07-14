import Mathlib.Tactic
import ProbabilityTheory.Chapter_02.def_2_5

/-

 Theorem 2.3 Finite subadditivity of measure

-/


/-
\begin{thmbox}{2.3 (Finite Subadditivity)}
Let $(\Omega,\mathcal{F},\mu)$ be a measure space, and suppose $A$ and $B$ are
$\mathcal{F}$-measurable sets. Then
\[
\mu(A\cup B)\le \mu(A)+\mu(B).
\]
\end{thmbox}

\textit{Proof} $\mu(A\cup B)= \mu(A \uplus (B\setminus A))
 =\mu(A)+\mu(B\setminus A)\le \mu(A)+\mu(B)$. \hfill $\square$
-/


open MeasureTheory Set

/-- # Theorem 2.5 Measure function is finite subadditivity

This is theorem `measure_union_le` in Mathlib

Exported theorem for finite subadditivity of measures. -/
theorem thm_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω) :
    μ (A ∪ B) ≤ μ A + μ B := by
  simpa using measure_union_le A B
