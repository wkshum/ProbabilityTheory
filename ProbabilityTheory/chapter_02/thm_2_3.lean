import Mathlib.Tactic
import ProbabilityTheory.chapter_02.def_2_5
import ProbabilityTheory.chapter_02.thm_2_2

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

/-- # Theorem 2.3 Measure function is finitely subadditive

This is theorem `measure_union_le` in Mathlib

Exported theorem for finite subadditivity of measures. -/
theorem thm_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∪ B) ≤ μ A + μ B := by
  have h_disj : Disjoint A (B \ A) := disjoint_sdiff_right
  have h_union : A ∪ (B \ A) = A ∪ B := by
    ext x
    constructor
    · intro hx
      exact Or.imp_right (fun hxB => hxB.1) hx
    · intro hx
      rcases hx with hxA | hxB
      · exact Or.inl hxA
      · by_cases hxA : x ∈ A
        · exact Or.inl hxA
        · exact Or.inr ⟨hxB, hxA⟩
  have h_diff_meas : MeasurableSet (B \ A) := hB.diff hA
  have h_add : μ (A ∪ B) = μ A + μ (B \ A) := by
    rw [← h_union]
    exact measure_union h_disj h_diff_meas
  have h_diff_le : μ (B \ A) ≤ μ B :=
    thm_2_2 μ (A := B \ A) (B := B) h_diff_meas hB sdiff_subset
  rw [h_add]
  exact add_le_add le_rfl h_diff_le
