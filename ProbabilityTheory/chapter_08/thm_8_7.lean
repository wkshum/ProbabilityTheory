import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Real
import ProbabilityTheory.chapter_08.def_8_1
import ProbabilityTheory.chapter_08.def_8_5

/-

  # Theorem 8.8   Coupling inequality

-/

/-
\begin{thmbox}{8.7 (Coupling Inequality)}
Given two probability measures $P$ and $Q$ defined on the same measurable space $(\mathcal{X},\mathcal{F})$, any coupling of $(X,Y)$ defined on a probability space $(\Omega,\mathcal{H},\mu)$ satisfies
\[
d_{TV}(P,Q)\le \mu(\{X\neq Y\}).
\]
\end{thmbox}

\textit{Proof} The proof depends on the following trick. For any subset $A\subseteq \mathcal{X}$ that is $\mathcal{F}$-measurable, we have
\[
P(A)-Q(A)=\mu(X\in A)-\mu(Y\in A)
\]
\[
=\mu(X\in A, X=Y)+\mu(X\in A, X\neq Y)
\]
\[
\qquad -\mu(Y\in A, X=Y)-\mu(Y\in A, X\neq Y)
\]
\[
=\mu(X\in A, X\neq Y)-\mu(Y\in A, X\neq Y)
\]
\[
\le \mu(X\in A, X\neq Y).
\]

Taking supremum over all $A\in \mathcal{F}$ on both sides, we get
\[
\sup_{A\in \mathcal{F}} (P(A)-Q(A))
\le
\sup_{A\in \mathcal{F}} \mu(X\in A, X\neq Y).
\]

The last supremum is achieved when $A=\mathcal{X}$. This proves $d_{TV}(P,Q)\le \mu(X\neq Y)$. \hfill $\square$
-/


open MeasureTheory Set --ProbabilityTheory Set

noncomputable section

/-- Any coupling controls the total variation distance by its mismatch probability. -/
theorem thm_8_7
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) :
    totalVariationDistance P Q ≤ π.μ.real {ω : π.Ω | π.X ω ≠ π.Y ω} := by
  let mismatch : Set π.Ω := {ω : π.Ω | π.X ω ≠ π.Y ω}
  let S : Set ℝ := {d : ℝ | ∃ A : Set α, MeasurableSet A ∧ d = |P.real A - Q.real A|}
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simp
  have hbound : ∀ d ∈ S, d ≤ π.μ.real mismatch := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    have hP : P.real A = π.μ.real (π.X ⁻¹' A) := by
      simpa [π.map_X] using
        (MeasureTheory.map_measureReal_apply (μ := π.μ) π.measurable_X hA)
    have hQ : Q.real A = π.μ.real (π.Y ⁻¹' A) := by
      simpa [π.map_Y] using
        (MeasureTheory.map_measureReal_apply (μ := π.μ) π.measurable_Y hA)
    have hsubXY : π.X ⁻¹' A ⊆ π.Y ⁻¹' A ∪ mismatch := by
      intro ω hω
      by_cases hEq : π.X ω = π.Y ω
      · left
        simpa [Set.mem_preimage, hEq] using hω
      · right
        simp [mismatch, hEq]
    have hsubYX : π.Y ⁻¹' A ⊆ π.X ⁻¹' A ∪ mismatch := by
      intro ω hω
      by_cases hEq : π.X ω = π.Y ω
      · left
        simpa [Set.mem_preimage, hEq] using hω
      · right
        simp [mismatch, hEq]
    have hXY_le :
        π.μ.real (π.X ⁻¹' A) ≤ π.μ.real (π.Y ⁻¹' A) + π.μ.real mismatch := by
      refine le_trans (MeasureTheory.measureReal_mono hsubXY) ?_
      exact MeasureTheory.measureReal_union_le (π.Y ⁻¹' A) mismatch
    have hYX_le :
        π.μ.real (π.Y ⁻¹' A) ≤ π.μ.real (π.X ⁻¹' A) + π.μ.real mismatch := by
      refine le_trans (MeasureTheory.measureReal_mono hsubYX) ?_
      exact MeasureTheory.measureReal_union_le (π.X ⁻¹' A) mismatch
    have h1 : π.μ.real (π.X ⁻¹' A) - π.μ.real (π.Y ⁻¹' A) ≤ π.μ.real mismatch := by
      linarith
    have h2 : π.μ.real (π.Y ⁻¹' A) - π.μ.real (π.X ⁻¹' A) ≤ π.μ.real mismatch := by
      linarith
    rw [hP, hQ]
    exact (abs_sub_le_iff.2 ⟨h1, h2⟩)
  unfold totalVariationDistance
  change sSup S ≤ π.μ.real mismatch
  exact csSup_le hnonempty hbound
