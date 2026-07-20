import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-

  # Theorem 7.10 Push-forward measure

-/

/-
\begin{thmbox}{7.10}
Given a measurable mapping $X$ as in (7.6), the set function
\[
X_{\#}\mu(B)\triangleq \mu(X^{-1}(B))=\mu(\{\omega : X(\omega)\in B\})
\]
is a Borel measure defined for all $B\in \mathcal{B}(\mathbb{R})$.
\end{thmbox}

\textit{Proof} Since $X$ is $(\mathcal{F},\mathcal{B}(\mathbb{R}))$-measurable, the pre-image $X^{-1}(B)$ is $\mathcal{F}$-measurable. Hence $X_{\#}\mu$ is well-defined. We check the axioms of measure below. It is obvious that $X_{\#}\mu(\emptyset)=0$. For any sequence of mutually disjoint sets $B_1,B_2,\dots$ in $\mathcal{B}(\mathbb{R})$,
\[
X_{\#}\mu\Bigl(\biguplus_{i=1}^{\infty} B_i\Bigr)
=
\mu\Bigl(X^{-1}\bigl(\biguplus_{i=1}^{\infty} B_i\bigr)\Bigr)
=
\mu\Bigl(\biguplus_{i=1}^{\infty} X^{-1}(B_i)\Bigr)
=
\sum_{i=1}^{\infty} X_{\#}\mu(B_i).
\]

The second equality follows from (4.3) and the third equality from the assumption that $\mu$ is a measure function. \hfill $\square$
-/

open MeasureTheory

/-- The push-forward/Borel measure induced by a measurable map into `ℝ`. -/
noncomputable def pushForwardRealMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  Measure.map X μ

/--
Exported statement for Theorem 7.10: the push-forward set function is a Borel
measure, and on Borel sets it is computed by preimages.
-/
theorem thm_7_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) {B : Set ℝ} (hB : MeasurableSet B) :
    pushForwardRealMeasure μ X B = μ (X ⁻¹' B) := by
  simpa [pushForwardRealMeasure] using (Measure.map_apply hX hB)
