import Mathlib.Tactic
import ProbabilityTheory.chapter_08.def_8_5
import ProbabilityTheory.common_support.tv_distance_core


/-

 # Theorem 8.6  Formula for computing TV distance for continuous and discrete distribution

-/

open MeasureTheory Set
open TVCore

noncomputable section

/-
TASK ID: thm_8_6
TYPE: Theorem_with_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
TASK CONTENT:
\begin{thmbox}{8.6}
Suppose $P$ and $Q$ are probability measures defined on the set of nonnegative integers $\Omega=\{0,1,2,3,\dots\}$. Then, the total variation distance between $P$ and $Q$ is given by
\[
d_{TV}(P,Q)=\frac{1}{2}\sum_{i=0}^{\infty} |P(\{i\})-Q(\{i\})|.
\]

If probability measures $P$ and $Q$ have piece-wise continuous pdf's $f(x)$ and $g(x)$, respectively, then we have
\[
d_{TV}(P,Q)=\frac{1}{2}\int_{-\infty}^{\infty} |f(x)-g(x)|\, dx.
\]
\end{thmbox}

\textit{Proof} We only prove the discrete case. We first note that in the definition of total variation distance, we can remove the absolute value in (8.3) without changing the result. This is because if $P(A)<Q(A)$, we can consider the complement $A^c$ and use the fact that
\[
|P(A)-Q(A)| = |1-P(A^c)-(1-Q(A^c))| = P(A^c)-Q(A^c).
\]

Hence, the computation of total variation distance amounts to the maximization of $P(A)-Q(A)$ over all events $A$. We claim that is maximized when $A$ is the event
\[
A_+\triangleq \{i\in \Omega : P(\{i\})>Q(\{i\})\}.
\]

To see this, we let $A_-\triangleq \{i : P(\{i\})<Q(\{i\})\}$, and $A_0=\{i : P(\{i\})=Q(\{i\})\}$. The three events $A_+$, $A_-$, and $A_0$ are disjoint. Hence,
\[
P(A_+)+P(A_-)+P(A_0)=1=Q(A_+)+Q(A_-)+Q(A_0).
\]

By noting $P(A_0)=Q(A_0)$, we obtain
\[
|P(A_+)-Q(A_+)| = |P(A_-)-Q(A_-)| = \frac{1}{2}\sum_{i=0}^{\infty} |P(\{i\})-Q(\{i\})|.
\]

The proof for the continuous case is similar. \hfill $\square$
-/

/-- Discrete PMF version of Theorem 8.6. -/
theorem thm_8_6_discrete_pmf (p q : PMF ℕ) :
    totalVariationDistance p.toMeasure q.toMeasure
      = (1 / 2 : ℝ) * ∑' n, |(p n).toReal - (q n).toReal| := by
  simpa [TVCore.pmfDiff, TVCore.pmfReal] using
    TVCore.discrete_totalVariationDistance_eq_half_tsum_abs p q

/-- Discrete measure version of Theorem 8.6. -/
theorem thm_8_6_discrete (P Q : Measure ℕ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    totalVariationDistance P Q
      = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}| := by
  calc
    totalVariationDistance P Q
        = totalVariationDistance P.toPMF.toMeasure Q.toPMF.toMeasure := by
            rw [Measure.toPMF_toMeasure, Measure.toPMF_toMeasure]
    _ = (1 / 2 : ℝ) * ∑' n, |((P.toPMF n).toReal - (Q.toPMF n).toReal)| := by
            exact thm_8_6_discrete_pmf P.toPMF Q.toPMF
    _ = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}| := by
            simp [Measure.toPMF_apply, Measure.real_def]

/-- Continuous density version of Theorem 8.6. The assumptions are phrased in a stronger but
textbook-compatible way: measurable, integrable, nonnegative densities of total mass `1`. -/
theorem thm_8_6_continuous
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    totalVariationDistance (densityMeasure f) (densityMeasure g)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  exact TVCore.continuous_totalVariationDistance_eq_half_integral_abs
    hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob

/-- Exported wrapper for Theorem 8.6 containing both the discrete and continuous formulas. -/
theorem thm_8_6 :
    (∀ (P Q : Measure ℕ) (_ : IsProbabilityMeasure P) (_ : IsProbabilityMeasure Q),
      totalVariationDistance P Q = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}|) ∧
    (∀ (f g : ℝ → ℝ),
      Measurable f →
      Measurable g →
      Integrable f volume →
      Integrable g volume →
      (∀ x, 0 ≤ f x) →
      (∀ x, 0 ≤ g x) →
      (∫ x, f x = 1) →
      (∫ x, g x = 1) →
      totalVariationDistance (densityMeasure f) (densityMeasure g)
        = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x|) := by
  constructor
  · intro P Q hP hQ
    letI := hP
    letI := hQ
    exact thm_8_6_discrete P Q
  · intro f g hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
    exact thm_8_6_continuous hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
