import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import ProbabilityTheory.chapter_06.thm_6_4

/-

 # Theorem 7.3   Fatou lemma

-/

/-
\begin{thmbox}{7.3 (Fatou's Lemma)}
Let $X_n$, $n=1,2,3,\dots$, be a sequence of measurable functions defined on a measure space $(\Omega,\mathcal{F},\mu)$, such that each of them is nonnegative almost everywhere. Then
\[
\int \liminf_{n\to\infty} X_n\, d\mu \le \liminf_{n\to\infty} \int X_n\, d\mu.
\]
\end{thmbox}

\textit{Proof} The function $\liminf_{n\to\infty} X_n(\omega)$ is well defined and is nonnegative almost everywhere. To be precise, we can assume that each $X_n$ is nonnegative on a measurable set $E_n$ with $\mu(E_n^c)=0$, for $n=1,2,3,\dots$. Then, we can consider the intersection $E=\cap_{n=1}^{\infty} E_n$, which is measurable and satisfies $X_n(\omega)\ge 0$ for all $n$ and all $\omega$ in this set. Moreover, the complement of the set $E$ has measure zero.

For $n\ge 1$, define
\[
Y_n(\omega)\triangleq \inf_{k\ge n} X_k(\omega).
\]
The sequence $Y_1 \le Y_2 \le Y_3 \le \cdots$ is non-decreasing and is converging pointwise on the set $E$. By the monotone convergence theorem (Theorem 6.4),
\[
\int_E Y_n\, d\mu \nearrow \int_E \lim_n Y_n\, d\mu = \int_E \liminf_n X_n\, d\mu.
\]

Therefore
\begin{equation}
\sup_n \int_E Y_n\, d\mu = \int_E \liminf_n X_n\, d\mu.
\tag{7.1}
\end{equation}

We then use the definition of $Y_n=\inf_{k\ge n} X_k$ to see that $X_k\ge Y_n$ on $E$ for all $k\ge n$. Hence, by the monotonic property of integral, we get
\[
\int_E X_k\, d\mu \ge \int_E Y_n\, d\mu \qquad \text{for all } k\ge n.
\]

Combining with the fact that $\mu(E^c)=0$, we obtain
\[
\sup_n \left( \inf_{k\ge n} \int_{\Omega} X_k\, d\mu \right) \ge \int_{\Omega} \liminf_n X_n\, d\mu.
\]

This proves the inequality in Fatou's lemma. \hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

/--  ## Theorem 7.4 Fatou lemma
Exported statement for Fatou's lemma in the textbook
nonnegative setting, modeled as an `ENNReal`-valued sequence.

We apply an equivalent API in Mathlib.
-/
theorem thm_7_3 {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (X : ℕ → Ω → ENNReal)
  (hX : ∀ n, Measurable (X n)) :
    ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂μ ≤
      Filter.liminf (fun n => ∫⁻ ω, X n ω ∂μ) Filter.atTop
  := by
  exact MeasureTheory.lintegral_liminf_le (μ := μ) hX
