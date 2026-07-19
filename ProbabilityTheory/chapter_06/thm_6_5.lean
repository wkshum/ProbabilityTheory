import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-

 # Linearity of Lebesgue integral of nonnegative functions

-/


/-
\begin{thmbox}{6.5 (Linear Property)}
Let $X$ and $Y$ be nonnegative and measurable functions and let $\alpha$ be a nonnegative constant. Then
\[
\int (X+Y)\, d\mu = \int X\, d\mu + \int Y\, d\mu,
\]
\[
\int \alpha X\, d\mu = \alpha \int X\, d\mu.
\]
\end{thmbox}

The equalities in this theorem are interpreted as follows: If the one side of an equality in Theorem 6.5 is infinity, then the other side is also infinity.

\textit{Proof} Let $X_n$'s and $Y_n$'s be simple nonnegative functions such that $X_n \nearrow X$ and $Y_n \nearrow Y$. Such sequences of simple functions always exist using the approximation in (6.4).

For each $n$, the sum $X_n+Y_n$ is simple nonnegative functions converging to $X+Y$ from below. By applying the monotone convergence theorem, we obtain
\[
\int (X+Y)\, d\mu = \int \lim_{n\to\infty} (X_n+Y_n)\, d\mu
\]
\[
= \lim_{n\to\infty} \int (X_n+Y_n)\, d\mu
\]
\[
= \int X\, d\mu + \int Y\, d\mu.
\]

To prove the second equality, we approximate $\alpha X$ by $(\alpha X_n)_{n=1}^{\infty}$, which is non-decreasing and converging to $\alpha X$ from below. The proof is similar to the first part.
-/


open MeasureTheory

/-- ## Theorem 6.5: linearity of the Lebesgue integral for nonnegative measurable functions.

We prove this using existing theorems in Mathlib
-/
theorem thm_6_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hX : Measurable X) (_hY : Measurable Y) (c : ENNReal) :
    ∫⁻ ω, X ω + Y ω ∂μ = ∫⁻ ω, X ω ∂μ + ∫⁻ ω, Y ω ∂μ ∧
      ∫⁻ ω, c * X ω ∂μ = c * ∫⁻ ω, X ω ∂μ := by
  refine ⟨?_, ?_⟩
  · exact MeasureTheory.lintegral_add_left hX Y
  · exact MeasureTheory.lintegral_const_mul c hX
