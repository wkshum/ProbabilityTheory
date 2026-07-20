import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
\begin{thmbox}{7.1 (Triangle Inequality for Real Integral and Complex Integral)}
\[
\left|\int X\, d\mu\right| \le \int |X|\, d\mu \quad \text{for } X \in L^1(\mu).
\]
\end{thmbox}

\textit{Proof} When $X$ is $\bar{\mathbb{R}}$-valued, we can prove the inequality easily by using the fact $|X| = X^+ + X^-$,
\[
\left|\int X\right|
=
\left|\int X^+ - \int X^-\right|
\le
\int X^+ + \int X^-
=
\int |X|.
\]

A little bit more work is required when $X$ is a complex measurable function. We write $X$ as $U+iV$, where $U$ and $V$ are real-valued functions. If $\int X = 0$, then the inequality is trivially true. Suppose $\int X \neq 0$ and $\int X$ in polar form is $re^{i\theta}$.

Let $\alpha = e^{-i\theta}$. Geometrically, multiplying $\alpha$ and $\int X$ means rotating the point in the complex plane corresponding to $\int X$ by an angle of $-\theta$. Using the properties that the product $\alpha\int X$ is a positive real number and $|\alpha|=1$, we get
\[
\left|\int X\right|
=
|\alpha|\cdot \left|\int X\right|
=
\left|\alpha \int X\right|
=
\left|\int \alpha X\right|
=
\int \alpha X
=
\operatorname{Re}\left(\int \alpha X\right)
=
\int \operatorname{Re}(\alpha X).
\]

Since $\operatorname{Re}(z)\le |z|$ for any complex number $z$, by monotonic property for real integral, we obtain
\[
\left|\int X\right|
\le
\int |\alpha X|
=
\int |\alpha||X|
=
\int |X|.
\]
\hfill $\square$
-/

open MeasureTheory

/--
## Theorem 7.1: triangle inequality
for real- or complex-valued integrable
functions, the norm/absolute value of the integral
is bounded by the integral of the pointwise norm.

We use an existing API in Mathlib to finish the proof
-/
theorem thm_7_1 {Ω 𝕜 : Type*}
  [MeasurableSpace Ω] [RCLike 𝕜] (μ : Measure Ω)
  (X : Ω → 𝕜) (_hX : Integrable X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := by
  exact MeasureTheory.norm_integral_le_integral_norm (μ := μ) X
