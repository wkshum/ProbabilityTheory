import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-
\begin{thmbox}{7.11 (Change-of-Variable Formula)}
Let $(\Omega,\mathcal{F},\mu)$ be a measure space, and consider two measurable maps $X$ and $h$
\[
(\Omega,\mathcal{F},\mu)\xrightarrow{X} (\mathbb{R},\mathcal{B}(\mathbb{R})) \xrightarrow{h} (\mathbb{R},\mathcal{B}(\mathbb{R})).
\]

Let $X_{\#}\mu$ denote the measure on $\mathbb{R}$ induced by $X$. Then,
\begin{enumerate}[label=(\alph*)]
    \item $h(X)\in L^1(\mu)$ iff $h\in L^1(X_{\#}\mu)$.
    \item If $h$ is nonnegative or if the two equivalent conditions in (a) hold, then
    \begin{equation}
    \int_{\Omega} h(X(\omega))\, d\mu(\omega)
    =
    \int_{\mathbb{R}} h(x)\, dX_{\#}\mu(x).
    \tag{7.7}
    \end{equation}
\end{enumerate}
\end{thmbox}

The function $h$ in the theorem may be continuous or piece-wise continuous. The important requirement is that the composite function $h(X)$ is measurable, so that the composite function $h\circ X$ is also measurable.

\textit{Proof} Suppose $h$ is an indicator function $1_B$ for some Borel set $B\in \mathcal{B}(\mathbb{R})$. The left-hand side of (7.7) is
\[
\int_{\Omega} h(X(\omega))\, d\mu(\omega)
=
\int_{\Omega} (1_B\circ X)(\omega)\, d\mu(\omega)
=
\int_{\Omega} 1_{X^{-1}(B)}\, d\mu
=
\mu(X^{-1}(B)).
\]

Meanwhile, the right-hand side is
\[
\int_{\mathbb{R}} 1_B\, dX_{\#}\mu = X_{\#}\mu(B)=\mu(X^{-1}(B)).
\]

The first equality above follows from the definition of Lebesgue integral for simple function and the second from the definition of $X_{\#}\mu$. Therefore (7.7) holds for indicator functions $h$.

Suppose $h$ is a nonnegative and measurable function. Let $h_n$ be simple and nonnegative functions for $n=1,2,3,\dots$ such that $h_n \nearrow h$. We have $h_n(X)\nearrow h(X)$. Apply the monotone convergence theorem two times in the following derivation:
\[
\int_{\Omega} h(X)\, d\mu
=
\int_{\Omega} \lim_{n\to\infty} h_n(X(\omega))\, d\mu(\omega)
\]
\[
\stackrel{\text{MCT}}{=}
\lim_{n\to\infty} \int_{\Omega} h_n(X(\omega))\, d\mu(\omega)
\]
\[
=
\lim_{n\to\infty} \int_{\mathbb{R}} h_n(x)\, dX_{\#}\mu(x)
\]
\[
\stackrel{\text{MCT}}{=}
\int_{\mathbb{R}} \lim_{n\to\infty} h_n(x)\, dX_{\#}\mu(x)
\]
\[
=
\int_{\mathbb{R}} h(x)\, dX_{\#}\mu(x).
\]

Therefore (7.7) holds for nonnegative and measurable functions.

Next we assume that $h$ is a real-valued and measurable function. Applying the argument in the previous paragraph to $|h|$, we obtain part (a) immediately.

Write $h=h^+-h^-$, where $h^+$ and $h^-$ are the positive and negative parts of $h$. Suppose $h(X)$ is integrable, i.e., suppose that $\int h^+(X)<\infty$ and $\int h^-(X)<\infty$. We note that $h^+(X)$ and $h^-(X)$ are both nonnegative and measurable functions in $L^1(\mu)$. The integral of $h(X)$ is
\[
\int_{\Omega} h(X)\, d\mu
\triangleq
\int_{\Omega} h^+(X(\omega))\, d\mu(\omega)
-
\int_{\Omega} h^-(X(\omega))\, d\mu(\omega)
\]
\[
=
\int_{\mathbb{R}} h^+(x)\, dX_{\#}\mu(x)
-
\int_{\mathbb{R}} h^-(x)\, dX_{\#}\mu(x)
\]
\[
=
\int_{\mathbb{R}} h\, dX_{\#}\mu.
\]

This finishes the proof of the change-of-variable formula. \hfill $\square$
-/


open MeasureTheory

/--
  ## Theorem 7.11
for a measurable `X : Ω → ℝ`, integrability of `h ∘ X` under
`μ` is equivalent to integrability of `h` under the pushforward
measure `Measure.map X μ`, and the corresponding integrals agree.
-/
theorem thm_7_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ} (hX : Measurable X) (hh : Measurable h) :
    (Integrable (fun ω => h (X ω)) μ ↔ Integrable h (Measure.map X μ)) ∧
      (∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ) := by
  constructor
  · change Integrable (h ∘ X) μ ↔ Integrable h (Measure.map X μ)
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ) (f := X) (g := h) hh.aestronglyMeasurable hX.aemeasurable).symm
  · change (∫ ω, (h ∘ X) ω ∂μ) = ∫ x, h x ∂Measure.map X μ
    exact
      (MeasureTheory.integral_map
        (μ := μ) (φ := X) (f := h) hX.aemeasurable hh.aestronglyMeasurable).symm
