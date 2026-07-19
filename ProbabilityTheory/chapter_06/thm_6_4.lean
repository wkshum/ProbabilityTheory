import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-

 # Monotone convergence theorem

-/


/-
\begin{thmbox}{6.4 (Monotone Convergence Theorem (MCT))}
If
\[
0 \le X_1 \le X_2 \le X_3 \le \cdots
\]
is a sequence of non-decreasing, nonnegative measurable functions converging to $X$ from below, then
\[
\int X_n\, d\mu \to \int X\, d\mu
\]
as $n \to \infty$.
\end{thmbox}

We note that the pointwise limit of $(X_n)_{n=1}^{\infty}$ in Theorem 6.4 always exists. We set $X(\omega)=\infty$ when $\lim_{n\to\infty} X_n(\omega)=\infty$. We use the notation $X_n \nearrow X$ to mean that $(X_n)_{n \ge 1}$ is a non-decreasing sequence converging pointwise to $X$.

\textit{Proof} By monotonicity, we have $\int X_n \le \int X$ for all $n$. Therefore, $\sup_n \int X_n \le \int X$. To complete the proof, we need to show that $\sup_n \int X_n \ge \int X$.

Suppose $g$ is a simple function in $S(X)$, so that $g(\omega) \le X(\omega)$ for all $\omega$. We write $g(\omega)$ as a finite summation
\[
g(\omega)=\sum_{i=1}^{k} a_i 1_{A_i}(\omega),
\]
where $a_i \ge 0$ for $i=1,2,\dots,k$, and the sets $A_i$'s are measurable and mutually disjoint.

Fix $\epsilon > 0$. For any $n \ge 1$, let
\[
B_n^{\epsilon} \triangleq \{\omega \in \Omega : X_n(\omega) \ge (1-\epsilon)g(\omega)\}.
\]

The set $B_n^{\epsilon}$ is measurable because both $X_n$ and $g$ are measurable functions.

Since $X_n \nearrow X$ by assumption and $g \le X$, we have $B_n^{\epsilon} \nearrow \Omega$ as $n \to \infty$. For each $n$, we can restrict the integral to the set $B_n^{\epsilon}$ and lower bound $X_n(\omega)$ by $(1-\epsilon)g(\omega)$. Hence, using the monotonicity of Lebesgue integral, we obtain
\[
\int X_n\, d\mu \ge \int 1_{B_n^{\epsilon}} X_n\, d\mu \ge \int 1_{B_n^{\epsilon}(\omega)}(1-\epsilon)g(\omega)\, d\mu(\omega)
\]
\[
= (1-\epsilon)\int 1_{B_n^{\epsilon}} \sum_{i=1}^{k} a_i 1_{A_i}\, d\mu
= (1-\epsilon)\sum_{i=1}^{k} a_i \mu(B_n^{\epsilon} \cap A_i).
\]

Since $B_n^{\epsilon} \nearrow \Omega$, we can take limits on both sides as $n \to \infty$. This yields
\[
\sup_n \int X_n\, d\mu \ge (1-\epsilon)\sum_{i=1}^{k} a_i \mu(A_i).
\]

Because $\epsilon$ can be arbitrarily small, we get $\sup_n \int X_n\, d\mu \ge \int g\, d\mu$. Since the above inequality holds for any $g \in S(X)$, we obtain $\sup_n \int X_n \ge \int X$. \hfill $\square
-/


open MeasureTheory Filter

/--
# Theorem 6.4 Monotone convergence theorem
for a monotone increasing sequence of nonnegative measurable
functions whose pointwise supremum is `X`, the integrals converge to the
integral of `X`.

The corresponding theorem in Mathlib is `lintegral_iSup`
-/
theorem thm_6_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Xn : ℕ → Ω → ENNReal)
    (X : Ω → ENNReal) (h_meas : ∀ n, Measurable (Xn n)) (h_mono : Monotone Xn)
    (h_sup : ∀ ω, (⨆ n, Xn n ω) = X ω) :
    Tendsto (fun n => ∫⁻ ω, Xn n ω ∂μ) atTop (nhds (∫⁻ ω, X ω ∂μ)) := by
  have h_int_mono : Monotone fun n => ∫⁻ ω, Xn n ω ∂μ := by
    intro m n hmn
    exact MeasureTheory.lintegral_mono (fun ω => h_mono hmn ω)
  have h_lintegral :
      ∫⁻ ω, X ω ∂μ = ⨆ n, ∫⁻ ω, Xn n ω ∂μ := by
    calc
      ∫⁻ ω, X ω ∂μ = ∫⁻ ω, ⨆ n, Xn n ω ∂μ := by simp [h_sup]
      _ = ⨆ n, ∫⁻ ω, Xn n ω ∂μ := MeasureTheory.lintegral_iSup h_meas h_mono
  rw [h_lintegral]
  exact tendsto_atTop_iSup h_int_mono
