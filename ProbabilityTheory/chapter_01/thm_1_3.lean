import Mathlib
import ToyApollo.Output.def_1_2

/-
TASK ID: thm_1_3
TYPE: Theorem_with_Proof
SOURCE PLAN: 38_chap1_riemann_stieltjes
TASK CONTENT:
\begin{thmbox}{1.3}
If $f \in \mathcal{R}(\alpha_1)$ and $f \in \mathcal{R}(\alpha_2)$ for two non-decreasing functions $\alpha_1$ and $\alpha_2$, then $f \in \mathcal{R}(\alpha_1+\alpha_2)$ and
\[
\int_a^b f\, d(\alpha_1+\alpha_2)=\int_a^b f\, d\alpha_1+\int_a^b f\, d\alpha_2.
\]
\end{thmbox}

\textit{Proof} It is clear that $\alpha_1+\alpha_2$ is a non-decreasing function. Let $P$ be a partition of the interval $[a,b]$ as in (1.5) and choose any point $t_k \in [x_{k-1},x_k]$. The Riemann--Stieltjes sum of $f$ with respect to $\alpha_1+\alpha_2$ can be decomposed as
\[
S(P,f,\alpha_1+\alpha_2)
=
\sum_{k=1}^{n} f(t_k)\bigl[\alpha_1(x_k)+\alpha_2(x_k)-(\alpha_1(x_{k-1})+\alpha_2(x_{k-1}))\bigr]
\]
\[
=
\sum_{k=1}^{n} f(t_k)(\alpha_1(x_k)-\alpha_1(x_{k-1}))
+
\sum_{k=1}^{n} f(t_k)(\alpha_2(x_k)-\alpha_2(x_{k-1})).
\]

As $n\to \infty$ and $\max_k (x_k-x_{k-1})\to 0$, we have
\[
S(P,f,\alpha_1+\alpha_2)\to \int_a^b f\, d\alpha_1+\int_a^b f\, d\alpha_2.
\]
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

/-- The displayed source-line decomposition
`S(P,f,alpha1+alpha2) = S(P,f,alpha1) + S(P,f,alpha2)` for tagged
Riemann-Stieltjes sums. -/
theorem thm_1_3_tagged_sum_decomposition {a b : ℝ}
    (P : DarbouxRS.Partition a b) (tags : ℕ → ℝ) (f α₁ α₂ : ℝ → ℝ) :
    DarbouxRS.taggedSum P tags f (fun x => α₁ x + α₂ x) =
      DarbouxRS.taggedSum P tags f α₁ + DarbouxRS.taggedSum P tags f α₂ := by
  exact DarbouxRS.taggedSum_integrator_add P tags f α₁ α₂

/-- Theorem 1.3: additivity of the Riemann--Stieltjes integral in the
integrator. -/
theorem thm_1_3 {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    ∃ hsum : RSIntegrable f (fun x => α₁ x + α₂ x) a b,
      rsIntegral f (fun x => α₁ x + α₂ x) a b hsum =
        rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact ⟨rsIntegrable_integrator_add h₁ h₂, rsIntegral_integrator_add h₁ h₂⟩
