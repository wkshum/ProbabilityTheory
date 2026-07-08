import Mathlib
import ProbabilityTheory.chapter_01.def_1_2

/- # Improper Riemann-Stieltjes integrals

\begin{defbox}{1.4}
We define an improper Riemann--Stieltjes integral of a function $f$
with respect to a non-decreasing function $\alpha$ by the double limit
\[
\int_{-\infty}^{\infty} f\, d\alpha
\triangleq
\lim_{\substack{a\to -\infty\\ b\to \infty}} \int_a^b f\, d\alpha
\]
provided that the limit exists and is finite. In this case,
we say that the improper integral converges.
\end{defbox}

-/

open Filter

noncomputable section

/-- The directed filter used for the textbook double limit
`a -> -infty`, `b -> infty` with the side condition `a <= b`. -/
def improperRSFilter : Filter (ℝ × ℝ) :=
  (atBot ×ˢ atTop) ⊓ Filter.principal {p : ℝ × ℝ | p.1 ≤ p.2}

/-- The finite truncation value, guarded by the Definition 1.2 interface. -/
noncomputable def rsTruncIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ :=
  by
    classical
    exact if h : RSIntegrable f α a b then rsIntegral f α a b h else 0

/-- Convergence of the double truncation net to the value `I`. -/
def ImproperRSConvergesTo (f α : ℝ → ℝ) (I : ℝ) : Prop :=
  (∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable f α p.1 p.2) ∧
    Tendsto
      (fun p : ℝ × ℝ => rsTruncIntegral f α p.1 p.2)
      improperRSFilter
      (nhds I)

/-- Improper Riemann-Stieltjes integrability via the double truncation limit. -/
def ImproperRSIntegrable (f α : ℝ → ℝ) : Prop :=
  ∃ I : ℝ, ImproperRSConvergesTo f α I

/-- Chosen value of the improper Riemann-Stieltjes integral,
available only after convergence has been established. -/
noncomputable def improperRSIntegral
  (f α : ℝ → ℝ) (h : ImproperRSIntegrable f α) : ℝ :=
  Classical.choose h

/-- The chosen value really is the limit packaged by `ImproperRSIntegrable`. -/
theorem improperRSIntegral_spec {f α : ℝ → ℝ} (h : ImproperRSIntegrable f α) :
    ImproperRSConvergesTo f α (improperRSIntegral f α h) :=
  Classical.choose_spec h

/-- # Definition 1.4 (Improper Riemann-Stieltjes Integrability)
Exported definition for Definition 1.4. -/
def def_1_4 (f α : ℝ → ℝ) : Prop :=
  ImproperRSIntegrable f α
