import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-

   # Theorem 6.3 Monotonicity
   of Lebesuge integral for nonnegative integral

-/

/-
\begin{thmbox}{6.3 (Monotonicity)}
Suppose $X$ and $Y$ are nonnegative measurable functions, and $X \le Y$. Then
\[
\int X\, d\mu \le \int Y\, d\mu.
\]
\end{thmbox}

\textit{Proof} By the definition of Lebesgue integral for nonnegative functions, we have
\[
\int X\, d\mu \triangleq \sup \left\{ \int f\, d\mu : f \in S(X) \right\},
\]
\[
\int Y\, d\mu \triangleq \sup \left\{ \int g\, d\mu : g \in S(Y) \right\}.
\]

Since $X \le Y$, we have $S(X) \subseteq S(Y)$. Therefore, for any $f \in S(X)$, we have $f \in S(Y)$, and so
\[
\int f\, d\mu \le \sup \left\{ \int g\, d\mu : g \in S(Y) \right\}.
\]

Taking the supremum over $S(X)$, we get $\int X\, d\mu \le \int Y\, d\mu$. \hfill $\square
-/


open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

-- Source Definition 6.3: simple ENNReal functions lying below the target function.
-- Nonnegativity is encoded by the codomain `ENNReal`; simplicity by `SimpleFunc`.
def sourceSimpleApproximationSet (X : Ω → ENNReal) : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}

noncomputable def sourceSimpleApproximationIntegral
    (μ : Measure Ω) (f : SimpleFunc Ω ENNReal) : ENNReal :=
  f.lintegral μ

noncomputable def sourceSupIntegral (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ⨆ f : sourceSimpleApproximationSet X, sourceSimpleApproximationIntegral μ f.1

lemma sourceSimpleApproximationSet_mono {X Y : Ω → ENNReal} (hXY : X ≤ Y) :
    sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y := by
  intro f hf ω
  exact le_trans (hf ω) (hXY ω)

lemma sourceSupIntegral_mono (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hsub : sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y) :
    sourceSupIntegral μ X ≤ sourceSupIntegral μ Y := by
  unfold sourceSupIntegral
  refine iSup_le ?_
  intro f
  exact le_iSup
    (fun g : sourceSimpleApproximationSet Y =>
      sourceSimpleApproximationIntegral μ g.1)
    ⟨f.1, hsub f.2⟩

lemma sourceSupIntegral_eq_lintegral (μ : Measure Ω) (X : Ω → ENNReal) :
    sourceSupIntegral μ X = ∫⁻ ω, X ω ∂μ := by
  unfold sourceSupIntegral sourceSimpleApproximationIntegral sourceSimpleApproximationSet
  rw [MeasureTheory.lintegral]
  exact (iSup_subtype'
    (α := ENNReal)
    (ι := SimpleFunc Ω ENNReal)
    (p := fun f => ∀ ω, f ω ≤ X ω)
    (f := fun f _ => f.lintegral μ)).symm

theorem thm_6_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hXY : X ≤ Y) :
    ∫⁻ ω, X ω ∂μ ≤ ∫⁻ ω, Y ω ∂μ := by
  rw [← sourceSupIntegral_eq_lintegral μ X, ← sourceSupIntegral_eq_lintegral μ Y]
  exact sourceSupIntegral_mono μ (sourceSimpleApproximationSet_mono hXY)
