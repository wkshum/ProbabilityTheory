import Mathlib.Tactic
import Mathlib.Probability.Moments.Covariance
import ProbabilityTheory.chapter_07.thm_7_13

/-

 # Definition 7.3
 Uncorrelatedness and expectation of product of independent random variables

-/

/-
\begin{defbox}{7.3}
We say that two real-valued random variables $X$ and $Y$ are \textit{uncorrelated} if
\[
E[XY]=E[X]E[Y].
\]

The notion of uncorrelated random variables is closely related to the \textit{covariance}, which is defined as
\[
\operatorname{Cov}(X,Y)\triangleq E[(X-E[X])(Y-E[Y])].
\]

It is straightforward to show that $\operatorname{Cov}(X,Y)=0$ if and only if $X$ and $Y$ are uncorrelated. Theorem 7.13 says that two independent random variables are uncorrelated, but the converse does not hold in general.
\end{defbox}
-/


open MeasureTheory ProbabilityTheory

/-- Textbook notion: `X` and `Y` are uncorrelated when `E[XY] = E[X] E[Y]`. -/
def Uncorrelated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ

/-- Textbook covariance, using Mathlib's probability-theory definition. -/
noncomputable def Covariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ProbabilityTheory.covariance X Y μ

/-- On a probability space, zero covariance is equivalent to being uncorrelated. -/
theorem covariance_zero_iff_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Covariance μ X Y = 0 ↔ Uncorrelated μ X Y := by
  rw [Covariance, ProbabilityTheory.covariance_eq_sub hX hY, Uncorrelated]
  rw [sub_eq_zero]
  simp [Pi.mul_apply]

/-- Theorem 7.13 implies that independent random variables are uncorrelated. -/
theorem independent_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hXY : def_5_2 μ X Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY_int : Integrable (fun ω => X ω * Y ω) μ) :
    Uncorrelated μ X Y := by
  exact thm_7_13 hXY hX hY hXY_int

/-- Exported definition for Definition 7.3. -/
def def_7_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  Uncorrelated μ X Y
