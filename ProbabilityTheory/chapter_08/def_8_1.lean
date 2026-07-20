import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-

 # Definition 8.1 Coupling of two probability measures

-/


/-

\begin{defbox}{8.1}
Given two probability spaces $(\mathcal{X},\mathcal{F},P)$ and $(\mathcal{Y},\mathcal{G},Q)$, a \textit{coupling} of $P$ and $Q$ consists of a common probability space $(\Omega,\mathcal{H},\mu)$ and two measurable functions $X:\Omega\to \mathcal{X}$ and $Y:\Omega\to \mathcal{Y}$ such that the push-forward measures $X_{\#}\mu$ and $Y_{\#}\mu$ are equal to $P$ and $Q$, respectively.
\[
(\Omega,\mathcal{H},\mu)
\]
\[
\overset{X}{\swarrow} \qquad \qquad \overset{Y}{\searrow}
\]
\[
(\mathcal{X},\mathcal{F},P) \qquad \qquad (\mathcal{Y},\mathcal{G},Q)
\]
\end{defbox}
-/


open MeasureTheory

/--   ## Definition 8.1  Coupling
A coupling of two probability measures `P` and `Q` consists
of a common probability space `(Ω, 𝓗, μ)` together with
measurable maps to the two target spaces whose push-forward measures
are exactly `P` and `Q`.
-/
structure Coupling
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] where
  Ω : Type*
  instMeasurableSpaceΩ : MeasurableSpace Ω
  μ : Measure Ω
  instIsProbabilityMeasureμ : IsProbabilityMeasure μ
  X : Ω → α
  Y : Ω → β
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  map_X : Measure.map X μ = P
  map_Y : Measure.map Y μ = Q

attribute [instance] Coupling.instMeasurableSpaceΩ Coupling.instIsProbabilityMeasureμ

/-- Exported definition for Definition 8.1. -/
noncomputable def def_8_1
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :=
  Coupling P Q
