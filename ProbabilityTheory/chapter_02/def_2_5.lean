import Mathlib.Tactic
-- import Mathlib.MeasureTheory.MeasurableSpace.Defs
-- import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-

 Definition 2.5 Measure and Probability Measure on a sigma-algebra

-/

/-
\begin{defbox}{2.5}
Let $\mathcal{F}$ be a $\sigma$-field on a sample space $\Omega$. A set function $m$ from $\mathcal{F}$ to $[0,\infty]$ is called a \textit{measure} if it satisfies the following properties:
\begin{enumerate}[label=\arabic*.]
    \item $m(\emptyset)=0$.
    \item For any sequence of mutually disjoint $A_i\in \mathcal{F}$, for $i=1,2,3,\dots$, we have
    \[
    m\left(\biguplus_{i=1}^{\infty} A_i\right)
    =
    \sum_{i=1}^{\infty} m(A_i).
    \]
\end{enumerate}

This property is known as the $\sigma$-\textit{additive} property.

A measure $m$ is said to be \textit{finite} if $m(\Omega)$ is finite. If $m(\Omega)=1$, then $m$ is called a \textit{probability measure}.

A \textit{measure space} is a triple $(\Omega,\mathcal{F},m)$ where $\mathcal{F}$ is a $\sigma$-field on $\Omega$ and $m$ is a measure on $\mathcal{F}$. A \textit{probability space} is a measure space $(\Omega,\mathcal{F},m)$ when $\mathcal{F}$ is a $\sigma$-field on $\Omega$ and $m$ is a probability measure.
\end{defbox}
-/


open MeasureTheory Set

/-- Lean's `Measure Ω` plays the role of a textbook measure on a sigma-field over `Ω`. -/
abbrev MeasureOn (Ω : Type*) [MeasurableSpace Ω] := Measure Ω

/-- A measure is finite if the whole space has finite mass. -/
def IsFiniteMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  μ Set.univ < ⊤

/-- A probability measure is a measure of total mass `1`. -/
def IsProbabilityMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ

/-- A measure space packages a measurable space together with a measure. -/
structure MeasureSpaceData (Ω : Type*) [MeasurableSpace Ω] where
  measure : Measure Ω

/-- A probability space packages a measurable space with a probability measure.
 We obtain this data structure by extending `MeasureSpaceData` and adding
 the condition that the measure of the whole space is 1.
-/
structure ProbabilitySpaceData (Ω : Type*) [MeasurableSpace Ω]
  extends MeasureSpaceData Ω where
  (is_probability : IsProbabilityMeasure measure)

-- structure ProbabilitySpaceData (Ω : Type*) [MeasurableSpace Ω] where
--   measure : Measure Ω
--   is_probability : IsProbabilityMeasure measure

/-- # Definition 2.5 Measure functino
Exported definition for Definition 2.5. -/
def def_2_5 {Ω : Type*} [MeasurableSpace Ω] := Measure Ω


/-
  The measure function make takes the infinity as its value
  We have the following convention with ∞
-/

section checking_ENNReal

open ENNReal

-- c + ∞ = ∞
example (c : ENNReal) : c + ∞ = ∞ := by
  exact add_top c

-- ∞ · ∞ = ∞
example : ∞ * ∞ = ∞ := by
  exact top_mul_top


end checking_ENNReal
