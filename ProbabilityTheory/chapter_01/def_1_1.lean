import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-
# Definition 1.1: Singular Random Variable

\begin{defbox}{1.1}

A real-valued random variable $X$ is said to be \textit{singular}
if there exists a set $S$ with length $0$ such that $X$ takes
a value in $S$ with probability $1$. Similarly, a random vector
$\mathbf{X}$ with values in $\mathbb{R}^n$ is called \textit{singular}
 if there exists a set $S$ with zero volume such that
 $\Pr(\mathbf{X}\in S)=1$.

\end{defbox}
-/

/-
We skip the hypothesis `Measurable X`
to the definition. It is defined
for any function X, not just for measurable function.
-/

open MeasureTheory Set

/-- A real-valued random variable is singular if it is supported
with probability `1`on a set of Lebesgue measure `0`.
-/
def IsSingularRealRandomVariable {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) :
    Prop :=
  ∃ S : Set ℝ, volume S = 0 ∧ P (X ⁻¹' S) = 1


/-- A random vector is singular if it is supported with probability `1`
on a subset of Euclidean space with volume `0`. -/
def IsSingularRandomVector {Ω : Type*}
  [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ S : Set (EuclideanSpace ℝ (Fin n)), volume S = 0 ∧ P (X ⁻¹' S) = 1

/--  ## Definition 1.1 (Singular Random Variable)
  Exported definition for Definition 1.1.
-/
def def_1_1 {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  IsSingularRealRandomVariable P X
