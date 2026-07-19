import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.SimpleFunc


/-

  # Simple function

-/

/-
\begin{defbox}{6.1}
Let $(\Omega,\mathcal{F},\mu)$ be a measure space. A function $X:\Omega \to \bar{\mathbb{R}}$ is called a \textit{simple function} if its range is finite and it is $\mathcal{F}$-measurable.

Suppose $X$ takes on $n$ distinct values, denoted by $a_1,a_2,\ldots,a_n$, for some integer $n$. Since $X$ is a function with values in $\bar{\mathbb{R}}$, one of the $a_i$'s may be $\infty$ or $-\infty$. For $i=1,2,\ldots,n$, let $A_i$ be the pre-image $X^{-1}(\{a_i\}) \triangleq \{\omega : X(\omega)=a_i\}$. Because a simple function is $\mathcal{F}$-measurable by definition, the sets $A_i$'s are also $\mathcal{F}$-measurable and form a partition of the sample space $\Omega$. We can write $X(\omega)$ as a linear combination of indicator functions
\begin{equation}
X(\omega)=\sum_{i=1}^{n} a_i 1_{A_i}(\omega).
\tag{6.1}
\end{equation}
\end{defbox}
-/


open MeasureTheory
open scoped BigOperators

/-- ## Definition 6.1
In Mathlib, a simple function on a measurable space `(Ω, 𝓕)` is an
`EReal`-valued measurable function with finite range. This is
exactly the same as the meaning in Definition 6.1
Mathlib already packages exactly this notion as `MeasureTheory.SimpleFunc`.
-/
abbrev SimpleFunction (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  MeasureTheory.SimpleFunc Ω EReal

/-- ## Definition 6.1. -/
def def_6_1 (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  SimpleFunction Ω

namespace SimpleFunction

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A simple function is measurable. -/
theorem measurable_of_simpleFunction (X : SimpleFunction Ω) : Measurable X :=
  MeasureTheory.SimpleFunc.measurable X

/-- A simple function has finite range. -/
theorem finite_range_of_simpleFunction (X : SimpleFunction Ω) : (Set.range X).Finite :=
  MeasureTheory.SimpleFunc.finite_range X

/-- Each singleton fiber of a simple function is measurable. -/
theorem measurableSet_fiber (X : SimpleFunction Ω) (x : EReal) :
    MeasurableSet (X ⁻¹' {x}) := by
  exact X.measurable (measurableSet_singleton x)

/-- The textbook fiber notation agrees with the singleton preimage. -/
theorem setOf_eq_eq_preimage (X : SimpleFunction Ω) (x : EReal) :
    {ω | X ω = x} = X ⁻¹' {x} := by
  ext ω
  simp

/-- Distinct singleton fibers of a simple function are disjoint. -/
theorem disjoint_fiber_of_ne (X : SimpleFunction Ω) {x y : EReal}
  (hxy : x ≠ y) :
    Disjoint (X ⁻¹' {x}) (X ⁻¹' {y}) := by
  refine Set.disjoint_left.2 ?_
  intro ω hx hy
  exact hxy <| by
    have hx' : X ω = x := by simpa using hx
    have hy' : X ω = y := by simpa using hy
    exact hx'.symm.trans hy'

/-- The singleton fibers over the finite range cover the whole sample space. -/
theorem iUnion_fiber_range (X : SimpleFunction Ω) :
    (⋃ x ∈ X.range, X ⁻¹' ({x} : Set EReal)) = Set.univ := by
  ext ω
  simp

/--
Formula (6.1): a simple function equals the finite sum of its values times the
indicators of the corresponding singleton fibers.
-/
theorem sum_indicator_fiber (X : SimpleFunction Ω) :
    X = fun ω => ∑ x ∈ X.range, Set.indicator (X ⁻¹' ({x} : Set EReal)) (fun _ => x) ω := by
  classical
  funext ω
  rw [Finset.sum_eq_single (X ω)]
  · simp [Set.indicator_of_mem]
  · intro y hy hy_ne
    have hω : ω ∉ X ⁻¹' ({y} : Set EReal) := by
      intro h_mem
      exact hy_ne ((by simpa using h_mem) : X ω = y).symm
    simp [Set.indicator_of_notMem, hω]
  · intro h_not_mem
    exact (h_not_mem (X.mem_range_self ω)).elim

/-- The pair construction recovers the left component after mapping `Prod.fst`. -/
theorem map_fst_pair (X Y : SimpleFunction Ω) :
    (X.pair Y).map Prod.fst = X := by
  simp [MeasureTheory.SimpleFunc.map_fst_pair X Y]

/-- The pair construction recovers the right component after mapping `Prod.snd`. -/
theorem map_snd_pair (X Y : SimpleFunction Ω) :
    (X.pair Y).map Prod.snd = Y := by
  simp [MeasureTheory.SimpleFunc.map_snd_pair X Y]

/-- Pointwise addition of simple functions is `map` on the pair refinement. -/
theorem add_eq_map_pair (X Y : SimpleFunction Ω) :
    X + Y = (X.pair Y).map (fun p => p.1 + p.2) := by
  simpa using MeasureTheory.SimpleFunc.add_eq_map₂ X Y

end SimpleFunction
