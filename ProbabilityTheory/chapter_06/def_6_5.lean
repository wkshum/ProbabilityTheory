import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-

 # Definition 6.5 Lebesgue integral of real-valued function

defined in terms of the integrals of the positive part and the negative part
-/


/-
\begin{defbox}{6.5 (Real Lebesgue Integral)}
We define the \textit{Lebesgue integral} of a measurable $\bar{\mathbb{R}}$-valued
function $X$ on a measure space $(\Omega,\mathcal{F},\mu)$ by
\[
\int X\, d\mu \triangleq \int X^+\, d\mu - \int X^-\, d\mu.
\]

It is well-defined unless we have $\infty-\infty$ on the right-hand side.
When $\int X^+$ and $\int X^-$ are both finite, we say that $X$ is
$\mu$-\textit{integrable} and write $X \in L^1(\mu)$.
\end{defbox}
-/

open MeasureTheory

namespace Def65Support

/-- Positive contribution extracted from an `EReal`-valued function. -/
noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal)
  : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

/-- Negative contribution extracted from an `EReal`-valued function. -/
noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal)
  : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

/-- The nonnegative integral of the positive part. -/
noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ

/-- The nonnegative integral of the negative part. -/
noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ

end Def65Support

/-- Textbook Definition 6.5: the signed integral is undefined exactly in the
`∞ - ∞` case, represented here by `none`. -/
noncomputable def textbookIntegral {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (X : Ω → EReal) : Option EReal :=
  if _hUndefined :
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤ then
    none
  else
    let p := Def65Support.posLIntegral μ X
    let n := Def65Support.negLIntegral μ X
    some ((p : EReal) - (n : EReal))

/-- Textbook integrability means both positive and negative parts have finite
nonnegative integral. -/
def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal) :
    Prop :=
  Def65Support.posLIntegral μ X < ⊤ ∧ Def65Support.negLIntegral μ X < ⊤

/-- ## Definition 6.5.
  export definition 6.5
-/
noncomputable def def_6_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  textbookIntegral μ X

/-- Integration over a measurable set is defined by multiplying by the indicator
of the set, following the textbook convention introduced after Example 6.3.1. -/
noncomputable def textbookIntegralOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (X : Ω → EReal) : Option EReal :=
  textbookIntegral μ (s.indicator X)

section TextbookIntegralLemmas

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → EReal}

theorem textbookIntegral_eq_none_iff :
    textbookIntegral μ X = none ↔
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤
  := by
  unfold textbookIntegral
  by_cases hUndefined :
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤
  · simp [hUndefined]
  · simp [hUndefined]

theorem textbookIntegrable_pos_ne_top (hX : textbookIntegrable μ X) :
    Def65Support.posLIntegral μ X ≠ ⊤ := by
  exact ne_of_lt hX.1

theorem textbookIntegrable_neg_ne_top (hX : textbookIntegrable μ X) :
    Def65Support.negLIntegral μ X ≠ ⊤ := by
  exact ne_of_lt hX.2

theorem textbookIntegrable_implies_some (hX : textbookIntegrable μ X) :
    ∃ v : EReal, textbookIntegral μ X = some v := by
  unfold textbookIntegral
  have hUndefined :
      ¬ (Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤) := by
    intro hBothTop
    exact (textbookIntegrable_pos_ne_top hX) hBothTop.1
  refine ⟨(Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal), ?_⟩
  simp [hUndefined]

theorem textbookIntegral_of_nonneg
    (_hX : ∀ ω, 0 ≤ X ω)
    (hneg_zero :
      Def65Support.negLIntegral μ X = 0) :
    textbookIntegral μ X = some (Def65Support.posLIntegral μ X : EReal) := by
  unfold textbookIntegral
  have hUndefined :
      ¬ (Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤) := by
    intro hBothTop
    simpa [hneg_zero] using hBothTop.2
  simp [hneg_zero]

end TextbookIntegralLemmas
