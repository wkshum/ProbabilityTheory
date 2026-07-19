import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-

 # Lebesgue integral of nonnegative function

-/

/-
\begin{defbox}{6.3}
For a nonnegative measurable function $X$, we define the \textit{Lebesgue integral} of $X$ by
\[
\int X\, d\mu \triangleq \sup \left\{ \int f\, d\mu : f \text{ is simple},\ 0\le f\le X \right\}.
\]
\end{defbox}
-/


open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- ## Equation 6.3 in textbook
The textbook approximation class. Given a nonnegative
measurable function `X`, define `S(X)` as the set
of nonnegative simple functions that is less than or equal to `X`.

`S(X) = {f : f is simple, 0 ≤ f ≤ X}` for a nonnegative function `X`.

-/
def simpleApproximationSet (X : Ω → ENNReal)
    : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}


/--
Lebesgue integral for nonnegative Lebesgue integral:

`sup { ∫ f dμ : f simple, f ≤ X }`.

Here `f.lintegral μ` is the integral of a simple function.
-/
noncomputable def textbookIntegralNonnegative
    (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ⨆ (f : SimpleFunc Ω ENNReal) (_hf : f ∈ simpleApproximationSet X),
    f.lintegral μ

/--
If the simple-function integrals below `X` are unbounded in the finite part
of `ENNReal`, then the textbook integral is `⊤`.

In `ENNReal`, every set is bounded above by `⊤`, so "unbounded" should be
formalized as: for every finite `C < ⊤`, there is an admissible simple function
whose integral is strictly bigger than `C`.
-/
theorem textbookIntegralNonnegative_eq_top_of_unbounded
    {μ : Measure Ω} {X : Ω → ENNReal}
    (h :
      ∀ C : ENNReal, C < ⊤ →
        ∃ f : SimpleFunc Ω ENNReal,
          f ∈ simpleApproximationSet X ∧ C < f.lintegral μ) :
    textbookIntegralNonnegative μ X = ⊤ := by
  by_contra htop
  have hlt : textbookIntegralNonnegative μ X < ⊤ := by
    exact (lt_top_iff_ne_top).2 htop
  rcases h (textbookIntegralNonnegative μ X) hlt with ⟨f, hfS, hf_lt⟩
  have hf_le :
      f.lintegral μ ≤ textbookIntegralNonnegative μ X := by
    exact le_iSup_of_le f (le_iSup_of_le hfS le_rfl)
  exact not_lt_of_ge hf_le hf_lt


/--
Compatibility between the textbook definition of the nonnegative Lebesgue
integral and Mathlib's lower Lebesgue integral.

In the textbook development, the Lebesgue integral of a nonnegative function
`X : Ω → ENNReal` is introduced as the supremum of the integrals of all
nonnegative simple functions lying below `X`:
\[
  \sup \left\{ \int f\,d\mu :
    f \text{ is simple and } f \le X \right\}.
\]
In this file, that textbook approximation class is encoded by
`simpleApproximationSet X`, and the corresponding supremum is encoded by
`textbookIntegralNonnegative μ X`.

Mathlib already implements this construction as the lower Lebesgue integral
`∫⁻ ω, X ω ∂μ`.  The theorem below proves that our textbook formulation and
Mathlib's formulation are definitionally/theorematically the same: after
unfolding `MeasureTheory.lintegral_def`, both sides are the same supremum over
`SimpleFunc Ω ENNReal` bounded above by `X`.

Thus, from this point onward, we may freely use Mathlib's notation and API for
the lower Lebesgue integral while retaining the standard textbook
interpretation.  In particular, replacing `textbookIntegralNonnegative μ X` by
`∫⁻ ω, X ω ∂μ` is not a change of mathematical meaning, but only a transition
from the pedagogical definition to Mathlib's established implementation.
-/
theorem textbookIntegralNonnegative_eq_lintegral
    (μ : Measure Ω) (X : Ω → ENNReal) :
    textbookIntegralNonnegative μ X = ∫⁻ ω, X ω ∂μ := by
  simp [
    textbookIntegralNonnegative,
    simpleApproximationSet,
    MeasureTheory.lintegral_def,
    Pi.le_def
  ]



/--
  ## Definition 6.3
the Lebesgue integral of a nonnegative measurable function,
implemented in Mathlib by lower Lebesgue integral `lintegral`.
-/
noncomputable def def_6_3 (μ : Measure Ω) (X : Ω → ENNReal)
    : ENNReal :=
  ∫⁻ ω, X ω ∂μ
