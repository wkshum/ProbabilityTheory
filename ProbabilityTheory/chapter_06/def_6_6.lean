import Mathlib.Tactic
import ProbabilityTheory.chapter_06.def_6_5
/-

 # Lebesgue integral of complex-valued function

-/


/-
\begin{defbox}{6.6 (Complex Lebesgue Integral)}
Suppose $Z(\omega)=X(\omega)+iY(\omega)$, where $X(\omega)$ and $Y(\omega)$ are the real and imaginary parts of $Z(\omega)$, respectively. If both $X$ and $Y$ are integrable, then we say that $Z$ is \textit{integrable} and define the Lebesgue integral of $Z$ by
\[
\int Z\, d\mu \triangleq \int X\, d\mu + i\int Y\, d\mu
\]
and write $Z \in L^1(\mu)$. The integral of $Z$ is not defined if $X$ or $Y$ is not integrable.
\end{defbox}
-/

open MeasureTheory

namespace Def66RealSupport

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤

noncomputable def textbookValue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ℝ :=
  (((posLIntegral μ X : EReal) - (negLIntegral μ X : EReal)).toReal)

end Def66RealSupport

/-- Using the definition in textbook, a complex-valued
 function is integrable if its real and imaginary
parts are integrable. -/
def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  Def66RealSupport.textbookIntegrable μ (fun ω => ((Z ω).re : EReal)) ∧
    Def66RealSupport.textbookIntegrable μ (fun ω => ((Z ω).im : EReal))

/-- Textbook complex integral
undefined if either component is not integrable. -/
noncomputable def complexTextbookIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Option ℂ := by
  classical
  exact
    if hZ : complexTextbookIntegrable μ Z then
      some
        (Complex.ofReal
            (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).re : EReal))) +
          Complex.I *
            Complex.ofReal
              (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).im : EReal))))
    else
      none

/-- ## Definition 6.6. -/
noncomputable def def_6_6 {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (Z : Ω → ℂ) :
    Option ℂ :=
  complexTextbookIntegral μ Z

theorem complexTextbookIntegral_eq_none_of_not_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : ¬ complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = none := by
  classical
  simp [complexTextbookIntegral, hZ]

theorem complexTextbookIntegral_eq_some_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : complexTextbookIntegrable μ Z) :
    ∃ w : ℂ, complexTextbookIntegral μ Z = some w := by
  classical
  refine ⟨Complex.ofReal
      (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).re : EReal))) +
    Complex.I *
      Complex.ofReal
        (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).im : EReal))), ?_⟩
  simp [complexTextbookIntegral, hZ]
