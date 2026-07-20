import Mathlib.Tactic
import ProbabilityTheory.chapter_01.rs_stieltjes_step_support
import ProbabilityTheory.chapter_07.thm_7_8_sandwich_support
import ProbabilityTheory.chapter_01.thm_1_1

open MeasureTheory Set
open Topology

noncomputable section

/-- First finite-interval support for Theorem 7.8: a continuous integrand on
`[a,b]` is Lebesgue-Stieltjes integrable on that compact interval. -/
theorem thm_7_8_integrability
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    IntegrableOn g (Icc a b) F.measure := by
  exact hg.integrableOn_compact isCompact_Icc

/-- Focused support for `t7_8_rs_exists`: a continuous integrand on the
closed interval is Riemann-Stieltjes integrable against a Stieltjes function.

The proof extends `g` from `Icc a b` to a globally continuous function by
projection onto the interval, applies the reviewed strict Theorem 1.1 route to
the extension, and transfers the witness back because Riemann-Stieltjes sums
only see the integrand on `Icc a b`. -/
theorem thm_7_8_rs_exists
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) :
    RSIntegrable g F a b := by
  let hle : a ≤ b := le_of_lt hab
  let gIcc : Icc a b → ℝ := fun x => g x
  let gExt : ℝ → ℝ := Set.IccExtend hle gIcc
  have hgIcc : Continuous gIcc := by
    exact continuousOn_iff_continuous_restrict.mp hg
  have hgExt : Continuous gExt := by
    exact Continuous.Icc_extend' hgIcc
  have hAbove : BddAbove (gExt '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hgExt.continuousOn).bddAbove
  have hBelow : BddBelow (gExt '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hgExt.continuousOn).bddBelow
  have hDiscFinite : (discontinuitySetOn gExt a b).Finite := by
    apply Thm11SourceRoute.finite_discontinuitySetOn_of_forall_continuousWithinAt
    intro x hx
    exact hgExt.continuousAt.continuousWithinAt
  have hFCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn gExt a b →
      ContinuousWithinAt F (Icc a b) x := by
    intro x hx
    exfalso
    exact hx.2 hgExt.continuousAt.continuousWithinAt
  have hExt : RSIntegrable gExt F a b :=
    thm_1_1 hab (F.mono.monotoneOn (Icc a b)) hAbove hBelow hDiscFinite hFCont
  refine rsIntegrable_congr_integrand_Icc hExt ?_
  intro x hx
  dsimp [gExt, gIcc]
  rw [Set.IccExtend_of_mem hle _ hx]

/-- Focused downstream packaging support for the finite-interval bridge. -/
theorem thm_7_8_downstream_instantiation_support
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hgInt : IntegrableOn g (Icc a b) F.measure)
    (hRS : RSIntegrable g F a b)
    (hSqueeze : ∀ P : DarbouxRS.Partition a b,
      DarbouxRS.lowerSum P g F ≤ ∫ x in Icc a b, g x ∂F.measure ∧
        ∫ x in Icc a b, g x ∂F.measure ≤ DarbouxRS.upperSum P g F) :
    IntegrableOn g (Icc a b) F.measure ∧
      ∃ hRS' : RSIntegrable g F a b,
        ∫ x in Icc a b, g x ∂F.measure = rsIntegral g F a b hRS' := by
  exact ⟨hgInt, ⟨hRS, thm_7_8_common_limit_squeeze_rsIntegral F hRS hSqueeze⟩⟩

/-- The source-facing finite interval theorem.  The full
Theorem 7.8 equality is reassembled only after the other child obligations
are landed. -/
theorem thm_7_8
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Icc a b))
    (hAtom : F.measure {a} = 0) :
    IntegrableOn g (Icc a b) F.measure ∧
      ∃ hRS : RSIntegrable g F a b,
        ∫ x in Icc a b, g x ∂F.measure = rsIntegral g F a b hRS := by
  have hgInt : IntegrableOn g (Icc a b) F.measure :=
    thm_7_8_integrability F hg
  have hRS : RSIntegrable g F a b :=
    thm_7_8_rs_exists F hab hg
  have hAbove : BddAbove (g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  have hSqueeze : ∀ P : DarbouxRS.Partition a b,
      DarbouxRS.lowerSum P g F ≤ ∫ x in Icc a b, g x ∂F.measure ∧
        ∫ x in Icc a b, g x ∂F.measure ≤ DarbouxRS.upperSum P g F := by
    intro P
    exact thm_7_8_cellStepWithLeft_integral_sandwich F P g hAtom
      (thm_7_8_lowerCellStepWithLeft_le_ae F P g hAtom hBelow)
      (thm_7_8_le_upperCellStepWithLeft_ae F P g hAtom hAbove)
      hgInt
  constructor
  · exact hgInt
  · exact ⟨hRS, thm_7_8_common_limit_squeeze_rsIntegral F hRS hSqueeze⟩
