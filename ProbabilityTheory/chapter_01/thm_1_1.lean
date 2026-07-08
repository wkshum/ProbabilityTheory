import ProbabilityTheory.chapter_01.thm_1_1_common_limit

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

/-
Support entry for Theorem 1.1.

The proof body is split across:

- `thm_1_1_basic`
- `thm_1_1_oscillation_basic`
- `thm_1_1_bad_cells`
- `thm_1_1_Daboux_gap`
- `thm_1_1_common_refinement_point`
- `thm_1_1_common_refinement_monotonicity`
- `thm_1_1_finite_discontinuity`
- `thm_1_1_common_limit`
-/

/--  # Theorem 1.1
Theorem 1.1 in the chapter's standing closed-interval context `a < b`. -/
theorem thm_1_1
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b :=
  Thm11SourceRoute.strict_thm_1_1
    hab hα_mono hAbove hBelow hDiscFinite hαCont
