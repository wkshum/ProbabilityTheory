import ToyApollo.Output.thm_1_1
import ToyApollo.Output.thm_7_9_regularity_support

open MeasureTheory Set Topology

noncomputable section

/-!
Finite-discontinuity regularity route for Theorem 7.9.

The source discussion before Theorem 7.9 treats piece-wise continuous
integrands by cutting the line at finitely many discontinuities and requiring
those discontinuities not to coincide with jumps of the Stieltjes function.
This file records the corresponding `thm_1_1`-level input surface and turns it
into `Thm79SourceRegular`.

It does not prove the finite Lebesgue-Stieltjes/Riemann-Stieltjes equality,
does not settle endpoint conventions, and does not complete Theorem 7.9.
-/

/-- Finite-discontinuity input surface for the finite intervals used in
Theorem 7.9.

For every strict finite interval it exposes boundedness, finite discontinuity
sets, and continuity of `F` at the discontinuities of both `g` and `|g|`. This
is the form directly consumed by `thm_1_1`. -/
structure Thm79FiniteDiscontinuityInputs
    (F : StieltjesFunction ℝ) (g : ℝ → ℝ) : Prop where
  measurable : Measurable g
  finite_bounds : ∀ ⦃a b : ℝ⦄, a < b →
    BddAbove (g '' Icc a b) ∧ BddBelow (g '' Icc a b)
  finite_abs_bounds : ∀ ⦃a b : ℝ⦄, a < b →
    BddAbove ((fun x => |g x|) '' Icc a b) ∧
      BddBelow ((fun x => |g x|) '' Icc a b)
  finite_discontinuities : ∀ ⦃a b : ℝ⦄, a < b →
    (discontinuitySetOn g a b).Finite
  finite_abs_discontinuities : ∀ ⦃a b : ℝ⦄, a < b →
    (discontinuitySetOn (fun x => |g x|) a b).Finite
  F_cont_at_discontinuities : ∀ ⦃a b x : ℝ⦄, a < b →
    x ∈ discontinuitySetOn g a b → ContinuousAt F x
  F_cont_at_abs_discontinuities : ∀ ⦃a b x : ℝ⦄, a < b →
    x ∈ discontinuitySetOn (fun x => |g x|) a b → ContinuousAt F x

namespace Thm79FiniteDiscontinuityInputs

/-- The finite-discontinuity/no-common-jump surface supplies the
`Thm79SourceRegular` inputs needed by the finite absolute bridge route. -/
theorem to_source_regular {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) :
    Thm79SourceRegular F g := by
  refine ⟨h.measurable, ?_, ?_⟩
  · intro a b hab
    have hbounds := h.finite_bounds hab
    exact thm_1_1 hab F.mono hbounds.1 hbounds.2
      (h.finite_discontinuities hab)
      (fun {x} hx => h.F_cont_at_discontinuities (a := a) (b := b) (x := x) hab hx)
  · intro a b hab
    have hbounds := h.finite_abs_bounds hab
    exact thm_1_1 hab F.mono hbounds.1 hbounds.2
      (h.finite_abs_discontinuities hab)
      (fun {x} hx =>
        h.F_cont_at_abs_discontinuities (a := a) (b := b) (x := x) hab hx)

/-- A direct finite-interval RS consequence for the original integrand. -/
theorem finite_rs {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {a b : ℝ} (hab : a < b) :
    RSIntegrable g F a b :=
  h.to_source_regular.finite_rs hab

/-- A direct finite-interval RS consequence for the absolute integrand. -/
theorem finite_abs_rs {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {a b : ℝ} (hab : a < b) :
    RSIntegrable (fun x => |g x|) F a b :=
  h.to_source_regular.finite_abs_rs hab

end Thm79FiniteDiscontinuityInputs
