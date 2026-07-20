import ToyApollo.Output.thm_7_8
import ToyApollo.Output.thm_7_9_truncation_support

open MeasureTheory Set

noncomputable section

/-!
Source-regularity support for Theorem 7.9.

The source statement of Theorem 7.9 assumes enough piecewise regularity for the
finite Riemann-Stieltjes integrals used in the truncation argument.  This file
does not prove the finite Lebesgue-Stieltjes/Riemann-Stieltjes equality and does
not handle endpoint atoms.  It only records the regularity surface needed before
the finite bridge can be applied to `g` and `|g|`.
-/

/-- Source-facing finite-interval regularity needed by Theorem 7.9.

This is intentionally weaker than a completed finite bridge: it gives
measurability and finite RS existence for `g` and `|g|`, but it does not assert
any LS/RS equality or endpoint convention. -/
structure Thm79SourceRegular (F : StieltjesFunction ℝ) (g : ℝ → ℝ) : Prop where
  measurable : Measurable g
  finite_rs : ∀ ⦃a b : ℝ⦄, a < b → RSIntegrable g F a b
  finite_abs_rs : ∀ ⦃a b : ℝ⦄, a < b → RSIntegrable (fun x => |g x|) F a b

namespace Thm79SourceRegular

theorem abs_measurable {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (hreg : Thm79SourceRegular F g) :
    Measurable (fun x => |g x|) :=
  hreg.measurable.abs

theorem abs_finite_rs {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (hreg : Thm79SourceRegular F g) {a b : ℝ} (hab : a < b) :
    RSIntegrable (fun x => |g x|) F a b :=
  hreg.finite_abs_rs hab

theorem trunc_measurable {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (hreg : Thm79SourceRegular F g) (n : ℕ) :
    Measurable (thm_7_9_trunc g n) :=
  thm_7_9_trunc_measurable hreg.measurable n

theorem abs_trunc_measurable {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (hreg : Thm79SourceRegular F g) (n : ℕ) :
    Measurable (thm_7_9_trunc (fun x => |g x|) n) :=
  thm_7_9_trunc_measurable hreg.abs_measurable n

theorem abs_trunc_rs {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (hreg : Thm79SourceRegular F g) {n : ℕ} (hn : 0 < n) :
    RSIntegrable (thm_7_9_trunc (fun x => |g x|) n) F (-(n : ℝ)) (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlt : -(n : ℝ) < (n : ℝ) := by
    linarith
  refine rsIntegrable_congr_integrand_Icc (hreg.finite_abs_rs hlt) ?_
  intro x hx
  exact Set.indicator_of_mem hx (fun y => |g y|)

theorem trunc_rs {F : StieltjesFunction ℝ} {g : ℝ → ℝ}
    (hreg : Thm79SourceRegular F g) {n : ℕ} (hn : 0 < n) :
    RSIntegrable (thm_7_9_trunc g n) F (-(n : ℝ)) (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlt : -(n : ℝ) < (n : ℝ) := by
    linarith
  refine rsIntegrable_congr_integrand_Icc (hreg.finite_rs hlt) ?_
  intro x hx
  exact Set.indicator_of_mem hx g

theorem of_continuous (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) :
    Thm79SourceRegular F g := by
  refine ⟨hg.measurable, ?_, ?_⟩
  · intro a b hab
    exact thm_7_8_rs_exists F hab hg.continuousOn
  · intro a b hab
    exact thm_7_8_rs_exists F hab hg.abs.continuousOn

end Thm79SourceRegular
