import ToyApollo.Output.thm_1_1_bad_cells

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

namespace Thm11SourceRoute


/-- The key closed-interval Darboux oscillation estimate needed for Theorem
1.1 after the strict-interval repair: fine partitions make the total
Stieltjes-weighted oscillation of `f` small. -/
def ClosedIntervalDarbouxOscillationSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : DarbouxRS.Partition a b,
    P.mesh < δ → partitionOscillation P f α < eps

/-- The same fine-partition smallness condition expressed directly as a
Darboux upper-minus-lower gap. This is generic Darboux infrastructure, not a
finite-discontinuity-specific estimate. -/
def ClosedIntervalDarbouxGapSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : DarbouxRS.Partition a b,
    P.mesh < δ →
      DarbouxRS.upperSum P f α - DarbouxRS.lowerSum P f α < eps

/-- A purely Darboux fine-Cauchy condition for upper and lower sums. It is
stronger than the same-partition gap estimate, but it is the exact
cross-partition comparison needed to extract a common limit from completeness
of `ℝ`. -/
def ClosedIntervalDarbouxFineCauchy
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P Q : DarbouxRS.Partition a b,
    P.mesh < δ →
    Q.mesh < δ →
      |DarbouxRS.upperSum P f α - DarbouxRS.upperSum Q f α| < eps ∧
      |DarbouxRS.lowerSum P f α - DarbouxRS.lowerSum Q f α| < eps ∧
      |DarbouxRS.upperSum P f α - DarbouxRS.lowerSum Q f α| < eps ∧
      |DarbouxRS.lowerSum P f α - DarbouxRS.upperSum Q f α| < eps

/-- Under source hypotheses, the upper-minus-lower Darboux gap is
nonnegative for every partition. -/
lemma upperSum_sub_lowerSum_nonneg_of_source {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    (P : DarbouxRS.Partition a b) :
    0 ≤ DarbouxRS.upperSum P f α - DarbouxRS.lowerSum P f α := by
  have hle : DarbouxRS.lowerSum P f α ≤ DarbouxRS.upperSum P f α :=
    DarbouxRS.lowerSum_le_upperSum_core P hs
  exact sub_nonneg.mpr hle

/-- Gap-smallness plus source hypotheses give the absolute-value version of
the same-partition upper/lower gap estimate. -/
theorem closedIntervalDarbouxAbsGapSmall_of_gapSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    (hgap : ClosedIntervalDarbouxGapSmall a b f α) :
    ∀ eps > 0, ∃ δ > 0, ∀ P : DarbouxRS.Partition a b,
      P.mesh < δ →
        |DarbouxRS.upperSum P f α - DarbouxRS.lowerSum P f α| < eps := by
  intro eps heps
  rcases hgap eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  rw [abs_of_nonneg (upperSum_sub_lowerSum_nonneg_of_source hs P)]
  exact Hδ P hmesh

/-- Oscillation-small partitions are exactly gap-small in the direction needed
for the Darboux criterion, since the oscillation sum is the upper-lower gap. -/
theorem closedIntervalDarbouxGapSmall_of_oscillationSmall
    {f α : ℝ → ℝ} {a b : ℝ}
    (hosc : ClosedIntervalDarbouxOscillationSmall a b f α) :
    ClosedIntervalDarbouxGapSmall a b f α := by
  intro eps heps
  rcases hosc eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  rw [upperSum_sub_lowerSum_eq_partitionOscillation]
  exact Hδ P hmesh


end Thm11SourceRoute
