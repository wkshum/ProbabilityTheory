import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Heine-Borel Theorem (Theorem 3.4)

Let A be a subset of ℝ. Then A is compact (defined in analysis as closed and bounded)
if and only if every open cover of A has a finite subcover.
-/

open Set Metric Bornology

/--
In the context of Theorem 3.4 (Heine-Borel) in real analysis,
a set is often defined as "compact" if it is both closed and bounded.
-/
def IsCompactTextbook (A : Set ℝ) : Prop :=
  IsClosed A ∧ IsBounded A

/-- ## Theorem 3.4 (Heine-Borel):
Let A be a subset of ℝ. Then A is compact (meaning closed and bounded)
if and only if every open cover of A has a finite subcover.

Mathlib's `Metric.isCompact_iff_isClosed_bounded` provides the equivalence
between being topologically compact and being closed and bounded in proper
metric spaces.
-/
theorem heine_borel (A : Set ℝ) :
    IsCompactTextbook A ↔
    (∀ {ι : Type} (U : ι → Set ℝ), (∀ i, IsOpen (U i)) → (A ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i) := by
  -- 1. Unfold our textbook definition of compactness
  rw [IsCompactTextbook]
  -- 2. Use the Heine-Borel theorem for proper spaces (like ℝ)
  -- to relate Closed + Bounded to Mathlib's IsCompact
  rw [← Metric.isCompact_iff_isClosed_bounded]
  -- 3. Use the topological definition of IsCompact to relate it to
  -- the finite subcover property
  exact isCompact_iff_finite_subcover
