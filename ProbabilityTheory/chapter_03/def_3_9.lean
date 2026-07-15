import Mathlib.MeasureTheory.Measure.NullMeasurable

/-

  # Definition 3.9 Null set and Complete space

-/

open MeasureTheory Set

/--
A set N ⊆ Ω is a null set if there exists a set E ∈ F such that N ⊆ E and μ(E) = 0.
-/
def IsNullSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : Set Ω) : Prop :=
  ∃ E, MeasurableSet E ∧ N ⊆ E ∧ μ E = 0

/--
The measure space (Ω, F, μ) is said to be complete if all null sets are indeed F-measurable.
-/
def IsCompleteSpace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ N, IsNullSet μ N → MeasurableSet N
