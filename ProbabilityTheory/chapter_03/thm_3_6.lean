import ProbabilityTheory.chapter_03.def_3_9
-- import Mathlib.Tactic

open MeasureTheory
open Set

/--
PROBLEM: Let (Ω, F, μ) be a measure space and N be the set of all null sets. We can define a new
collection of sets F' = {A ∪ N : A ∈ F and N ∈ N}. We can extend the measure μ to a measure on F',
denoted by μ', by μ'(A ∪ N) = μ(A), and the extended measure space (Ω, F', μ') is complete.
-/
def completionCollection {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Set (Set Ω) :=
  {s | ∃ A N, MeasurableSet A ∧ IsNullSet μ N ∧ s = A ∪ N}

abbrev completionMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) := μ.completion

theorem measure_eq_zero_of_isNullSet {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : Set Ω}
    (hN : IsNullSet μ N) : μ N = 0 := by
  rcases hN with ⟨E, hE, hNE, hE0⟩
  exact measure_mono_null hNE hE0

theorem nullMeasurableSet_of_mem_completionCollection {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : s ∈ completionCollection μ) :
    NullMeasurableSet s μ := by
  rcases hs with ⟨A, N, hA, hN, rfl⟩
  exact hA.nullMeasurableSet.union (NullMeasurableSet.of_null (measure_eq_zero_of_isNullSet hN))

theorem mem_completionCollection_of_nullMeasurableSet {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : NullMeasurableSet s μ) :
    s ∈ completionCollection μ := by
  rcases NullMeasurableSet.exists_measurable_subset_ae_eq hs with ⟨A, hAsub, hAmeas, hAae⟩
  refine ⟨A, s \ A, hAmeas, ?_, (union_sdiff_cancel hAsub).symm⟩
  refine ⟨toMeasurable μ (s \ A), measurableSet_toMeasurable _ _, subset_toMeasurable _ _, ?_⟩
  have hdiff : μ (s \ A) = 0 := ae_le_set.1 hAae.symm.le
  simpa [measure_toMeasurable] using hdiff

theorem mem_completionCollection_iff_nullMeasurableSet {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) :
    s ∈ completionCollection μ ↔ NullMeasurableSet s μ := by
  constructor
  · exact nullMeasurableSet_of_mem_completionCollection
  · exact mem_completionCollection_of_nullMeasurableSet

theorem completion_apply_union_isNullSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A N : Set Ω} (_hA : MeasurableSet A) (hN : IsNullSet μ N) :
    completionMeasure μ (A ∪ N) = μ A := by
  have hN0 : μ N = 0 := measure_eq_zero_of_isNullSet hN
  rw [Measure.completion_apply]
  apply le_antisymm
  · calc
      μ (A ∪ N) ≤ μ A + μ N := measure_union_le A N
      _ = μ A := by rw [hN0, add_zero]
  · exact measure_mono (subset_union_left : A ⊆ A ∪ N)


/--

 ## Theorem 3.6 Extension to a complete measure

-/
theorem thm_3_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    (∀ s, s ∈ completionCollection μ ↔ NullMeasurableSet s μ) ∧
      (∀ A N, @MeasurableSet Ω ‹MeasurableSpace Ω› A →
        IsNullSet μ N → completionMeasure μ (A ∪ N) = μ A) ∧
      Measure.IsComplete (completionMeasure μ) := by
  refine
    ⟨fun s => mem_completionCollection_iff_nullMeasurableSet μ s,
      ?_,
      Measure.completion.isComplete μ⟩
  intro A N hA hN
  exact completion_apply_union_isNullSet μ hA hN
