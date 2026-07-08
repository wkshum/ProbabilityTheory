import Mathlib
import ProbabilityTheory.chapter_01.def_1_2

open Finset BigOperators
open MeasureTheory Set Topology

/-- The discontinuity set of `f` inside the interval `[a, b]`. -/
def discontinuitySetOn (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Icc a b ∧ ¬ ContinuousAt f x}

namespace Thm11SourceRoute

/-- Outside the finite bad set, membership in the interval gives continuity of `f`. -/
lemma continuousAt_of_not_mem_discontinuitySetOn {f : ℝ → ℝ} {a b x : ℝ}
    (hxI : x ∈ Icc a b) (hx : x ∉ discontinuitySetOn f a b) :
    ContinuousAt f x := by
  by_contra hcont
  exact hx ⟨hxI, hcont⟩

/-- Any `RSIntegrable` witness for Definition 1.2 carries the strict interval
hypothesis from the source upper/lower and tagged common-limit packages. -/
lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨w⟩
  exact w.source_limit.1.1

/-- Therefore the current `def_1_2` interface has no integrability witness on a
degenerate interval. This is the smallest source-route obstruction to the
existing `a ≤ b` theorem shape once the bridge declaration is removed. -/
lemma not_rsIntegrable_refl (f α : ℝ → ℝ) (a : ℝ) :
    ¬ RSIntegrable f α a a := by
  intro h
  exact (lt_irrefl a) (strict_interval_of_rsIntegrable h)

/-- Constant functions have no discontinuities on a degenerate interval. This
keeps the counterexample to the current non-strict theorem shape explicit. -/
lemma discontinuitySetOn_const_refl_empty (c a : ℝ) :
    discontinuitySetOn (fun _ : ℝ => c) a a = ∅ := by
  ext x
  constructor
  · intro hx
    exact hx.2 (by
      simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => c) x))
  · intro hx
    cases hx

/-- Any proof of the current universal `a ≤ b` theorem shape would apply to
the constant zero integrand and integrator on `[0,0]`, producing a degenerate
`RSIntegrable` witness. -/
theorem current_le_interval_claim_creates_degenerate_witness
    (hclaim :
      ∀ {f α : ℝ → ℝ} {a b : ℝ},
        a ≤ b →
        Monotone α →
        BddAbove (f '' Icc a b) →
        BddBelow (f '' Icc a b) →
        (discontinuitySetOn f a b).Finite →
        (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
        RSIntegrable f α a b) :
    RSIntegrable (fun _ : ℝ => 0) (fun _ : ℝ => 0) 0 0 := by
  refine hclaim (f := fun _ : ℝ => 0) (α := fun _ : ℝ => 0)
    (a := 0) (b := 0) le_rfl ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · rw [discontinuitySetOn_const_refl_empty]
    exact Set.finite_empty
  · intro x hx
    simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x)

/-- The finite-discontinuity source-route cannot prove the current task-shaped
`a ≤ b` claim from `def_1_2` alone: applying that claim to constant functions on
`[0,0]` would contradict the strict interval stored in every `RSIntegrable`
witness. -/
theorem no_source_route_for_current_le_interval_claim :
    ¬ (∀ {f α : ℝ → ℝ} {a b : ℝ},
      a ≤ b →
      Monotone α →
      BddAbove (f '' Icc a b) →
      BddBelow (f '' Icc a b) →
      (discontinuitySetOn f a b).Finite →
      (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
      RSIntegrable f α a b) := by
  intro hclaim
  exact not_rsIntegrable_refl (fun _ : ℝ => 0) (fun _ : ℝ => 0) 0
    (current_le_interval_claim_creates_degenerate_witness hclaim)

/-- Under the strict interval shape, the public task hypotheses immediately
provide the standing source hypotheses required by Definition 1.2. The finite
bad-set and continuity-at-bad-points hypotheses are not needed until the actual
upper/lower and tagged common-limit construction. -/
lemma sourceHypotheses_of_strict_task_hypotheses {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    DarbouxRS.SourceHypotheses a b f α := by
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x _hx y _hy hxy
  exact hα_mono hxy

/-- If `f` is continuous at every interval point, the task-local discontinuity
set is empty. This isolates the genuinely finite-bad-set part of Theorem 1.1
from the easier continuous-on-the-interval special case. -/
lemma discontinuitySetOn_empty_of_forall_continuousAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousAt f x) :
    discontinuitySetOn f a b = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hx.2 (hf x hx.1))
  · intro hx
    cases hx

/-- Continuous functions on the interval satisfy the finite-discontinuity
hypothesis used by the strict version of the theorem. -/
lemma finite_discontinuitySetOn_of_forall_continuousAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ∈ Icc a b → ContinuousAt f x) :
    (discontinuitySetOn f a b).Finite := by
  rw [discontinuitySetOn_empty_of_forall_continuousAt hf]
  exact Set.finite_empty

/-- The Definition 1.2 `RSIntegrable` witness is equivalent to producing one
real number that satisfies both exposed common-limit interfaces. This is the
smallest theorem-level object still missing from a strict-interval
finite-discontinuity route. -/
theorem common_limits_iff_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ} :
    (∃ L, rsUpperLowerCommonLimit a b f α L ∧ rsTaggedCommonLimit a b f α L) ↔
      RSIntegrable f α a b := by
  constructor
  · rintro ⟨L, hSource, hTagged⟩
    exact ⟨{
      value := L
      source_limit := hSource
      tagged_limit := hTagged
    }⟩
  · intro h
    rcases h with ⟨w⟩
    exact ⟨w.value, w.source_limit, w.tagged_limit⟩

/-- For a fixed partition, the tagged sum lies between the lower and upper
Darboux sums. This removes the tagged-limit half of the strict route once the
upper/lower common limit has been produced. -/
lemma taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : DarbouxRS.SourceHypotheses a b f α)
    (P : DarbouxRS.Partition a b) (tags : ℕ → ℝ)
    (htags : DarbouxRS.tagsInPartition P tags) :
    DarbouxRS.lowerSum P f α ≤ DarbouxRS.taggedSum P tags f α ∧
      DarbouxRS.taggedSum P tags f α ≤ DarbouxRS.upperSum P f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  constructor
  · unfold DarbouxRS.lowerSum DarbouxRS.taggedSum
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hi : i < P.n := Finset.mem_range.mp hi_mem
    have hcellBelow : BddBelow (f '' DarbouxRS.subinterval P i) :=
      BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hBelow
    have hlow_le_tag : DarbouxRS.lowerStep P f i ≤ f (tags i) := by
      unfold DarbouxRS.lowerStep
      exact csInf_le hcellBelow ⟨tags i, htags i hi, rfl⟩
    have hinc_nonneg : 0 ≤ α (P.pts (i + 1)) - α (P.pts i) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩ hi
    exact mul_le_mul_of_nonneg_right hlow_le_tag hinc_nonneg
  · unfold DarbouxRS.taggedSum DarbouxRS.upperSum
    refine Finset.sum_le_sum ?_
    intro i hi_mem
    have hi : i < P.n := Finset.mem_range.mp hi_mem
    have hcellAbove : BddAbove (f '' DarbouxRS.subinterval P i) :=
      BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hAbove
    have htag_le_up : f (tags i) ≤ DarbouxRS.upperStep P f i := by
      unfold DarbouxRS.upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i hi, rfl⟩
    have hinc_nonneg : 0 ≤ α (P.pts (i + 1)) - α (P.pts i) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩ hi
    exact mul_le_mul_of_nonneg_right htag_le_up hinc_nonneg

/-- The tagged common limit is forced by the upper/lower common limit, with the
same value `L`, by squeezing every tagged sum between the lower and upper sums. -/
theorem taggedCommonLimit_of_upperLowerCommonLimit {f α : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f α L) :
    rsTaggedCommonLimit a b f α L := by
  rcases hUL with ⟨hs, hlim⟩
  refine ⟨hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := Hδ P hmesh
  have hbetween := taggedSum_between_lower_upper hs P tags htags
  have hlower_abs := abs_lt.mp hP.2
  have hupper_abs := abs_lt.mp hP.1
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

/-- It is enough for the strict finite-discontinuity route to construct the
upper/lower common Darboux limit; the tagged common limit then follows by
`taggedCommonLimit_of_upperLowerCommonLimit`. -/
def StrictFiniteDiscontinuityUpperLowerCriterion : Prop :=
  ∀ {f α : ℝ → ℝ} {a b : ℝ},
    a < b →
    Monotone α →
    BddAbove (f '' Icc a b) →
    BddBelow (f '' Icc a b) →
    (discontinuitySetOn f a b).Finite →
    (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
    ∃ L, rsUpperLowerCommonLimit a b f α L

end Thm11SourceRoute
