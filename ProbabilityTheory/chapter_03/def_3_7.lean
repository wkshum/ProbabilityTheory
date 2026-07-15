import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic

/-!  # Definition 3.7
# Open Covers, Subcovers, and Finite Covers

This file defines the notions of open covers, subcovers, and finite covers
for a set in a topological space, specifically designed to correspond to
Definition 3.7 for sets in ℝ.
-/

open Set

variable {X : Type*} [TopologicalSpace X]

/-- An open cover of a set `A ⊆ X` is a collection of open sets `{u_i}_{i ∈ I}`
such that `A` is contained in the union of the collection. -/
def IsOpenCover (A : Set X) {ι : Type*} (u : ι → Set X) : Prop :=
  (∀ i, IsOpen (u i)) ∧ A ⊆ ⋃ i, u i

/-- A subcover of `A` is a sub-collection of `{u_i}_{i ∈ I}` (indexed by `J ⊆ ι`)
that is also a cover of `A`. -/
def IsSubcover (A : Set X) {ι : Type*} (u : ι → Set X) (J : Set ι) : Prop :=
  IsOpenCover A (fun (j : J) => u j)

/-- A finite cover is an open cover consisting of finitely many open sets. -/
def IsFiniteCover (A : Set X) {ι : Type*} (u : ι → Set X) : Prop :=
  IsOpenCover A u ∧ Finite ι
