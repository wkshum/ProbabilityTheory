import Mathlib.Tactic
import ProbabilityTheory.chapter_04.def_4_3_sup_inf

/-!
 # Definition 4.4: limsup and liminf

We package the textbook definitions using the standard order-theoretic
operations already available in Mathlib. The notion of limsup and liminf
can be define in general in a complete lattice
-/

/-- Tail supremum of a sequence starting at index `n`. -/
noncomputable def tailSup {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨆ k : ℕ, a (n + k)

/-- Tail infimum of a sequence starting at index `n`. -/
noncomputable def tailInf {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨅ k : ℕ, a (n + k)

/-- Limsup of a sequence in a complete lattice. -/
noncomputable def seqLimsup {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨅ n : ℕ, tailSup a n

/-- Liminf of a sequence in a complete lattice. -/
noncomputable def seqLiminf {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨆ n : ℕ, tailInf a n
