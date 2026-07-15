import Mathlib.Tactic

open Set

/-! # Definition 4.3: supremum and infimum.

This file records the textbook notions using Mathlib's existing order-theoretic
objects instead of redefining them.
-/

/-- A real number `r` is the supremum of `A` when it is the least upper bound of `A`. -/
abbrev IsSupremum (A : Set ℝ) (r : ℝ) : Prop :=
  IsLUB A r

/-- A real number `s` is the infimum of `A` when it is the greatest lower bound of `A`. -/
abbrev IsInfimum (A : Set ℝ) (s : ℝ) : Prop :=
  IsGLB A s

/-- Supremum of a countable family in a complete lattice. -/
noncomputable def seqSup {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  iSup a

/-- Infimum of a countable family in a complete lattice. -/
noncomputable def seqInf {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  iInf a

/-- The extended-real supremum of a set of real numbers. -/
noncomputable def setSupEReal (A : Set ℝ) : EReal :=
  sSup ((fun x : ℝ => (x : EReal)) '' A)

/-- The extended-real infimum of a set of real numbers. -/
noncomputable def setInfEReal (A : Set ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' A)
