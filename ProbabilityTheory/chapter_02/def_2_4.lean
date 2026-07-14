import Mathlib.Tactic

/-

 Definition 2.4 limsup and liminf

-/

/-
\begin{defbox}{2.4}
Let $E_1,E_2,\dots$ be an arbitrary sequence of subsets in a set $\Omega$. The \textit{limit inferior} and \textit{limit superior} of $(E_i)_{i\ge 1}$ are defined, respectively, as
\[
\liminf_{i\to\infty} E_i
\triangleq
\bigcup_{j=1}^{\infty}\bigcap_{k\ge j} E_k,
\qquad
\limsup_{i\to\infty} E_i
\triangleq
\bigcap_{j=1}^{\infty}\bigcup_{k\ge j} E_k.
\]

In general, we have the following set inclusion:
\[
\liminf_{i\to\infty} E_i \subseteq \limsup_{i\to\infty} E_i.
\]

If equality holds, we say that the \textit{limit} of $(E_i)_{i\ge 1}$ exists and is defined as $\liminf_i E_i$ or $\limsup_i E_i$.
\end{defbox}
-/


open Set

/-- The liminf of a sequence of sets. -/
def setLiminf {Ω : Type*} (E : ℕ → Set Ω) : Set Ω :=
  ⋃ n : ℕ, ⋂ m ∈ Set.Ici n, E m

/-- The limsup of a sequence of sets. -/
def setLimsup {Ω : Type*} (E : ℕ → Set Ω) : Set Ω :=
  ⋂ n : ℕ, ⋃ m ∈ Set.Ici n, E m

/-- The set-theoretic limit exists when liminf and limsup agree. -/
def setSeqLimitExists {Ω : Type*} (E : ℕ → Set Ω) : Prop :=
  setLiminf E = setLimsup E


/-
  Given a sequence of sets, the liminf is a subset of the limsup
-/
theorem setLiminf_subset_setLimsup {Ω : Type*} (E : ℕ → Set Ω) :
    setLiminf E ⊆ setLimsup E := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨j, hj⟩
  rw [setLimsup, mem_iInter]
  intro n
  rw [mem_iUnion]
  refine ⟨max n j, ?_⟩
  rw [mem_iUnion]
  refine ⟨le_max_left n j, ?_⟩
  exact mem_iInter₂.mp hj (max n j) (le_max_right n j)

/-- # Definition 2.4  Limit of a sequence of sets
Exported definition for Definition 2.4. -/
def def_2_4 {Ω : Type*} (E : ℕ → Set Ω) : Set Ω :=
  setLiminf E
