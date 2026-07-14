import ProbabilityTheory.chapter_02.def_2_4

/-

Theorem 2.1  liminf and limsup

-/


/-
\begin{thmbox}{2.1 (Definition 2.4)}
Let $(E_i)_{i\ge 1}$ be a sequence of subsets in a set $\Omega$. We have
\[
\liminf_{i\to\infty} E_i
=
\{\omega\in \Omega : \omega \text{ belongs to } E_i \text{ for all but finitely many } i\},
\]
\[
\limsup_{i\to\infty} E_i
=
\{\omega\in \Omega : \omega \text{ belongs to } E_i \text{ infinitely often}\}.
\]
\end{thmbox}

\textit{Proof} We note that the condition of an outcome $\omega$ being in $E_i$
for all but finite many $i$ is equivalent to the statement that $\omega$ belongs
to $E_i$ eventually for all $i\ge N$, for some integer $N$. Using the definition
of liminf, we see that an outcome $\omega$ belongs to $\cup_{j\ge 1}\cap_{k\ge j}
 E_k$ if and only if it belongs to $\cap_{k\ge j} E_k$ for some $j$. This is the
 same as saying that $\omega$ belongs to $E_k$ eventually for all $k\ge j$.

To see that an element in limsup$_i\, E_i$ occurs in $E_i$ infinitely often,
we define $F_j\triangleq \cup_{k\ge j} E_k$ and write
limsup$_{i\to\infty} E_i \triangleq \cap_{j=1}^{\infty} F_j$.

Consider an element $\omega$ in the limsup of $E_i$'s. It must be in $F_j$
for all $j$. In particular, it must be in $F_1$. Since $F_1$ is the union of
all $E_k$'s, we can find an index $k_1$ such that $\omega\in E_{k_1}$.
Next, we use the fact that $\omega$ is in $F_{k_1+1}$. Since $F_{k_1+1}$ is
the union of all $E_i$'s for $i\ge k_1+1$, we can find an index $k_2>k_1$
such that $\omega\in E_{k_2}$. This process can be repeated indefinitely.
Therefore, $\omega$ belongs to $E_{k_1},E_{k_2},E_{k_3},\dots$, for some
strictly increasing indices $k_1<k_2<k_3<\cdots$. This shows that $\omega$
occurs in $E_i$ infinitely often, as desired.

Conversely, if $\omega$ belongs to $E_i$ for infinitely many indices $i$,
then $\omega$ belongs to $F_j$ for all indices $j$. This is because $F_j$
contains all $E_i$'s for $i\ge j$, and since $\omega$ belongs to infinitely
many $E_i$'s, it must belong to $F_j$ for all $j$. Therefore, $\omega$ is
in $\cap_{j\ge 1} F_j$, which is the limsup of $E_i$'s. \hfill $\square$
-/


open Set

/-- Given a sequence of sets E_i,
   A sample ω belongs to liminf E_i iff ω occurs in E_i for all but finitely many indices i
-/
theorem thm_2_1_part1 {Ω : Type*} (E : ℕ → Set Ω) :
   (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) := by
  intro ω
  constructor
  · intro hω
    rcases mem_iUnion.mp hω with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    exact mem_iInter₂.mp hN n hn
  · rintro ⟨N, hN⟩
    refine mem_iUnion.mpr ⟨N, ?_⟩
    exact mem_iInter₂.mpr hN


/-- Given a sequence of sets E_i,
  a sample ω belongs to limsup E_i iff ω occurs infinitely often in the sequence
-/
theorem thm_2_1_part2 {Ω : Type*} (E : ℕ → Set Ω) :
  (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by
  intro ω
  constructor
  · intro hω N
    rw [setLimsup, mem_iInter] at hω
    have hN := hω N
    rw [mem_iUnion] at hN
    rcases hN with ⟨n, hn⟩
    rw [mem_iUnion] at hn
    rcases hn with ⟨hnN, hmem⟩
    exact ⟨n, hnN, hmem⟩
  · intro hω
    rw [setLimsup, mem_iInter]
    intro N
    rcases hω N with ⟨n, hnN, hmem⟩
    rw [mem_iUnion]
    refine ⟨n, ?_⟩
    rw [mem_iUnion]
    exact ⟨hnN, hmem⟩


/-- Exported statement for Theorem 2.1. -/
theorem thm_2_1 {Ω : Type*} (E : ℕ → Set Ω) :
    (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) ∧
      (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by
  exact ⟨thm_2_1_part1 E, thm_2_1_part2 E⟩
