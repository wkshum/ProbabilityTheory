import Mathlib.Tactic

/-

Definition 2.6 Monotonically increasing and monotonically decreasing sequence of sets

-/


/-
\begin{defbox}{2.6}
A sequence of sets $A_i$, for $i=1,2,3,\dots$, is said to be \textit{increasing} if $A_1\subseteq A_2\subseteq A_3\subseteq \cdots$, or \textit{decreasing} if $A_1\supseteq A_2\supseteq A_3\supseteq \cdots$.
\end{defbox}
-/


open Set

/-- A sequence of sets is increasing when each earlier set is contained in each later set.

In Mathlib, it is defined as `Monotone A`
-/
def SetSeqIncreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Monotone A

/-- A sequence of sets is decreasing when each earlier set contains each later set.

In Mathlib, it is defined as `Antitone A`
-/
def SetSeqDecreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Antitone A



/--  # Definition 2.6
Exported increasing-sequence half of Definition 2.6.
-/
def def_2_6 {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  SetSeqIncreasing A
