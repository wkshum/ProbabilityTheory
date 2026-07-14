import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-

 Definition 2.3 sigma-algebra / sigma-field

 Sigma-algebra on a sample space `Ω` is defined in Mathlib `MeasurableSpace Ω`
-/




/-
\begin{defbox}{2.3}
A collection of subsets $\mathcal{F}$ of a sample space $\Omega$ is called a $\sigma$-\textit{algebra} or a $\sigma$-\textit{field} if it satisfies the following axioms:
\begin{enumerate}[label=\arabic*.]
    \item $\Omega\in \mathcal{F}$.
    \item If $(A_i)_{i=1}^{\infty}$ is a sequence of sets in $\mathcal{F}$, then $\cup_{i=1}^{\infty} A_i \in \mathcal{F}$.
    \item If $A\in \mathcal{F}$, then $A^c\in \mathcal{F}$.
\end{enumerate}

A set in $\mathcal{F}$ is called $\mathcal{F}$-\textit{measurable}, or simply \textit{measurable} if $\mathcal{F}$ is understood from the context. We say that $(\Omega,\mathcal{F})$ is a \textit{measurable space} if $\mathcal{F}$ is a $\sigma$-algebra of $\Omega$.

If $\mathcal{F}$ is a $\sigma$-field and $\mathcal{G}$ is a sub-collection of $\mathcal{F}$, we say that $\mathcal{G}$ is a \textit{sub-$\sigma$-field} or a \textit{sub-$\sigma$-algebra} of $\mathcal{F}$ if $\mathcal{G}$ is also a $\sigma$-field.
\end{defbox}
-/



open Set

/-- A sigma-field is represented by a measurable space in Lean. -/
abbrev SigmaField (Ω : Type*) := MeasurableSpace Ω

/-- A set is measurable with respect to the sigma-field `𝓕`. -/
def IsMeasurableIn {Ω : Type*} (𝓕 : SigmaField Ω) (A : Set Ω) : Prop :=
  @MeasurableSet Ω 𝓕 A

/-- `𝓖` is a sub-sigma-field of `𝓕` if every `𝓖`-measurable set is
`𝓕`-measurable. -/
def IsSubSigmaField {Ω : Type*} (𝓖 𝓕 : SigmaField Ω) : Prop :=
  ∀ ⦃A : Set Ω⦄, IsMeasurableIn 𝓖 A → IsMeasurableIn 𝓕 A

/-- # Definition 2.3

Exported definition for Definition 2.3. -/
def def_2_3 (Ω : Type*) : Type _ :=
  SigmaField Ω
