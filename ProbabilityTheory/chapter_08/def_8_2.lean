import ProbabilityTheory.chapter_08.def_8_1

/-

 # Defintition 8.2  Determinisitc coupling and transport map

-/

/-
\begin{defbox}{8.2}
Continuing with the notation in Definition 8.1, if there exists a map $T:\mathcal{X}\to \mathcal{Y}$ that is $(\mathcal{F},\mathcal{G})$-measurable and satisfies $Y=T(X)$, we say that the coupling is \textit{deterministic}. In this case, the function $T$ is called a \textit{transport map}.
\[
(\mathcal{X},\mathcal{F},P)
\]
\[
\overset{id}{\swarrow} \qquad \qquad \overset{T}{\searrow}
\]
\[
(\mathcal{X},\mathcal{F},P) \qquad \qquad (\mathcal{Y},\mathcal{G},Q)
\]
\end{defbox}
-/



open MeasureTheory


/--   ## Definition 8.2   Deterministic coupling

A deterministic coupling is a coupling equipped with a measurable transport map `T : α → β`
such that the second coordinate is exactly obtained from the first by `T`.
-/
structure DeterministicCoupling
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    extends Coupling P Q where
  T : α → β
  measurable_T : Measurable T
  Y_eq_transport : Y = T ∘ X

/-- The transport map attached to a deterministic coupling. -/
noncomputable def TransportMap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : DeterministicCoupling P Q) : α → β :=
  π.T

/-- Exported definition for Definition 8.2. -/
noncomputable def def_8_2
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :=
  DeterministicCoupling P Q
