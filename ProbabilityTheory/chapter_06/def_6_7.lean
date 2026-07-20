import ProbabilityTheory.chapter_06.def_6_5

/-

# Define mathematical expectation in terms of Lebesgue integral

-/

/-
\begin{defbox}{6.7}
The \textit{expectation} of a random variable $X$ is defined by
\[
E[X] \triangleq \int X\, dP,
\]
where the integral is taken over the sample space $\Omega$ with probability measure $P$.
\end{defbox}
-/


open MeasureTheory

namespace Def67Support

noncomputable abbrev textbookIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  _root_.textbookIntegral P X

end Def67Support



/-- ## Definition 6.7:
 Expectation is defined as Lebesgue integral under a probability measure
measure. -/
noncomputable def expectation {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  Def67Support.textbookIntegral P X

/-- Export Definition 6.7. -/
noncomputable def def_6_7 {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  expectation P X
