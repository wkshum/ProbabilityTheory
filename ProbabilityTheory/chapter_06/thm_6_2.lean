import Mathlib.Tactic
import ProbabilityTheory.chapter_06.ex_6_1_2
import ProbabilityTheory.chapter_06.thm_6_1


open MeasureTheory
open scoped BigOperators


/-
  # Theorem 6.2
Finite linear combination of indicator functions is a simple function
-/


/-
\begin{thmbox}{6.2}
Suppose
\[
X=\sum_{j=1}^{n} b_j 1_{B_j},
\]
where $B_j$'s are measurable sets (not necessarily mutually disjoint). Then $X$ is a simple function, and
\[
\int X\, d\mu = \sum_{j=1}^{n} b_j \mu(B_j).
\]
\end{thmbox}

\textit{Proof} By the linearity of Lebesgue integral for simple functions,
\[
\int X\, d\mu = \sum_{j=1}^{n} b_j \int 1_{B_j}\, d\mu = \sum_{j=1}^{n} b_j \mu(B_j).
\]
In the second equality in the above line, we have applied Example 6.1.2 to evaluate the integral of indicator functions. \hfill $\square
-/



variable {Ω : Type*} [MeasurableSpace Ω]

/-- ## Theorem 6.2
the finite indicator representation defines a measurable simple function, and whenever the
definition-level representation integral introduced for Theorem 6.2 lands at a
value `x`, the actual Definition 6.2 integral of the represented simple
function lands at the same value.
-/
theorem thm_6_2 (μ : Measure Ω) :
    ∀ (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω),
      (∀ i, MeasurableSet (B i)) →
      Measurable
          (((indicatorRepresentationSimpleFunction (Ω := Ω) n b B : SimpleFunc Ω EReal) :
            Ω → EReal)) ∧
        ∀ {x : EReal},
          indicatorRepresentationIntegral (Ω := Ω) μ n b B = some x →
          def_6_2 μ (indicatorRepresentationSimpleFunction (Ω := Ω) n b B) = some x := by
  intro n
  induction n with
  | zero =>
      intro b B hB
      refine ⟨?_, ?_⟩
      · simpa [indicatorRepresentationSimpleFunction, indicatorRepresentationSummand] using
          (show Measurable (((0 : SimpleFunc Ω EReal) : Ω → EReal)) from
            (0 : SimpleFunc Ω EReal).measurable)
      · intro x hx
        have hx0 : x = 0 := by
          have : (0 : EReal) = x := by
            simpa [indicatorRepresentationIntegral, simpleFunctionIntegralFinChain_zero,
              indicatorRepresentationSummand] using hx
          exact this.symm
        have hzeroRestrict :
            ((SimpleFunc.const Ω (0 : EReal)).restrict Set.univ : SimpleFunc Ω EReal) = 0 := by
          ext ω
          simp
        have hzero :
            def_6_2 μ (0 : SimpleFunc Ω EReal) = some (0 : EReal) := by
          simpa [hzeroRestrict] using
            (indicatorConstIntegral_def_6_2 (μ := μ) (c := (0 : EReal))
              (B := Set.univ) MeasurableSet.univ)
        simpa [indicatorRepresentationSimpleFunction, indicatorRepresentationSummand, hx0] using hzero
  | succ n ih =>
      intro b B hB
      have htailB : ∀ i : Fin n, MeasurableSet (B i.succ) := by
        intro i
        exact hB i.succ
      have ihtail := ih (fun i : Fin n => b i.succ) (fun i : Fin n => B i.succ) htailB
      refine ⟨?_, ?_⟩
      · simpa using
          ((indicatorRepresentationSimpleFunction (Ω := Ω) (n + 1) b B :
            SimpleFunc Ω EReal).measurable)
      · intro x hx
        cases htail :
            indicatorRepresentationIntegral (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
        | none =>
            simp [indicatorRepresentationIntegral_succ, htail] at hx
        | some y =>
            have hstep :
                simpleFunctionIntegralAdd μ
                  (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
                  (indicatorRepresentationSimpleFunction (Ω := Ω) n
                    (fun i => b i.succ) (fun i => B i.succ)) = some x := by
              simpa [indicatorRepresentationIntegral_succ, htail] using hx
            have hsum_split :
                indicatorRepresentationSimpleFunction (Ω := Ω) (n + 1) b B =
                  indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0 +
                    indicatorRepresentationSimpleFunction (Ω := Ω) n
                      (fun i => b i.succ) (fun i => B i.succ) := by
              exact indicatorRepresentationSimpleFunction_succ (Ω := Ω) n b B
            unfold simpleFunctionIntegralAdd at hstep
            split_ifs at hstep with hcompat
            · simpa [hsum_split] using hstep
