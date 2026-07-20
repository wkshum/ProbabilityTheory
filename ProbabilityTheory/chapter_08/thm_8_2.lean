import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-

 # Theorem 8.2

-/

/-
\begin{thmbox}{8.2}
Let $(\Omega_1,\mathcal{F},P)$ and $(\Omega_2,\mathcal{G},Q)$ be $\sigma$-finite measure spaces. Then there exists a unique measure, denoted by $P\times Q$, defined on the product space $(\mathcal{X}\times \mathcal{Y},\mathcal{F}\times \mathcal{G})$, such that
\[
(P\times Q)(E_1\times E_2)=P(E_1)Q(E_2)
\]
for all $E_1\in \mathcal{F}$ and $E_2\in \mathcal{G}$.
\end{thmbox}
-/

open MeasureTheory

/-- Exported statement for Theorem 8.2: on sigma-finite spaces, the product measure is the
unique measure on the product measurable space agreeing with rectangle masses. -/
theorem thm_8_2
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q] :
    ∃! R : Measure (α × β),
      ∀ s : Set α, ∀ t : Set β,
        MeasurableSet s → MeasurableSet t → R (s ×ˢ t) = P s * Q t := by
  refine ⟨P.prod Q, ?_, ?_⟩
  · intro s t hs ht
    exact Measure.prod_prod (μ := P) (ν := Q) s t
  · intro R hR
    exact (Measure.prod_eq (μ := P) (ν := Q) (μν := R)
      (by intro s t hs ht; exact hR s t hs ht)).symm
