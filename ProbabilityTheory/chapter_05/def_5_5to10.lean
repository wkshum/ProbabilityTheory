import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic

/--
## Independence of finitely many events
-/
def def_5_5 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ

/--
 ## Definition 5.6 Pairwise independence
-/
def def_5_6 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  Pairwise (fun i j => ProbabilityTheory.IndepSet (A i) (A j) μ)


/--
 ## Definition 5.7 Independence of finitely many collection of sets
-/
def def_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (F : Fin n → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ

/--
  ## Definition 5.8 Independence of finitely many collection of sets
-/
def def_5_8 {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (X : Fin n → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ

/--
  ## Definition 5.9 Independence of a sequence of collections of sets
-/
def def_5_9 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ


/--
  ## Definition 5.10 part 1
  Independence of finitely many random variables
-/
def def_5_10 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : ℕ → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ

/--
  ## Definition 5.10 part 2
  Independence of a sequence of random variables
-/
def def_5_10_randomVariables {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : MeasureTheory.Measure Ω) (X : ℕ → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ
