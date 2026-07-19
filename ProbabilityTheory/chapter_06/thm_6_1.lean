import Mathlib.Tactic
import ProbabilityTheory.chapter_06.def_6_2

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Thm61Support

/--
`EReal` only distributes over arbitrary sums when the scalar is a finite
nonnegative extended real. This is the case needed for positive real scalars.
-/
theorem ereal_mul_finset_sum_of_nonneg_of_ne_top {ι : Type*} (s : Finset ι)
    {a : EReal} (ha : 0 ≤ a) (ha_top : a ≠ ⊤) (f : ι → EReal) :
    a * (Finset.sum s f) = Finset.sum s (fun i => a * f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [EReal.left_distrib_of_nonneg_of_ne_top ha ha_top]
      exact congrArg (fun t => a * f i + t) ih

theorem finset_sum_ne_top_of_forall_ne_top {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    Finset.sum s f ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact EReal.add_ne_top (hf i (by simp [hi])) <|
        ih (fun j hj => hf j (by simp [hj]))

theorem finset_sum_ne_bot_of_forall_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) :
    Finset.sum s f ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (EReal.add_ne_bot_iff).2
        ⟨hf i (by simp [hi]), ih (fun j hj => hf j (by simp [hj]))⟩

theorem neg_finset_sum_of_forall_ne_top {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    Finset.sum s (fun i => -(f i)) = -(Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hfi : f i ≠ ⊤ := hf i (Finset.mem_insert_self i s)
      have hs : Finset.sum s f ≠ ⊤ := by
        exact finset_sum_ne_top_of_forall_ne_top s f
          (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
      rw [EReal.neg_add (.inr hs) (.inl hfi)]
      exact congrArg (fun t => -f i + t) <|
        ih (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))

theorem neg_finset_sum_of_forall_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) :
    Finset.sum s (fun i => -(f i)) = -(Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hfi : f i ≠ ⊥ := hf i (Finset.mem_insert_self i s)
      have hs : Finset.sum s f ≠ ⊥ := by
        exact finset_sum_ne_bot_of_forall_ne_bot s f
          (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))
      rw [EReal.neg_add (.inl hfi) (.inr hs)]
      exact congrArg (fun t => -f i + t) <|
        ih (fun j hj => hf j (Finset.mem_insert.mpr (Or.inr hj)))

/--
Negating a simple function negates the Definition 6.2 range-sum value, provided
the Definition 6.2 sum is actually defined.
-/
theorem integralValue_neg_of_defined (μ : Measure Ω) (X : SimpleFunc Ω EReal)
    (hXdef : simpleFunctionIntegralDefined μ X) :
    simpleFunctionIntegralValue μ (X.map fun x => -x) =
      -simpleFunctionIntegralValue μ X := by
  classical
  let term : EReal → EReal := fun x => x * (μ (X ⁻¹' {x}) : EReal)
  have hbranch :
      (∀ x ∈ X.range, term x ≠ ⊤) ∨
        (∀ x ∈ X.range, term x ≠ ⊥) := by
    by_cases hpos : simpleFunctionHasPosInf μ X
    · right
      intro x hx hbot
      exact hXdef ⟨hpos, ⟨x, hx, hbot⟩⟩
    · left
      intro x hx htop
      exact hpos ⟨x, hx, htop⟩
  have hnegSum :
      Finset.sum X.range (fun x => -(term x)) = -(Finset.sum X.range term) := by
    rcases hbranch with hnoTop | hnoBot
    · exact neg_finset_sum_of_forall_ne_top X.range term hnoTop
    · exact neg_finset_sum_of_forall_ne_bot X.range term hnoBot
  calc
    simpleFunctionIntegralValue μ (X.map fun x => -x)
        = ∑ x ∈ X.range, -(term x) := by
            simpa [term, simpleFunctionIntegralTerm, neg_mul] using
              (integralValue_map (μ := μ) (g := fun x : EReal => -x) (f := X))
    _ = -∑ x ∈ X.range, term x := by
          exact hnegSum
    _ = -simpleFunctionIntegralValue μ X := by
          simp [simpleFunctionIntegralValue, simpleFunctionIntegralTerm, term]

/--
Positive real scalars distribute through the Definition 6.2 range-sum.
-/
theorem integralValue_const_mul_of_nonneg (μ : Measure Ω) (X : SimpleFunc Ω EReal)
    (a : ℝ) (ha : 0 ≤ a) :
    simpleFunctionIntegralValue μ (X.map fun x => (a : EReal) * x) =
      (a : EReal) * simpleFunctionIntegralValue μ X := by
  have haE : 0 ≤ (a : EReal) := by
    exact_mod_cast ha
  have haTop : (a : EReal) ≠ ⊤ := by
    simp
  calc
    simpleFunctionIntegralValue μ (X.map fun x => (a : EReal) * x)
        = ∑ x ∈ X.range, (a : EReal) * (x * (μ (X ⁻¹' {x}) : EReal)) := by
            simpa [simpleFunctionIntegralTerm, mul_assoc] using
              (integralValue_map (μ := μ) (g := fun x : EReal => (a : EReal) * x) (f := X))
    _ = (a : EReal) * ∑ x ∈ X.range, x * (μ (X ⁻¹' {x}) : EReal) := by
          symm
          exact ereal_mul_finset_sum_of_nonneg_of_ne_top X.range haE haTop
            (fun x => x * (μ (X ⁻¹' {x}) : EReal))
    _ = (a : EReal) * simpleFunctionIntegralValue μ X := by
          simp [simpleFunctionIntegralValue, simpleFunctionIntegralTerm]

/--
Real scalar multiplication is compatible with the Definition 6.2 range-sum on
the defined branch of Definition 6.2.
-/
theorem integralValue_const_mul_real_of_defined (μ : Measure Ω) (X : SimpleFunc Ω EReal)
    (α : ℝ) (hXdef : simpleFunctionIntegralDefined μ X) :
    simpleFunctionIntegralValue μ (X.map fun x => (α : EReal) * x) =
      (α : EReal) * simpleFunctionIntegralValue μ X := by
  by_cases hα : 0 ≤ α
  · exact integralValue_const_mul_of_nonneg μ X α hα
  · have hneg : 0 ≤ -α := by linarith
    calc
      simpleFunctionIntegralValue μ (X.map fun x => (α : EReal) * x)
          = simpleFunctionIntegralValue μ
              ((X.map fun x => -x).map fun x => ((-α : ℝ) : EReal) * x) := by
                congr 1
                ext ω
                simp [SimpleFunc.map_map]
      _ = (((-α : ℝ) : EReal) * simpleFunctionIntegralValue μ (X.map fun x => -x)) := by
            exact integralValue_const_mul_of_nonneg μ (X.map fun x => -x) (-α) hneg
      _ = (((-α : ℝ) : EReal) * (-simpleFunctionIntegralValue μ X)) := by
            rw [integralValue_neg_of_defined (μ := μ) (X := X) hXdef]
      _ = (α : EReal) * simpleFunctionIntegralValue μ X := by
            simp

/-- Additivity of the raw Definition 6.2 range-sum under cellwise compatibility. -/
theorem integralValue_add_of_cellwise_distrib (μ : Measure Ω) (X Y : SimpleFunc Ω EReal)
    (hcell : simpleFunctionIntegralAddCompatible μ X Y) :
    simpleFunctionIntegralValue μ (X + Y) =
      simpleFunctionIntegralValue μ X + simpleFunctionIntegralValue μ Y := by
  classical
  calc
    simpleFunctionIntegralValue μ (X + Y)
        = ∑ p ∈ (X.pair Y).range,
            (p.1 + p.2) * (μ (X.pair Y ⁻¹' {p}) : EReal) := by
            rw [SimpleFunc.add_eq_map₂]
            simpa using
              (integralValue_map (μ := μ) (g := fun p : EReal × EReal => p.1 + p.2)
                (f := X.pair Y))
    _ = ∑ p ∈ (X.pair Y).range,
          (p.1 * (μ (X.pair Y ⁻¹' {p}) : EReal) +
            p.2 * (μ (X.pair Y ⁻¹' {p}) : EReal)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact hcell p hp
    _ = (∑ p ∈ (X.pair Y).range, p.1 * (μ (X.pair Y ⁻¹' {p}) : EReal)) +
          ∑ p ∈ (X.pair Y).range, p.2 * (μ (X.pair Y ⁻¹' {p}) : EReal) := by
            rw [Finset.sum_add_distrib]
    _ = simpleFunctionIntegralValue μ ((X.pair Y).map Prod.fst) +
          simpleFunctionIntegralValue μ ((X.pair Y).map Prod.snd) := by
          rw [integralValue_map (μ := μ) (g := Prod.fst),
            integralValue_map (μ := μ) (g := Prod.snd)]
    _ = simpleFunctionIntegralValue μ X + simpleFunctionIntegralValue μ Y := by
          simp

end Thm61Support

/-  ## Theorem 6.1
Theorem 6.1 at the Definition 6.2 interface.
-/
theorem thm_6_1 (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (α : ℝ) :
    (∀ {x xα : EReal},
        def_6_2 μ X = some x →
        def_6_2 μ (X.map fun t => (α : EReal) * t) = some xα →
        xα = (α : EReal) * x) ∧
      (∀ {x y xy : EReal},
        def_6_2 μ X = some x →
        def_6_2 μ Y = some y →
        simpleFunctionIntegralAdd μ X Y = some xy →
        xy = x + y) ∧
      (X ≤ Y →
        ∀ {x y : EReal},
          def_6_2 μ X = some x →
          def_6_2 μ Y = some y →
          x ≤ y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x xα hX hαX
    rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hX with ⟨hXdef, hx⟩
    rcases
      (def62_eq_some_iff (μ := μ) (f := X.map fun t => (α : EReal) * t) (v := xα)).1 hαX with
      ⟨_, hxα⟩
    rw [← hxα,
      Thm61Support.integralValue_const_mul_real_of_defined
        (μ := μ) (X := X) (α := α) hXdef,
      hx]
  · intro x y xy hX hY hXY
    unfold simpleFunctionIntegralAdd at hXY
    split_ifs at hXY with hcell
    · rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hX with ⟨_, hx⟩
      rcases (def62_eq_some_iff (μ := μ) (f := Y) (v := y)).1 hY with ⟨_, hy⟩
      rcases (def62_eq_some_iff (μ := μ) (f := X + Y) (v := xy)).1 hXY with ⟨_, hxy⟩
      rw [← hxy,
        Thm61Support.integralValue_add_of_cellwise_distrib (μ := μ) (X := X) (Y := Y) hcell,
        hx, hy]
  · intro hXY x y hX hY
    rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hX with ⟨_, hx⟩
    rcases (def62_eq_some_iff (μ := μ) (f := Y) (v := y)).1 hY with ⟨_, hy⟩
    rw [← hx, ← hy]
    exact integralValue_mono_fun (μ := μ) hXY
