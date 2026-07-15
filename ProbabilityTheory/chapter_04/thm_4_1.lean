import ProbabilityTheory.chapter_04.def_4_2
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic


/-
## Theorem 4.1

The indicator function 1_A is (F, B(ℝ))-measurable
if and only if A is F-measurable.
-/
theorem thm_4_1 {Ω : Type _} [MeasurableSpace Ω] (A : Set Ω) :
    Measurable (Set.indicator A (fun _ => (1 : ℝ))) ↔ MeasurableSet A := by
      constructor <;>
      intro h;
      · convert h ( MeasurableSingletonClass.measurableSet_singleton 1 ) using 1 ;
        ext x
        simp_all only [Set.mem_preimage, Set.mem_singleton_iff,
          Set.indicator_apply_eq_self, one_ne_zero, imp_false, not_not];
      · exact Measurable.indicator measurable_const h
