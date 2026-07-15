import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import ProbabilityTheory.chapter_04.def_4_3_sup_inf

open MeasureTheory

/--
Measurability of pointwise supremum
of a countable family of measurable `EReal`-valued functions.
-/
theorem measurable_seqSupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i))
  : Measurable (fun ω => seqSup (fun i => f i ω)) := by
  simpa [seqSup] using (Measurable.iSup hf)


/--
Measurability of pointwise infimum
of a countable family of measurable `EReal`-valued functions.
-/
theorem measurable_seqInfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i))
  : Measurable (fun ω => seqInf (fun i => f i ω)) := by
  simpa [seqInf] using (Measurable.iInf hf)

/-- ## Theorem 4.7   measurability of pointwise supremum and infimum
-/
theorem thm_4_7 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqSup (fun i => f i ω)) ∧
      Measurable (fun ω => seqInf (fun i => f i ω)) := by
  exact ⟨measurable_seqSupEReal f hf, measurable_seqInfEReal f hf⟩
