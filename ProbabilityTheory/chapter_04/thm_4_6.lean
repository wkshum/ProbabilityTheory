import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Group.Arithmetic

/-

# Theorem 4.6 Operations on measurable functions
-/

theorem thm_4_6 {Ω : Type _} [MeasurableSpace Ω] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (f + g) ∧ Measurable (f - g) ∧ (∀ c : ℝ, Measurable (c • f)) ∧ ((∀ ω, g ω ≠ 0) → Measurable (f / g)) := by
      exact ⟨ hf.add hg, hf.sub hg, fun c => measurable_const.mul hf, fun h => hf.div hg ⟩
