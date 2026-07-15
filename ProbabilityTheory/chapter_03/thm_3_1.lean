import Mathlib.Tactic
import ProbabilityTheory.chapter_03.def_3_1
import ProbabilityTheory.chapter_03.def_3_2
import ProbabilityTheory.chapter_03.def_3_3

/-!
# Carathéodory Extension Theorem

Let F₀ be a field of sets. A pre-measure μ₀ defined on F₀ extends to a measure on σ(F₀).
If μ₀ is σ-finite, the extension is unique.
-/

open Set MeasureTheory ENNReal

/--
**Carathéodory Extension Theorem (Existence + Uniqueness)**

Let F₀ be a field of sets and pm a pre-measure on F₀. Then:
1. There exists a measure μ on σ(F₀) that extends pm.
2. If pm is σ-finite, this extension is unique.
-/
theorem thm_3_1 {X : Type u} (F₀ : FieldOfSets X) (pm : Premeasure F₀) :
    (∃ μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      ∀ (s : Set X) (hs : s ∈ F₀.carrier), μ s = pm.μ₀ ⟨s, hs⟩) ∧
    (IsSigmaFinite pm →
      ∃! μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
        ∀ (s : Set X) (hs : s ∈ F₀.carrier), μ s = pm.μ₀ ⟨s, hs⟩) :=
  --⟨extension_exists F₀ pm, extension_unique F₀ pm⟩
  sorry
