import ProbabilityTheory.chapter_03.thm_3_1
import ProbabilityTheory.chapter_03.thm_3_7
import ProbabilityTheory.chapter_03.def_3_3
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Theorem 3.8: uniqueness of measure extension

The first theorem is the short Mathlib proof requested for the formalization.  The second
keeps the textbook route visible: on each finite cover piece it builds the equalizer
Dynkin system and explicitly applies the project's pi-lambda theorem `thm_3_7`.
-/

open MeasureTheory Set ENNReal MeasurableSpace

/-- ## Theorem 3.8 (short Mathlib proof).
Two sigma-finite extensions agreeing on a generating field agree
everywhere. -/
theorem thm_3_8 {Ω : Type*} [m : MeasurableSpace Ω] (F₀ : Set (Set Ω))
  (h_gen : m = MeasurableSpace.generateFrom F₀)
  (h_field_compl : ∀ s ∈ F₀, sᶜ ∈ F₀)
  (h_field_union : ∀ s ∈ F₀, ∀ t ∈ F₀, s ∪ t ∈ F₀)
  (μ1 μ2 : Measure Ω)
  (h_eq_on_F₀ : ∀ s ∈ F₀, μ1 s = μ2 s)
  (Ω_seq : ℕ → Set Ω)
  (h_in_F₀ : ∀ i, Ω_seq i ∈ F₀)
  (h_univ : (⋃ i, Ω_seq i) = univ)
  (h_finite : ∀ i, μ1 (Ω_seq i) = μ2 (Ω_seq i) ∧ μ1 (Ω_seq i) < ⊤) :
  μ1 = μ2 := by
  apply Measure.ext_of_generateFrom_of_iUnion F₀ Ω_seq h_gen
  · intro s hs t ht _
    have : s ∩ t = (sᶜ ∪ tᶜ)ᶜ := by ext x; simp
    rw [this]
    exact h_field_compl _ (h_field_union _ (h_field_compl _ hs) _ (h_field_compl _ ht))
  · exact h_univ
  · exact h_in_F₀
  · intro i
    exact (h_finite i).2.ne
  · exact h_eq_on_F₀

/-- ## Theorem 3.8 (textbook proof).
This independent proof follows the book's sigma-finite reduction and
explicitly invokes the pi-lambda theorem `thm_3_7`.
-/
theorem thm_3_8_textbook {Ω : Type*} [m : MeasurableSpace Ω] (F₀ : Set (Set Ω))
  (h_gen : m = MeasurableSpace.generateFrom F₀)
  (h_field_empty : ∅ ∈ F₀)
  (h_field_compl : ∀ s ∈ F₀, sᶜ ∈ F₀)
  (h_field_union : ∀ s ∈ F₀, ∀ t ∈ F₀, s ∪ t ∈ F₀)
  (μ1 μ2 : Measure Ω)
  (h_eq_on_F₀ : ∀ s ∈ F₀, μ1 s = μ2 s)
  (Ω_seq : ℕ → Set Ω)
  (h_disj : Pairwise (fun i j => Disjoint (Ω_seq i) (Ω_seq j)))
  (h_in_F₀ : ∀ i, Ω_seq i ∈ F₀)
  (h_univ : (⋃ i, Ω_seq i) = univ)
  (h_finite : ∀ i, μ1 (Ω_seq i) = μ2 (Ω_seq i) ∧ μ1 (Ω_seq i) < ⊤) :
  μ1 = μ2 := by
  have hInter : ∀ s ∈ F₀, ∀ t ∈ F₀, s ∩ t ∈ F₀ := by
    intro s hs t ht
    have : s ∩ t = (sᶜ ∪ tᶜ)ᶜ := by ext x; simp
    rw [this]
    exact h_field_compl _ (h_field_union _ (h_field_compl _ hs) _ (h_field_compl _ ht))
  have hPi : IsPiSystem F₀ := fun s hs t ht _ => hInter s hs t ht
  have hmeasF : ∀ s, s ∈ F₀ → MeasurableSet s := by
    intro s hs
    rw [h_gen]
    exact measurableSet_generateFrom hs
  have finite_uniq : ∀ (ν1 ν2 : Measure Ω) [IsFiniteMeasure ν1] [IsFiniteMeasure ν2],
      (∀ s ∈ F₀, ν1 s = ν2 s) → ν1 univ = ν2 univ → ν1 = ν2 := by
    intro ν1 ν2 _ _ hF huniv
    let L : DynkinSystem Ω :=
      { Has := fun s => MeasurableSet s ∧ ν1 s = ν2 s
        has_empty := ⟨MeasurableSet.empty, hF ∅ h_field_empty⟩
        has_compl := fun {a} ha =>
          ⟨ha.1.compl, by
            rw [measure_compl ha.1 (measure_ne_top ν1 a),
              measure_compl ha.1 (measure_ne_top ν2 a), ha.2, huniv]⟩
        has_iUnion_nat := fun {f} hd hf =>
          ⟨MeasurableSet.iUnion fun i => (hf i).1, by
            rw [measure_iUnion hd fun i => (hf i).1,
              measure_iUnion hd fun i => (hf i).1]
            exact tsum_congr fun i => (hf i).2⟩ }
    have key : ∀ s, MeasurableSet[generateFrom F₀] s → L.Has s :=
      thm_3_7 (P := F₀) (L := L) hPi (fun s hs => ⟨hmeasF s hs, hF s hs⟩)
    exact Measure.ext fun s hs => (key s (h_gen ▸ hs)).2
  have restrict_eq : ∀ i, μ1.restrict (Ω_seq i) = μ2.restrict (Ω_seq i) := by
    intro i
    haveI : IsFiniteMeasure (μ1.restrict (Ω_seq i)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (h_finite i).2⟩
    haveI : IsFiniteMeasure (μ2.restrict (Ω_seq i)) :=
      ⟨by rw [Measure.restrict_apply_univ, ← (h_finite i).1]; exact (h_finite i).2⟩
    apply finite_uniq
    · intro s hs
      rw [Measure.restrict_apply (hmeasF s hs), Measure.restrict_apply (hmeasF s hs)]
      exact h_eq_on_F₀ _ (hInter s hs _ (h_in_F₀ i))
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact (h_finite i).1
  ext B hB
  have hcov : (⋃ i, B ∩ Ω_seq i) = B := by
    rw [← inter_iUnion, h_univ, inter_univ]
  have hdisj' : Pairwise (fun i j => Disjoint (B ∩ Ω_seq i) (B ∩ Ω_seq j)) :=
    fun i j hij => Disjoint.mono inf_le_right inf_le_right (h_disj hij)
  have hmeas' : ∀ i, MeasurableSet (B ∩ Ω_seq i) :=
    fun i => hB.inter (hmeasF _ (h_in_F₀ i))
  calc
    μ1 B = μ1 (⋃ i, B ∩ Ω_seq i) := by rw [hcov]
    _ = ∑' i, μ1 (B ∩ Ω_seq i) := measure_iUnion hdisj' hmeas'
    _ = ∑' i, μ2 (B ∩ Ω_seq i) := by
      refine tsum_congr fun i => ?_
      rw [← Measure.restrict_apply hB, ← Measure.restrict_apply hB, restrict_eq i]
    _ = μ2 (⋃ i, B ∩ Ω_seq i) := (measure_iUnion hdisj' hmeas').symm
    _ = μ2 B := by rw [hcov]


/-- ## Theorem 3.1  Measure extension theorem
The full extension theorem, assembled after Theorem 3.8: existence comes from
Theorem 3.1 and uniqueness from the short Mathlib proof of Theorem 3.8. -/
theorem extension_unique {X : Type u} (F₀ : FieldOfSets X) (pm : Premeasure F₀)
    (h_sigma_finite : IsSigmaFinite pm) :
    ∃! μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀.carrier pm.toSetFunction μ := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom F₀.carrier
  rcases thm_3_1 F₀ pm with ⟨μ, hμ⟩
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  rcases h_sigma_finite with ⟨A, hA, h_univ, hfinite⟩
  have hEq : ∀ s ∈ F₀.carrier, μ s = ν s := by
    intro s hs
    rw [hμ s hs, hν s hs]
  have hFinite : ∀ i, μ (A i) = ν (A i) ∧ μ (A i) < ⊤ := by
    intro i
    refine ⟨hEq _ (hA i), ?_⟩
    calc
      μ (A i) = pm.toSetFunction (A i) := hμ _ (hA i)
      _ = pm.μ₀ ⟨A i, hA i⟩ := pm.toSetFunction_of_mem (hA i)
      _ < ⊤ := hfinite i
  exact (thm_3_8 F₀.carrier rfl F₀.compl_mem
    (fun s hs t ht => F₀.union_mem s t hs ht)
    μ ν hEq A hA h_univ hFinite).symm
