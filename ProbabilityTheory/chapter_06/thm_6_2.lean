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

private lemma ereal_finset_sum_eq_top_of_mem
    {ι : Type*} (s : Finset ι) (f : ι → EReal)
    {a : ι} (ha : a ∈ s) (hfa : f a = ⊤)
    (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at ha
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      by_cases hia : i = a
      · subst i
        rw [hfa, EReal.top_add_of_ne_bot]
        intro hsum_bot
        rcases WithBot.sum_eq_bot_iff.1 hsum_bot with ⟨j, hj, hjbot⟩
        exact hbot j (Finset.mem_insert_of_mem hj) hjbot
      · rw [ih (Finset.mem_of_mem_insert_of_ne ha (fun h => hia h.symm))
            (fun j hj => hbot j (Finset.mem_insert_of_mem hj)),
          EReal.add_top_of_ne_bot]
        exact hbot i (Finset.mem_insert_self i s)

private lemma def62_value_eq_top_of_term_eq_top
    (μ : Measure Ω) (X : SimpleFunc Ω EReal) {x a : EReal}
    (hx : def_6_2 μ X = some x) (ha : a ∈ X.range)
    (hterm : simpleFunctionIntegralTerm μ X a = ⊤) :
    x = ⊤ := by
  classical
  rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hx with
    ⟨hdefined, hvalue⟩
  have hpos : simpleFunctionHasPosInf μ X := ⟨a, ha, hterm⟩
  have hnoneg : ¬ simpleFunctionHasNegInf μ X := by
    intro hneg
    exact hdefined ⟨hpos, hneg⟩
  have hsum :
      ∑ z ∈ X.range, simpleFunctionIntegralTerm μ X z = ⊤ :=
    ereal_finset_sum_eq_top_of_mem X.range
      (simpleFunctionIntegralTerm μ X) ha hterm fun z hz hzbot =>
        hnoneg ⟨z, hz, hzbot⟩
  rw [simpleFunctionIntegralValue] at hvalue
  exact hvalue.symm.trans hsum

private lemma def62_value_eq_bot_of_term_eq_bot
    (μ : Measure Ω) (X : SimpleFunc Ω EReal) {x a : EReal}
    (hx : def_6_2 μ X = some x) (ha : a ∈ X.range)
    (hterm : simpleFunctionIntegralTerm μ X a = ⊥) :
    x = ⊥ := by
  rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hx with
    ⟨_, hvalue⟩
  have hsum :
      ∑ z ∈ X.range, simpleFunctionIntegralTerm μ X z = ⊥ := by
    exact WithBot.sum_eq_bot_iff.2 ⟨a, ha, hterm⟩
  rw [simpleFunctionIntegralValue] at hvalue
  exact hvalue.symm.trans hsum

private lemma pair_cell_measure_top_forces_left_term_top
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : μ (X.pair Y ⁻¹' {p}) = ⊤) (hp₁ : 0 < p.1) :
    simpleFunctionIntegralTerm μ X p.1 = ⊤ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ X ⁻¹' {p.1} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.fst hω
  have hfiber : μ (X ⁻¹' {p.1}) = ⊤ := by
    apply top_unique
    rw [← hμ]
    exact measure_mono hsubset
  simp [simpleFunctionIntegralTerm, hfiber, EReal.mul_top_of_pos hp₁]

private lemma pair_cell_measure_top_forces_left_term_bot
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : μ (X.pair Y ⁻¹' {p}) = ⊤) (hp₁ : p.1 < 0) :
    simpleFunctionIntegralTerm μ X p.1 = ⊥ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ X ⁻¹' {p.1} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.fst hω
  have hfiber : μ (X ⁻¹' {p.1}) = ⊤ := by
    apply top_unique
    rw [← hμ]
    exact measure_mono hsubset
  simp [simpleFunctionIntegralTerm, hfiber, EReal.mul_top_of_neg hp₁]

private lemma pair_cell_measure_top_forces_right_term_top
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : μ (X.pair Y ⁻¹' {p}) = ⊤) (hp₂ : 0 < p.2) :
    simpleFunctionIntegralTerm μ Y p.2 = ⊤ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ Y ⁻¹' {p.2} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.snd hω
  have hfiber : μ (Y ⁻¹' {p.2}) = ⊤ := by
    apply top_unique
    rw [← hμ]
    exact measure_mono hsubset
  simp [simpleFunctionIntegralTerm, hfiber, EReal.mul_top_of_pos hp₂]

private lemma pair_cell_measure_top_forces_right_term_bot
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : μ (X.pair Y ⁻¹' {p}) = ⊤) (hp₂ : p.2 < 0) :
    simpleFunctionIntegralTerm μ Y p.2 = ⊥ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ Y ⁻¹' {p.2} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.snd hω
  have hfiber : μ (Y ⁻¹' {p.2}) = ⊤ := by
    apply top_unique
    rw [← hμ]
    exact measure_mono hsubset
  simp [simpleFunctionIntegralTerm, hfiber, EReal.mul_top_of_neg hp₂]

private lemma pair_cell_measure_pos_forces_left_top_term
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : 0 < μ (X.pair Y ⁻¹' {p})) (hp₁ : p.1 = ⊤) :
    simpleFunctionIntegralTerm μ X p.1 = ⊤ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ X ⁻¹' {p.1} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.fst hω
  have hfiber : 0 < μ (X ⁻¹' {p.1}) := hμ.trans_le (measure_mono hsubset)
  have hfiber' : 0 < μ (X ⁻¹' {(⊤ : EReal)}) := by simpa [hp₁] using hfiber
  rw [simpleFunctionIntegralTerm, hp₁]
  exact EReal.top_mul_of_pos (by exact_mod_cast hfiber')

private lemma pair_cell_measure_pos_forces_left_bot_term
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : 0 < μ (X.pair Y ⁻¹' {p})) (hp₁ : p.1 = ⊥) :
    simpleFunctionIntegralTerm μ X p.1 = ⊥ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ X ⁻¹' {p.1} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.fst hω
  have hfiber : 0 < μ (X ⁻¹' {p.1}) := hμ.trans_le (measure_mono hsubset)
  have hfiber' : 0 < μ (X ⁻¹' {(⊥ : EReal)}) := by simpa [hp₁] using hfiber
  rw [simpleFunctionIntegralTerm, hp₁]
  exact EReal.bot_mul_of_pos (by exact_mod_cast hfiber')

private lemma pair_cell_measure_pos_forces_right_top_term
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : 0 < μ (X.pair Y ⁻¹' {p})) (hp₂ : p.2 = ⊤) :
    simpleFunctionIntegralTerm μ Y p.2 = ⊤ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ Y ⁻¹' {p.2} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.snd hω
  have hfiber : 0 < μ (Y ⁻¹' {p.2}) := hμ.trans_le (measure_mono hsubset)
  have hfiber' : 0 < μ (Y ⁻¹' {(⊤ : EReal)}) := by simpa [hp₂] using hfiber
  rw [simpleFunctionIntegralTerm, hp₂]
  exact EReal.top_mul_of_pos (by exact_mod_cast hfiber')

private lemma pair_cell_measure_pos_forces_right_bot_term
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (p : EReal × EReal)
    (hμ : 0 < μ (X.pair Y ⁻¹' {p})) (hp₂ : p.2 = ⊥) :
    simpleFunctionIntegralTerm μ Y p.2 = ⊥ := by
  have hsubset : X.pair Y ⁻¹' {p} ⊆ Y ⁻¹' {p.2} := by
    intro ω hω
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, SimpleFunc.pair_apply] using
      congrArg Prod.snd hω
  have hfiber : 0 < μ (Y ⁻¹' {p.2}) := hμ.trans_le (measure_mono hsubset)
  have hfiber' : 0 < μ (Y ⁻¹' {(⊥ : EReal)}) := by simpa [hp₂] using hfiber
  rw [simpleFunctionIntegralTerm, hp₂]
  exact EReal.bot_mul_of_pos (by exact_mod_cast hfiber')

private lemma simpleFunctionIntegralAddCompatible_of_defined_values
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (x y : EReal)
    (hX : def_6_2 μ X = some x) (hY : def_6_2 μ Y = some y)
    (hxy : textbookERealAddDefined x y) :
    simpleFunctionIntegralAddCompatible μ X Y := by
  intro p hp
  by_cases hμtop : μ (X.pair Y ⁻¹' {p}) = ⊤
  · have hp₁range : p.1 ∈ X.range := by
      rcases SimpleFunc.mem_range.1 hp with ⟨ω, hω⟩
      exact SimpleFunc.mem_range.2 ⟨ω, by
        simpa only [SimpleFunc.pair_apply] using congrArg Prod.fst hω⟩
    have hp₂range : p.2 ∈ Y.range := by
      rcases SimpleFunc.mem_range.1 hp with ⟨ω, hω⟩
      exact SimpleFunc.mem_range.2 ⟨ω, by
        simpa only [SimpleFunc.pair_apply] using congrArg Prod.snd hω⟩
    by_cases hp₁nonneg : 0 ≤ p.1
    · by_cases hp₂nonneg : 0 ≤ p.2
      · exact EReal.right_distrib_of_nonneg hp₁nonneg hp₂nonneg
      · have hp₂neg : p.2 < 0 := lt_of_not_ge hp₂nonneg
        rcases hp₁nonneg.eq_or_lt with hp₁zero | hp₁pos
        · rw [← hp₁zero]
          simp
        · have hx_top : x = ⊤ :=
            def62_value_eq_top_of_term_eq_top μ X hX hp₁range
              (pair_cell_measure_top_forces_left_term_top μ X Y p hμtop hp₁pos)
          have hy_bot : y = ⊥ :=
            def62_value_eq_bot_of_term_eq_bot μ Y hY hp₂range
              (pair_cell_measure_top_forces_right_term_bot μ X Y p hμtop hp₂neg)
          exact False.elim (hxy (Or.inl ⟨hx_top, hy_bot⟩))
    · have hp₁neg : p.1 < 0 := lt_of_not_ge hp₁nonneg
      by_cases hp₂nonpos : p.2 ≤ 0
      · have hpaddneg : p.1 + p.2 < 0 := add_neg_of_neg_of_nonpos hp₁neg hp₂nonpos
        have hμereal : ((μ (X.pair Y ⁻¹' {p}) : ENNReal) : EReal) = ⊤ := by
          simp [hμtop]
        rw [hμereal, EReal.mul_top_of_neg hpaddneg,
          EReal.mul_top_of_neg hp₁neg, EReal.bot_add]
      · have hp₂pos : 0 < p.2 := lt_of_not_ge hp₂nonpos
        have hx_bot : x = ⊥ :=
          def62_value_eq_bot_of_term_eq_bot μ X hX hp₁range
            (pair_cell_measure_top_forces_left_term_bot μ X Y p hμtop hp₁neg)
        have hy_top : y = ⊤ :=
          def62_value_eq_top_of_term_eq_top μ Y hY hp₂range
            (pair_cell_measure_top_forces_right_term_top μ X Y p hμtop hp₂pos)
        exact False.elim (hxy (Or.inr ⟨hx_bot, hy_top⟩))
  · apply EReal.right_distrib_of_nonneg_of_ne_top (by positivity)
    intro hcast
    exact hμtop (EReal.coe_ennreal_eq_top_iff.1 hcast)

private lemma simpleFunction_map_hasPosInf_refines
    {β : Type*} (μ : Measure Ω) (f : SimpleFunc Ω β) (g : β → EReal)
    (hpos : simpleFunctionHasPosInf μ (f.map g)) :
    ∃ p ∈ f.range,
      g p * (μ (f ⁻¹' {p}) : EReal) = ⊤ := by
  classical
  rcases hpos with ⟨z, hzrange, hzterm⟩
  let s : Finset β := f.range.filter fun p => g p = z
  have hmeasure :
      (∑ p ∈ s, μ (f ⁻¹' {p})) = μ (f ⁻¹' (s : Set β)) :=
    f.sum_measure_preimage_singleton s
  unfold simpleFunctionIntegralTerm at hzterm
  rw [SimpleFunc.map_preimage_singleton] at hzterm
  have hzterm_s : z * (μ (f ⁻¹' (s : Set β)) : EReal) = ⊤ := by
    simpa [s] using hzterm
  rw [← hmeasure] at hzterm_s
  change z * ((∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) : EReal) = ⊤ at hzterm_s
  rcases (EReal.mul_eq_top z ((∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) : EReal)).1 hzterm_s with
    hbad | hbad | htop | hmeasuretop
  · exact False.elim (not_lt_of_ge
      (show 0 ≤ ((∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) : EReal) by positivity) hbad.2)
  · exact False.elim (EReal.coe_ennreal_ne_bot _ hbad.2)
  · have hsumpos : 0 < ∑ p ∈ s, μ (f ⁻¹' {p}) := by
      exact_mod_cast htop.2
    rcases Finset.sum_pos_iff.1 hsumpos with ⟨p, hp, hpmeasure⟩
    have hpdata := Finset.mem_filter.1 hp
    refine ⟨p, hpdata.1, ?_⟩
    rw [hpdata.2, htop.1]
    exact EReal.top_mul_of_pos (by exact_mod_cast hpmeasure)
  · have hsumtop : (∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) = ⊤ :=
      EReal.coe_ennreal_eq_top_iff.1 hmeasuretop.2
    rcases ENNReal.sum_eq_top.1 hsumtop with ⟨p, hp, hpmeasure⟩
    have hpdata := Finset.mem_filter.1 hp
    refine ⟨p, hpdata.1, ?_⟩
    rw [hpdata.2, hpmeasure]
    exact EReal.mul_top_of_pos hmeasuretop.1

private lemma simpleFunction_map_hasNegInf_refines
    {β : Type*} (μ : Measure Ω) (f : SimpleFunc Ω β) (g : β → EReal)
    (hneg : simpleFunctionHasNegInf μ (f.map g)) :
    ∃ p ∈ f.range,
      g p * (μ (f ⁻¹' {p}) : EReal) = ⊥ := by
  classical
  rcases hneg with ⟨z, hzrange, hzterm⟩
  let s : Finset β := f.range.filter fun p => g p = z
  have hmeasure :
      (∑ p ∈ s, μ (f ⁻¹' {p})) = μ (f ⁻¹' (s : Set β)) :=
    f.sum_measure_preimage_singleton s
  unfold simpleFunctionIntegralTerm at hzterm
  rw [SimpleFunc.map_preimage_singleton] at hzterm
  have hzterm_s : z * (μ (f ⁻¹' (s : Set β)) : EReal) = ⊥ := by
    simpa [s] using hzterm
  rw [← hmeasure] at hzterm_s
  change z * ((∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) : EReal) = ⊥ at hzterm_s
  rcases (EReal.mul_eq_bot z ((∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) : EReal)).1 hzterm_s with
    hbot | hbad | hbad | hmeasuretop
  · have hsumpos : 0 < ∑ p ∈ s, μ (f ⁻¹' {p}) := by
      exact_mod_cast hbot.2
    rcases Finset.sum_pos_iff.1 hsumpos with ⟨p, hp, hpmeasure⟩
    have hpdata := Finset.mem_filter.1 hp
    refine ⟨p, hpdata.1, ?_⟩
    rw [hpdata.2, hbot.1]
    exact EReal.bot_mul_of_pos (by exact_mod_cast hpmeasure)
  · exact False.elim (EReal.coe_ennreal_ne_bot _ hbad.2)
  · exact False.elim (not_lt_of_ge
      (show 0 ≤ ((∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) : EReal) by positivity) hbad.2)
  · have hsumtop : (∑ p ∈ s, μ (f ⁻¹' {p}) : ENNReal) = ⊤ :=
      EReal.coe_ennreal_eq_top_iff.1 hmeasuretop.2
    rcases ENNReal.sum_eq_top.1 hsumtop with ⟨p, hp, hpmeasure⟩
    have hpdata := Finset.mem_filter.1 hp
    refine ⟨p, hpdata.1, ?_⟩
    rw [hpdata.2, hpmeasure]
    exact EReal.mul_top_of_neg hmeasuretop.1

private lemma simpleFunction_add_hasPosInf_forces_value_top
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (x y : EReal)
    (hX : def_6_2 μ X = some x) (hY : def_6_2 μ Y = some y)
    (hpos : simpleFunctionHasPosInf μ (X + Y)) :
    x = ⊤ ∨ y = ⊤ := by
  have hadd : X + Y = (X.pair Y).map fun p => p.1 + p.2 := by
    ext ω
    simp [SimpleFunc.pair_apply]
  rw [hadd] at hpos
  rcases simpleFunction_map_hasPosInf_refines μ (X.pair Y) (fun p => p.1 + p.2) hpos with
    ⟨p, hp, hpterm⟩
  have hp₁range : p.1 ∈ X.range := by
    rcases SimpleFunc.mem_range.1 hp with ⟨ω, hω⟩
    exact SimpleFunc.mem_range.2 ⟨ω, by
      simpa only [SimpleFunc.pair_apply] using congrArg Prod.fst hω⟩
  have hp₂range : p.2 ∈ Y.range := by
    rcases SimpleFunc.mem_range.1 hp with ⟨ω, hω⟩
    exact SimpleFunc.mem_range.2 ⟨ω, by
      simpa only [SimpleFunc.pair_apply] using congrArg Prod.snd hω⟩
  rcases (EReal.mul_eq_top (p.1 + p.2)
      ((μ (X.pair Y ⁻¹' {p}) : ENNReal) : EReal)).1 hpterm with
    hbad | hbad | haddtop | hmeasuretop
  · exact False.elim ((show ¬ (((μ (X.pair Y ⁻¹' {p}) : ENNReal) : EReal) < 0) by
      exact not_lt_of_ge (by positivity)) hbad.2)
  · exact False.elim (EReal.coe_ennreal_ne_bot _ hbad.2)
  · have hcomponent : p.1 = ⊤ ∨ p.2 = ⊤ := by
      by_contra hne
      push Not at hne
      exact EReal.add_ne_top hne.1 hne.2 haddtop.1
    have hmeasurepos : 0 < μ (X.pair Y ⁻¹' {p}) := by
      exact_mod_cast haddtop.2
    rcases hcomponent with hp₁top | hp₂top
    · exact Or.inl <| def62_value_eq_top_of_term_eq_top μ X hX hp₁range
        (pair_cell_measure_pos_forces_left_top_term μ X Y p hmeasurepos hp₁top)
    · exact Or.inr <| def62_value_eq_top_of_term_eq_top μ Y hY hp₂range
        (pair_cell_measure_pos_forces_right_top_term μ X Y p hmeasurepos hp₂top)
  · have hcomponent : 0 < p.1 ∨ 0 < p.2 := by
      by_contra hnot
      push Not at hnot
      exact (not_lt_of_ge (add_nonpos hnot.1 hnot.2)) hmeasuretop.1
    have hμtop : μ (X.pair Y ⁻¹' {p}) = ⊤ :=
      EReal.coe_ennreal_eq_top_iff.1 hmeasuretop.2
    rcases hcomponent with hp₁pos | hp₂pos
    · exact Or.inl <| def62_value_eq_top_of_term_eq_top μ X hX hp₁range
        (pair_cell_measure_top_forces_left_term_top μ X Y p hμtop hp₁pos)
    · exact Or.inr <| def62_value_eq_top_of_term_eq_top μ Y hY hp₂range
        (pair_cell_measure_top_forces_right_term_top μ X Y p hμtop hp₂pos)

private lemma simpleFunction_add_hasNegInf_forces_value_bot
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (x y : EReal)
    (hX : def_6_2 μ X = some x) (hY : def_6_2 μ Y = some y)
    (hneg : simpleFunctionHasNegInf μ (X + Y)) :
    x = ⊥ ∨ y = ⊥ := by
  have hadd : X + Y = (X.pair Y).map fun p => p.1 + p.2 := by
    ext ω
    simp [SimpleFunc.pair_apply]
  rw [hadd] at hneg
  rcases simpleFunction_map_hasNegInf_refines μ (X.pair Y) (fun p => p.1 + p.2) hneg with
    ⟨p, hp, hpterm⟩
  have hp₁range : p.1 ∈ X.range := by
    rcases SimpleFunc.mem_range.1 hp with ⟨ω, hω⟩
    exact SimpleFunc.mem_range.2 ⟨ω, by
      simpa only [SimpleFunc.pair_apply] using congrArg Prod.fst hω⟩
  have hp₂range : p.2 ∈ Y.range := by
    rcases SimpleFunc.mem_range.1 hp with ⟨ω, hω⟩
    exact SimpleFunc.mem_range.2 ⟨ω, by
      simpa only [SimpleFunc.pair_apply] using congrArg Prod.snd hω⟩
  rcases (EReal.mul_eq_bot (p.1 + p.2)
      ((μ (X.pair Y ⁻¹' {p}) : ENNReal) : EReal)).1 hpterm with
    haddbot | hbad | hbad | hmeasuretop
  · have hmeasurepos : 0 < μ (X.pair Y ⁻¹' {p}) := by
      exact_mod_cast haddbot.2
    rcases EReal.add_eq_bot_iff.1 haddbot.1 with hp₁bot | hp₂bot
    · exact Or.inl <| def62_value_eq_bot_of_term_eq_bot μ X hX hp₁range
        (pair_cell_measure_pos_forces_left_bot_term μ X Y p hmeasurepos hp₁bot)
    · exact Or.inr <| def62_value_eq_bot_of_term_eq_bot μ Y hY hp₂range
        (pair_cell_measure_pos_forces_right_bot_term μ X Y p hmeasurepos hp₂bot)
  · exact False.elim (EReal.coe_ennreal_ne_bot _ hbad.2)
  · exact False.elim ((show ¬ (((μ (X.pair Y ⁻¹' {p}) : ENNReal) : EReal) < 0) by
      exact not_lt_of_ge (by positivity)) hbad.2)
  · have hcomponent : p.1 < 0 ∨ p.2 < 0 := by
      by_contra hnot
      push Not at hnot
      exact (not_lt_of_ge (add_nonneg hnot.1 hnot.2)) hmeasuretop.1
    have hμtop : μ (X.pair Y ⁻¹' {p}) = ⊤ :=
      EReal.coe_ennreal_eq_top_iff.1 hmeasuretop.2
    rcases hcomponent with hp₁neg | hp₂neg
    · exact Or.inl <| def62_value_eq_bot_of_term_eq_bot μ X hX hp₁range
        (pair_cell_measure_top_forces_left_term_bot μ X Y p hμtop hp₁neg)
    · exact Or.inr <| def62_value_eq_bot_of_term_eq_bot μ Y hY hp₂range
        (pair_cell_measure_top_forces_right_term_bot μ X Y p hμtop hp₂neg)

private lemma simpleFunctionIntegralDefined_add_of_defined_values
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (x y : EReal)
    (hX : def_6_2 μ X = some x) (hY : def_6_2 μ Y = some y)
    (hxy : textbookERealAddDefined x y) :
    simpleFunctionIntegralDefined μ (X + Y) := by
  intro hconflict
  rcases hconflict with ⟨hpos, hneg⟩
  have htop := simpleFunction_add_hasPosInf_forces_value_top μ X Y x y hX hY hpos
  have hbot := simpleFunction_add_hasNegInf_forces_value_bot μ X Y x y hX hY hneg
  rcases htop with hx_top | hy_top <;> rcases hbot with hx_bot | hy_bot
  · exact top_ne_bot (hx_top.symm.trans hx_bot)
  · exact hxy (Or.inl ⟨hx_top, hy_bot⟩)
  · exact hxy (Or.inr ⟨hx_bot, hy_top⟩)
  · exact top_ne_bot (hy_top.symm.trans hy_bot)

private lemma def62_add_eq_some_of_textbook_add
    (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (x y z : EReal)
    (hX : def_6_2 μ X = some x) (hY : def_6_2 μ Y = some y)
    (hadd : textbookERealAdd x y = some z) :
    def_6_2 μ (X + Y) = some z := by
  unfold textbookERealAdd at hadd
  split_ifs at hadd with hdefined
  have hz : z = x + y := by simpa using hadd.symm
  rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hX with ⟨_, hxvalue⟩
  rcases (def62_eq_some_iff (μ := μ) (f := Y) (v := y)).1 hY with ⟨_, hyvalue⟩
  apply (def62_eq_some_iff (μ := μ) (f := X + Y) (v := z)).2
  refine ⟨simpleFunctionIntegralDefined_add_of_defined_values μ X Y x y hX hY hdefined, ?_⟩
  rw [Thm61Support.integralValue_add_of_cellwise_distrib μ X Y
      (simpleFunctionIntegralAddCompatible_of_defined_values μ X Y x y hX hY hdefined),
    hxvalue, hyvalue, hz]

/-- ## Theorem 6.2
the finite indicator representation defines a measurable simple function.  On
every branch where the textbook ordered sum `∑ j, b_j μ(B_j)` is defined, the
actual Definition 6.2 integral of the represented function has exactly that
value.  No disjointness assumption on the measurable sets is needed.
-/
theorem thm_6_2 (μ : Measure Ω) :
    ∀ (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω),
      (∀ i, MeasurableSet (B i)) →
      Measurable
          (((indicatorRepresentationSimpleFunction (Ω := Ω) n b B : SimpleFunc Ω EReal) :
            Ω → EReal)) ∧
        ∀ {x : EReal},
          indicatorRepresentationWeightedSum (Ω := Ω) μ n b B = some x →
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
            simpa [indicatorRepresentationWeightedSum, textbookERealFinSum_zero] using hx
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
        simpa [indicatorRepresentationSimpleFunction,
          indicatorRepresentationSummand, hx0] using hzero
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
            indicatorRepresentationWeightedSum (Ω := Ω) μ n
              (fun i => b i.succ) (fun i => B i.succ) with
        | none =>
            simp [indicatorRepresentationWeightedSum_succ, htail,
              textbookIntegralAdd] at hx
        | some y =>
            have htailIntegral :
                def_6_2 μ
                    (indicatorRepresentationSimpleFunction (Ω := Ω) n
                      (fun i => b i.succ) (fun i => B i.succ)) = some y :=
              ihtail.2 htail
            have hheadIntegral :
                def_6_2 μ
                    (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0) =
                  some (b 0 * (μ (B 0) : EReal)) := by
              simpa [indicatorRepresentationSummand] using
                (indicatorConstIntegral_def_6_2 (μ := μ) (c := b 0)
                  (B := B 0) (hB 0))
            have hadd :
                textbookERealAdd (b 0 * (μ (B 0) : EReal)) y = some x := by
              simpa [indicatorRepresentationWeightedSum_succ, htail,
                textbookIntegralAdd] using hx
            have hsumIntegral :=
              def62_add_eq_some_of_textbook_add μ
                (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
                (indicatorRepresentationSimpleFunction (Ω := Ω) n
                  (fun i => b i.succ) (fun i => B i.succ))
                (b 0 * (μ (B 0) : EReal)) y x
                hheadIntegral htailIntegral hadd
            rw [indicatorRepresentationSimpleFunction_succ]
            exact hsumIntegral
