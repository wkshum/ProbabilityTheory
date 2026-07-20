import Mathlib.Tactic
import ProbabilityTheory.chapter_07.thm_7_8_ioc_bounded_bridge_support
import ProbabilityTheory.chapter_07.thm_7_9_filter_support
import ProbabilityTheory.chapter_07.thm_7_9_piecewise_regular_support
import ProbabilityTheory.chapter_07.thm_7_9_reverse_bound_support
import ProbabilityTheory.chapter_07.thm_7_9_value_support

open Filter MeasureTheory Set

noncomputable section

/-!
The source statement assumes the piecewise-continuity and no-common-jump
surface used before Theorem 7.9.  The older `hRS`-only formal interface was
too weak to justify the finite absolute bridges required by the proof.  This
parent theorem therefore consumes the reviewed source-facing regularity
surface `Thm79FiniteDiscontinuityInputs`, not the old bridge-debt axiom.
-/

instance thm_7_9_improperRSFilter_isCountablyGenerated :
    improperRSFilter.IsCountablyGenerated := by
  unfold improperRSFilter
  infer_instance

theorem thm_7_9_tendsto_symmetric_to_improperRSFilter :
    Tendsto (fun n : ℕ => ((-(n : ℝ), (n : ℝ)) : ℝ × ℝ))
      atTop improperRSFilter := by
  unfold improperRSFilter
  rw [Filter.tendsto_inf]
  constructor
  · rw [Filter.tendsto_prod_iff']
    constructor
    · change Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot
      exact Filter.tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    · change Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop
      exact tendsto_natCast_atTop_atTop
  · rw [Filter.tendsto_principal]
    exact Filter.Eventually.of_forall fun n => by
      dsimp
      exact le_trans (neg_nonpos.mpr (Nat.cast_nonneg n)) (Nat.cast_nonneg n)

lemma thm_7_9_nat_Ioc_subset_for_ioc_indicators {n m : ℕ} (hnm : n ≤ m) :
    Ioc (-(n : ℝ)) (n : ℝ) ⊆ Ioc (-(m : ℝ)) (m : ℝ) := by
  intro x hx
  have hnmR : (n : ℝ) ≤ m := by
    exact_mod_cast hnm
  constructor
  · linarith [hx.1]
  · exact le_trans hx.2 hnmR

lemma thm_7_9_ioc_abs_indicator_monotone (g : ℝ → ℝ) (x : ℝ) :
    Monotone (fun n : ℕ =>
      ENNReal.ofReal
        ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun y => |g y|) x)) := by
  intro n m hnm
  by_cases hn : x ∈ Ioc (-(n : ℝ)) (n : ℝ)
  · have hm : x ∈ Ioc (-(m : ℝ)) (m : ℝ) :=
      thm_7_9_nat_Ioc_subset_for_ioc_indicators hnm hn
    simp [Set.indicator_of_mem hn, Set.indicator_of_mem hm]
  · by_cases hm : x ∈ Ioc (-(m : ℝ)) (m : ℝ)
    · simp [Set.indicator_of_notMem hn, Set.indicator_of_mem hm]
    · simp [Set.indicator_of_notMem hn, Set.indicator_of_notMem hm]

lemma thm_7_9_ioc_abs_indicator_tendsto (g : ℝ → ℝ) (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal
          ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun y => |g y|) x))
      atTop (nhds (ENNReal.ofReal |g x|)) := by
  rcases exists_nat_gt |x| with ⟨N, hN⟩
  have hEq : (fun _ : ℕ => ENNReal.ofReal |g x|) =ᶠ[atTop]
      fun n : ℕ =>
        ENNReal.ofReal
          ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun y => |g y|) x) := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hNn : (N : ℝ) ≤ n := by
      exact_mod_cast hn
    have hxabslt : |x| < (n : ℝ) := lt_of_lt_of_le hN hNn
    have hxmem : x ∈ Ioc (-(n : ℝ)) (n : ℝ) := by
      constructor
      · exact (abs_lt.mp hxabslt).1
      · exact le_of_lt ((abs_lt.mp hxabslt).2)
    simp [Set.indicator_of_mem hxmem]
  exact Filter.Tendsto.congr' hEq tendsto_const_nhds

theorem thm_7_9_lintegral_ioc_abs_tendsto
    (μ : Measure ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Tendsto
      (fun n : ℕ => ∫⁻ x : ℝ,
        ENNReal.ofReal
          ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun y => |g y|) x) ∂μ)
      atTop
      (nhds (∫⁻ x : ℝ, ENNReal.ofReal |g x| ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone ?hmeas ?hmono ?htendsto
  · intro n
    exact (((hg.abs).indicator measurableSet_Ioc).ennreal_ofReal).aemeasurable
  · filter_upwards with x
    exact thm_7_9_ioc_abs_indicator_monotone g x
  · filter_upwards with x
    exact thm_7_9_ioc_abs_indicator_tendsto g x

theorem thm_7_9_abs_integrableOn_Ioc
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {a b : ℝ} (hab : a < b) :
    IntegrableOn (fun x => |g x|) (Ioc a b) F.measure := by
  have hOrig : RSIntegrable (fun x => |g x|) F a b := h.finite_abs_rs hab
  have hgMeasRestrict : Measurable ((Icc a b).restrict (fun x => |g x|)) := by
    exact h.measurable.abs.comp measurable_subtype_coe
  have hBounds := h.finite_abs_bounds hab
  exact (thm_7_8_ioc_bridge_of_rs_integrable_bounded_measurableOn
    F hgMeasRestrict hBounds.1 hBounds.2 hOrig).1

theorem thm_7_9_rsTruncIntegral_eq_integral_Ioc
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {a b : ℝ} (hab : a < b) :
    rsTruncIntegral g F a b = ∫ x in Ioc a b, g x ∂F.measure := by
  have hOrig : RSIntegrable g F a b := h.finite_rs hab
  have hRsTruncOrig :
      rsTruncIntegral g F a b = rsIntegral g F a b hOrig := by
    unfold rsTruncIntegral
    by_cases hIf : RSIntegrable g F a b
    · simp [hIf]
    · exact False.elim (hIf hOrig)
  have hgMeasRestrict : Measurable ((Icc a b).restrict g) := by
    exact h.measurable.comp measurable_subtype_coe
  have hBounds := h.finite_bounds hab
  have hIoc :=
    thm_7_8_ioc_bridge_of_rs_integrable_bounded_measurableOn
      F hgMeasRestrict hBounds.1 hBounds.2 hOrig
  rcases hIoc with ⟨_hIntIoc, hEqIoc⟩
  rcases hEqIoc with ⟨hRSIoc, hIocEq⟩
  have hRSIocOrig :
      rsIntegral g F a b hRSIoc = rsIntegral g F a b hOrig := by
    exact DarbouxRS.taggedCommonLimit_unique
      (rsIntegral_spec hRSIoc) (rsIntegral_spec hOrig)
  calc
    rsTruncIntegral g F a b = rsIntegral g F a b hOrig := hRsTruncOrig
    _ = rsIntegral g F a b hRSIoc := hRSIocOrig.symm
    _ = ∫ x in Ioc a b, g x ∂F.measure := hIocEq.symm

theorem thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc_any
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {a b : ℝ} (hab : a < b) :
    rsTruncIntegral (fun x => |g x|) F a b =
      ∫ x in Ioc a b, |g x| ∂F.measure := by
  have hOrig : RSIntegrable (fun x => |g x|) F a b := h.finite_abs_rs hab
  have hRsTruncOrig :
      rsTruncIntegral (fun x => |g x|) F a b =
        rsIntegral (fun x => |g x|) F a b hOrig := by
    unfold rsTruncIntegral
    by_cases hIf : RSIntegrable (fun x => |g x|) F a b
    · simp [hIf]
    · exact False.elim (hIf hOrig)
  have hgMeasRestrict : Measurable ((Icc a b).restrict (fun x => |g x|)) := by
    exact h.measurable.abs.comp measurable_subtype_coe
  have hBounds := h.finite_abs_bounds hab
  have hIoc :=
    thm_7_8_ioc_bridge_of_rs_integrable_bounded_measurableOn
      F hgMeasRestrict hBounds.1 hBounds.2 hOrig
  rcases hIoc with ⟨_hIntIoc, hEqIoc⟩
  rcases hEqIoc with ⟨hRSIoc, hIocEq⟩
  have hRSIocOrig :
      rsIntegral (fun x => |g x|) F a b hRSIoc =
        rsIntegral (fun x => |g x|) F a b hOrig := by
    exact DarbouxRS.taggedCommonLimit_unique
      (rsIntegral_spec hRSIoc) (rsIntegral_spec hOrig)
  calc
    rsTruncIntegral (fun x => |g x|) F a b =
        rsIntegral (fun x => |g x|) F a b hOrig := hRsTruncOrig
    _ = rsIntegral (fun x => |g x|) F a b hRSIoc := hRSIocOrig.symm
    _ = ∫ x in Ioc a b, |g x| ∂F.measure := hIocEq.symm

theorem thm_7_9_lintegral_ioc_abs_eq_ofReal_rs
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {n : ℕ} (hn : 0 < n) :
    (∫⁻ x : ℝ,
      ENNReal.ofReal
        ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun y => |g y|) x)
        ∂F.measure) =
      ENNReal.ofReal
        (rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)) := by
  have hlt : -(n : ℝ) < (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hIntOn :
      IntegrableOn (fun x => |g x|)
        (Ioc (-(n : ℝ)) (n : ℝ)) F.measure :=
    thm_7_9_abs_integrableOn_Ioc F h hlt
  have hIntIndicator :
      Integrable
        ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun x => |g x|))
        F.measure :=
    hIntOn.integrable_indicator measurableSet_Ioc
  have hNonneg :
      0 ≤ᵐ[F.measure]
        ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun x => |g x|)) := by
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ Ioc (-(n : ℝ)) (n : ℝ)
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
  have hOfReal := ofReal_integral_eq_lintegral_ofReal hIntIndicator hNonneg
  have hIntegralIndicator :
      (∫ x : ℝ,
        (Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun y => |g y|) x
          ∂F.measure) =
        ∫ x in Ioc (-(n : ℝ)) (n : ℝ), |g x| ∂F.measure :=
    integral_indicator measurableSet_Ioc
  have hBridge := thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc_any F h hlt
  rw [← hOfReal]
  rw [hIntegralIndicator]
  rw [← hBridge]

lemma thm_7_9_eventually_mem_Ioc_improper (x : ℝ) :
    ∀ᶠ p : ℝ × ℝ in improperRSFilter, x ∈ Ioc p.1 p.2 := by
  unfold improperRSFilter
  apply Filter.Eventually.filter_mono inf_le_left
  rw [Filter.eventually_prod_iff]
  refine ⟨fun a : ℝ => a < x, ?_, fun b : ℝ => x ≤ b, ?_, ?_⟩
  · exact Filter.eventually_atBot.2 ⟨x - 1, by intro a ha; linarith⟩
  · exact Filter.eventually_atTop.2 ⟨x, by intro b hb; exact hb⟩
  · intro a ha b hb
    exact ⟨ha, hb⟩

lemma thm_7_9_indicator_Ioc_tendsto_self (g : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun p : ℝ × ℝ => (Ioc p.1 p.2).indicator g x)
      improperRSFilter (nhds (g x)) := by
  have hEq : (fun _ : ℝ × ℝ => g x) =ᶠ[improperRSFilter]
      fun p : ℝ × ℝ => (Ioc p.1 p.2).indicator g x :=
    (thm_7_9_eventually_mem_Ioc_improper x).mono fun p hp => by
      exact (Set.indicator_of_mem hp g).symm
  exact Filter.Tendsto.congr' hEq tendsto_const_nhds

theorem thm_7_9_integral_Ioc_tendsto
    (μ : Measure ℝ) {g : ℝ → ℝ}
    (hg : Measurable g)
    (hAbs : Integrable (fun x => |g x|) μ) :
    Tendsto (fun p : ℝ × ℝ => ∫ x in Ioc p.1 p.2, g x ∂μ)
      improperRSFilter (nhds (∫ x, g x ∂μ)) := by
  have hDCT :
      Tendsto
        (fun p : ℝ × ℝ => ∫ x : ℝ, (Ioc p.1 p.2).indicator g x ∂μ)
        improperRSFilter (nhds (∫ x : ℝ, g x ∂μ)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => |g x|) ?hmeas ?hbound hAbs ?hlim
    · exact Filter.Eventually.of_forall fun p =>
        hg.aestronglyMeasurable.indicator measurableSet_Ioc
    · exact Filter.Eventually.of_forall fun p =>
        Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ Ioc p.1 p.2
          · simp [Set.indicator_of_mem hx, Real.norm_eq_abs]
          · simp [Set.indicator_of_notMem hx]
    · exact Filter.Eventually.of_forall fun x =>
        thm_7_9_indicator_Ioc_tendsto_self g x
  have hEq :
      (fun p : ℝ × ℝ =>
        ∫ x : ℝ, (Ioc p.1 p.2).indicator g x ∂μ) =ᶠ[improperRSFilter]
        fun p : ℝ × ℝ => ∫ x in Ioc p.1 p.2, g x ∂μ := by
    exact Filter.Eventually.of_forall fun p => integral_indicator measurableSet_Ioc
  exact Filter.Tendsto.congr' hEq hDCT

theorem thm_7_9_integrable_abs_of_improper_abs
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hImp : ImproperRSIntegrable (fun x => |g x|) F) :
    Integrable (fun x => |g x|) F.measure := by
  rcases hImp with ⟨I, hConv⟩
  have hSeq :
      Tendsto
        (fun n : ℕ =>
          rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ))
        atTop (nhds I) := by
    simpa [Function.comp_def] using
      hConv.2.comp thm_7_9_tendsto_symmetric_to_improperRSFilter
  have hRealBound : ∀ᶠ n : ℕ in atTop,
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) ≤ I + 1 := by
    have hEv := (Metric.tendsto_nhds.mp hSeq) 1 zero_lt_one
    filter_upwards [hEv] with n hn
    have habs :
        |rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) - I| < 1 := by
      simpa [Real.dist_eq] using hn
    linarith [(abs_lt.mp habs).2]
  let u : ℕ → ENNReal := fun n =>
    ∫⁻ x : ℝ,
      ENNReal.ofReal
        ((Ioc (-(n : ℝ)) (n : ℝ)).indicator (fun y => |g y|) x)
        ∂F.measure
  have hENNBound : ∀ᶠ n : ℕ in atTop, u n ≤ ENNReal.ofReal (I + 1) := by
    filter_upwards [hRealBound,
      (Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩)] with n hnBound hnpos
    have hnpos' : 0 < n := hnpos
    dsimp [u]
    rw [thm_7_9_lintegral_ioc_abs_eq_ofReal_rs F h hnpos']
    exact ENNReal.ofReal_le_ofReal hnBound
  have hMCT :
      Tendsto u atTop
        (nhds (∫⁻ x : ℝ, ENNReal.ofReal |g x| ∂F.measure)) := by
    dsimp [u]
    exact thm_7_9_lintegral_ioc_abs_tendsto F.measure h.measurable
  have hLle :
      (∫⁻ x : ℝ, ENNReal.ofReal |g x| ∂F.measure) ≤
        ENNReal.ofReal (I + 1) :=
    le_of_tendsto hMCT hENNBound
  have hLlt :
      (∫⁻ x : ℝ, ENNReal.ofReal |g x| ∂F.measure) < ⊤ :=
    lt_of_le_of_lt hLle ENNReal.ofReal_lt_top
  have hNonnegFull : 0 ≤ᵐ[F.measure] (fun x : ℝ => |g x|) := by
    exact Filter.Eventually.of_forall fun x => abs_nonneg (g x)
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      h.measurable.abs.aestronglyMeasurable hNonnegFull).1
      (ne_of_lt hLlt)

theorem thm_7_9_improper_abs_of_integrable_abs
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) :
    ImproperRSIntegrable (fun x => |g x|) F := by
  have hAbsAbs : Integrable (fun x => |(fun y => |g y|) x|) F.measure := by
    simpa [abs_abs] using hAbs
  have hLS :=
    thm_7_9_integral_Ioc_tendsto
      F.measure h.measurable.abs hAbsAbs
  have hEq :
      (fun p : ℝ × ℝ => ∫ x in Ioc p.1 p.2, |g x| ∂F.measure)
        =ᶠ[improperRSFilter]
        fun p : ℝ × ℝ => rsTruncIntegral (fun x => |g x|) F p.1 p.2 := by
    filter_upwards [thm_7_9_eventually_strict_improperRSFilter] with p hp
    exact (thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc_any F h hp).symm
  have hTendsto :
      Tendsto
        (fun p : ℝ × ℝ => rsTruncIntegral (fun x => |g x|) F p.1 p.2)
        improperRSFilter
        (nhds (∫ x, |g x| ∂F.measure)) :=
    Filter.Tendsto.congr' hEq hLS
  have hFinite :
      ∀ᶠ p : ℝ × ℝ in improperRSFilter,
        RSIntegrable (fun x => |g x|) F p.1 p.2 :=
    thm_7_9_eventually_rsIntegrable_of_forall
      (fun ⦃a b : ℝ⦄ hab => h.finite_abs_rs hab)
  exact thm_7_9_improperRSIntegrable_of_convergesTo ⟨hFinite, hTendsto⟩

theorem thm_7_9_improper_convergesTo_of_integrable_abs
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) :
    ImproperRSConvergesTo g F (∫ x, g x ∂F.measure) := by
  have hLS := thm_7_9_integral_Ioc_tendsto F.measure h.measurable hAbs
  have hEq :
      (fun p : ℝ × ℝ => ∫ x in Ioc p.1 p.2, g x ∂F.measure)
        =ᶠ[improperRSFilter]
        fun p : ℝ × ℝ => rsTruncIntegral g F p.1 p.2 := by
    filter_upwards [thm_7_9_eventually_strict_improperRSFilter] with p hp
    exact (thm_7_9_rsTruncIntegral_eq_integral_Ioc F h hp).symm
  have hTendsto :
      Tendsto
        (fun p : ℝ × ℝ => rsTruncIntegral g F p.1 p.2)
        improperRSFilter
        (nhds (∫ x, g x ∂F.measure)) :=
    Filter.Tendsto.congr' hEq hLS
  have hFinite :
      ∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable g F p.1 p.2 :=
    thm_7_9_eventually_rsIntegrable_of_forall
      (fun ⦃a b : ℝ⦄ hab => h.finite_rs hab)
  exact ⟨hFinite, hTendsto⟩

theorem thm_7_9_value_equality
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) :
    ∃ hImp : ImproperRSIntegrable g F,
      ∫ x, g x ∂F.measure = improperRSIntegral g F hImp := by
  exact
    thm_7_9_value_packaging_with_improperRSIntegral_spec
      (thm_7_9_improper_convergesTo_of_integrable_abs F h hAbs)

theorem thm_7_9
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) :
    (ImproperRSIntegrable (fun x => |g x|) F ↔
      Integrable (fun x => |g x|) F.measure) ∧
      (Integrable (fun x => |g x|) F.measure →
        ∃ hImp : ImproperRSIntegrable g F,
          ∫ x, g x ∂F.measure = improperRSIntegral g F hImp) := by
  constructor
  · constructor
    · exact thm_7_9_integrable_abs_of_improper_abs F h
    · exact thm_7_9_improper_abs_of_integrable_abs F h
  · exact thm_7_9_value_equality F h
