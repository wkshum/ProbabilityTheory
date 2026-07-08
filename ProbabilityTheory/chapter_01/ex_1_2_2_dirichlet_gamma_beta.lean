import ToyApollo.Output.ex_1_2_2_dirichlet_gamma_chart

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section
/-- The `n = 2` special case, i.e. the Beta density formula. -/
def ex122BetaDensity (α₁ α₂ y : ℝ) : ℝ :=
  Real.Gamma (α₁ + α₂) / (Real.Gamma α₁ * Real.Gamma α₂) *
    y ^ (α₁ - 1) * (1 - y) ^ (α₂ - 1)

theorem ex122_beta_density_formula (α₁ α₂ y : ℝ) :
    ex122BetaDensity α₁ α₂ y =
      Real.Gamma (α₁ + α₂) / (Real.Gamma α₁ * Real.Gamma α₂) *
        y ^ (α₁ - 1) * (1 - y) ^ (α₂ - 1) := rfl

/-- The two-parameter vector used when the projected Dirichlet density has one
free coordinate. -/
def ex122TwoParameterAlpha (α₁ α₂ : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then α₁ else α₂

/-- In the two-parameter case the projected Dirichlet density is exactly the
textbook Beta density formula on the single projected coordinate. -/
theorem ex122_dirichletProjectedDensity_two_eq_betaDensity
    (α₁ α₂ : ℝ) (y : Fin 1 → ℝ) :
    ex122DirichletProjectedDensity (ex122TwoParameterAlpha α₁ α₂) y =
      ex122BetaDensity α₁ α₂ (y 0) := by
  simp [ex122DirichletProjectedDensity, ex122DirichletNormalizer,
    ex122ProjectedLastCoord, ex122TwoParameterAlpha, ex122BetaDensity]

/-- The textbook Beta density, with the support restriction stated in the
source as part of the density rather than hidden in prose. -/
def ex122BetaDensityOnUnitInterval (α₁ α₂ y : ℝ) : ℝ :=
  if 0 < y ∧ y < 1 then ex122BetaDensity α₁ α₂ y else 0

theorem ex122_beta_normalizing_constant_eq {α₁ α₂ : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    1 / ProbabilityTheory.beta α₁ α₂ =
      Real.Gamma (α₁ + α₂) / (Real.Gamma α₁ * Real.Gamma α₂) := by
  rw [ProbabilityTheory.beta]
  field_simp [Real.Gamma_pos_of_pos hα₁, Real.Gamma_pos_of_pos hα₂,
    Real.Gamma_pos_of_pos (add_pos hα₁ hα₂)]

/-- Mathlib's Beta pdf has the same interior formula as the source density. -/
theorem ex122_betaPDFReal_eq_betaDensity_on_Ioo {α₁ α₂ y : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hy0 : 0 < y) (hy1 : y < 1) :
    ProbabilityTheory.betaPDFReal α₁ α₂ y = ex122BetaDensity α₁ α₂ y := by
  rw [ProbabilityTheory.betaPDFReal, if_pos ⟨hy0, hy1⟩, ex122BetaDensity]
  rw [ex122_beta_normalizing_constant_eq hα₁ hα₂]

theorem ex122_betaPDF_eq_ofReal_betaDensityOnUnitInterval
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ProbabilityTheory.betaPDF α₁ α₂ =
      fun y => ENNReal.ofReal (ex122BetaDensityOnUnitInterval α₁ α₂ y) := by
  funext y
  rw [ProbabilityTheory.betaPDF]
  by_cases hy : 0 < y ∧ y < 1
  · rw [ex122BetaDensityOnUnitInterval, if_pos hy]
    rw [ex122_betaPDFReal_eq_betaDensity_on_Ioo hα₁ hα₂ hy.1 hy.2]
  · rw [ex122BetaDensityOnUnitInterval, if_neg hy]
    rw [ProbabilityTheory.betaPDFReal]
    rw [if_neg hy]

/-- The `n = 2` Beta law has the source Beta density relative to Lebesgue
measure, including the support restriction `0 < y < 1`. -/
theorem ex122_betaMeasure_eq_withDensity_betaDensityOnUnitInterval
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ProbabilityTheory.betaMeasure α₁ α₂ =
      (volume : Measure ℝ).withDensity
        (fun y => ENNReal.ofReal (ex122BetaDensityOnUnitInterval α₁ α₂ y)) := by
  rw [ProbabilityTheory.betaMeasure]
  rw [ex122_betaPDF_eq_ofReal_betaDensityOnUnitInterval α₁ α₂ hα₁ hα₂]

/-- Combining the projected `n = 2` density reduction with Mathlib's Beta law:
the one-coordinate projected Dirichlet density generates the Beta measure. -/
theorem ex122_betaMeasure_eq_withDensity_projectedDensity_two
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ProbabilityTheory.betaMeasure α₁ α₂ =
      (volume : Measure ℝ).withDensity
        (fun y => ENNReal.ofReal
          (if 0 < y ∧ y < 1 then
            ex122DirichletProjectedDensity (ex122TwoParameterAlpha α₁ α₂)
              (fun _ : Fin 1 => y)
          else 0)) := by
  rw [ex122_betaMeasure_eq_withDensity_betaDensityOnUnitInterval α₁ α₂ hα₁ hα₂]
  congr with y
  by_cases hy : 0 < y ∧ y < 1
  · simp [ex122BetaDensityOnUnitInterval, hy,
      ex122_dirichletProjectedDensity_two_eq_betaDensity]
  · simp [ex122BetaDensityOnUnitInterval, hy]

/-- The one-dimensional real law obtained by taking the only coordinate of the
`n = 2` projected Dirichlet pushforward. -/
def ex122ProjectedDirichletLawFirstCoordTwo (α₁ α₂ β : ℝ) : Measure ℝ :=
  Measure.map (fun y : Fin 1 → ℝ => y 0)
    (ex122ProjectedDirichletLaw (ex122TwoParameterAlpha α₁ α₂) β)

/-- The support-restricted source density measure for the `n = 2` projected
formula, written as a named measure so the remaining density-law gap is a
single equality of measures. -/
def ex122ProjectedDensityMeasureTwo (α₁ α₂ : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal
      (if 0 < y ∧ y < 1 then
        ex122DirichletProjectedDensity (ex122TwoParameterAlpha α₁ α₂)
          (fun _ : Fin 1 => y)
      else 0))

/-- The two-variable Gamma-ratio map `x₁ / (x₁ + x₂)`. -/
def ex122GammaRatioMapTwo (x : Fin 2 → ℝ) : ℝ :=
  x 0 / (x 0 + x 1)

theorem measurable_ex122GammaRatioMapTwo :
    Measurable ex122GammaRatioMapTwo := by
  unfold ex122GammaRatioMapTwo
  fun_prop

/-- The remaining `n = 2` projected-law gap, exposed as the direct law of the
Gamma ratio `X₁ / (X₁ + X₂)` under the independent same-scale Gamma product law. -/
def ex122GammaRatioLawTwo (α₁ α₂ β : ℝ) : Measure ℝ :=
  Measure.map ex122GammaRatioMapTwo
    (ex122GammaProductLaw (ex122TwoParameterAlpha α₁ α₂) β)

/-- The same independent Gamma product law, written on ordinary pairs instead
of functions `Fin 2 → ℝ`. -/
def ex122GammaPairLawTwo (α₁ α₂ β : ℝ) : Measure (ℝ × ℝ) :=
  (ex122GammaScaleLaw α₁ β).prod (ex122GammaScaleLaw α₂ β)

/-- Pair-coordinate version of the Gamma-ratio map. -/
def ex122GammaPairRatioMapTwo (x : ℝ × ℝ) : ℝ :=
  x.1 / (x.1 + x.2)

theorem measurable_ex122GammaPairRatioMapTwo :
    Measurable ex122GammaPairRatioMapTwo := by
  unfold ex122GammaPairRatioMapTwo
  fun_prop

/-- The standard ratio-sum inverse chart `(u, t) ↦ (u t, (1-u) t)`.
On `0 < u < 1`, `0 < t`, this parametrizes the positive quadrant fibers of
the Gamma-ratio map. -/
def ex122RatioSumToPair (yt : ℝ × ℝ) : ℝ × ℝ :=
  (yt.1 * yt.2, (1 - yt.1) * yt.2)

/-- The ratio-sum chart `(x₁, x₂) ↦ (x₁/(x₁+x₂), x₁+x₂)`. -/
def ex122PairToRatioSum (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 / (x.1 + x.2), x.1 + x.2)

theorem measurable_ex122RatioSumToPair :
    Measurable ex122RatioSumToPair := by
  unfold ex122RatioSumToPair
  fun_prop

theorem measurable_ex122PairToRatioSum :
    Measurable ex122PairToRatioSum := by
  unfold ex122PairToRatioSum
  fun_prop

/-- The derivative matrix of the ratio-sum inverse chart. In coordinates it is
`[[t, u], [-t, 1 - u]]` at `(u, t)`. -/
def ex122FDerivRatioSumToPair (y : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![y.2, y.1; -y.2, 1 - y.1]).toContinuousLinearMap

theorem ex122RatioSumToPair_hasFDerivAt (y : ℝ × ℝ) :
    HasFDerivAt ex122RatioSumToPair (ex122FDerivRatioSumToPair y) y := by
  unfold ex122FDerivRatioSumToPair
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hfst :
      HasFDerivAt (fun z : ℝ × ℝ => z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) y :=
    hasFDerivAt_fst
  have hsnd :
      HasFDerivAt (fun z : ℝ × ℝ => z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    hasFDerivAt_snd
  have hconst :
      HasFDerivAt (fun _ : ℝ × ℝ => (1 : ℝ)) (0 : ℝ × ℝ →L[ℝ] ℝ) y :=
    hasFDerivAt_const (1 : ℝ) y
  convert HasFDerivAt.prodMk (𝕜 := ℝ)
    (hfst.mul hsnd)
    ((hconst.sub hfst).mul hsnd) using 2 <;>
  ext <;> simp [sub_eq_add_neg, add_comm, mul_comm]

theorem ex122FDerivRatioSumToPair_det (y : ℝ × ℝ) :
    (ex122FDerivRatioSumToPair y).det = y.2 := by
  unfold ex122FDerivRatioSumToPair
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

theorem ex122RatioSumToPair_fderiv_det (y : ℝ × ℝ) :
    (fderiv ℝ ex122RatioSumToPair y).det = y.2 := by
  rw [(ex122RatioSumToPair_hasFDerivAt y).fderiv]
  exact ex122FDerivRatioSumToPair_det y

theorem ex122RatioSumToPair_abs_fderiv_det_of_snd_pos {y : ℝ × ℝ}
    (hy : 0 < y.2) :
    |(fderiv ℝ ex122RatioSumToPair y).det| = y.2 := by
  rw [ex122RatioSumToPair_fderiv_det]
  exact abs_of_pos hy

theorem ex122GammaPairRatioMapTwo_ratioSumToPair
    {u t : ℝ} (ht : t ≠ 0) :
    ex122GammaPairRatioMapTwo (ex122RatioSumToPair (u, t)) = u := by
  unfold ex122GammaPairRatioMapTwo ex122RatioSumToPair
  have hsum : u * t + (1 - u) * t = t := by ring
  rw [hsum]
  exact mul_div_cancel_right₀ u ht

theorem ex122PairToRatioSum_ratioSumToPair
    {u t : ℝ} (ht : t ≠ 0) :
    ex122PairToRatioSum (ex122RatioSumToPair (u, t)) = (u, t) := by
  ext <;> unfold ex122PairToRatioSum ex122RatioSumToPair
  · have hsum : u * t + (1 - u) * t = t := by ring
    rw [hsum]
    exact mul_div_cancel_right₀ u ht
  · ring

theorem ex122RatioSumToPair_pairToRatioSum
    {x : ℝ × ℝ} (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) :
    ex122RatioSumToPair (ex122PairToRatioSum x) = x := by
  have hsum : x.1 + x.2 ≠ 0 := ne_of_gt (add_pos hx₁ hx₂)
  ext <;> unfold ex122RatioSumToPair ex122PairToRatioSum
  · exact div_mul_cancel₀ x.1 hsum
  · field_simp [hsum]
    ring

/-- The ratio-sum chart domain used for a measurable set of possible ratio
values. -/
def ex122RatioSumDomain (s : Set ℝ) : Set (ℝ × ℝ) :=
  s ×ˢ Set.Ioi (0 : ℝ)

theorem measurableSet_ex122RatioSumDomain {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet (ex122RatioSumDomain s) := by
  exact hs.prod measurableSet_Ioi

/-- The positive-quadrant part of the Gamma-ratio preimage. Gamma densities
vanish off this quadrant, so this is the geometric image needed by the
change-of-variables reduction. -/
def ex122PositiveRatioPreimage (s : Set ℝ) : Set (ℝ × ℝ) :=
  {x | 0 < x.1 ∧ 0 < x.2 ∧ ex122GammaPairRatioMapTwo x ∈ s}

/-- On ratio values inside `(0,1)` and positive total mass, the source
ratio-sum map has exactly the positive part of the Gamma-ratio preimage as its
image. This is the set-theoretic core needed before applying Mathlib's
Jacobian change-of-variables theorem. -/
theorem ex122RatioSumToPair_image_domain_eq_positiveRatioPreimage
    {s : Set ℝ} (hs01 : s ⊆ Set.Ioo (0 : ℝ) 1) :
    ex122RatioSumToPair '' ex122RatioSumDomain s =
      ex122PositiveRatioPreimage s := by
  ext x
  constructor
  · rintro ⟨yt, hyt, rfl⟩
    rcases hyt with ⟨hu, ht⟩
    have hu01 := hs01 hu
    have hratio :
        ex122GammaPairRatioMapTwo (ex122RatioSumToPair yt) = yt.1 := by
      exact ex122GammaPairRatioMapTwo_ratioSumToPair (ne_of_gt ht)
    exact ⟨mul_pos hu01.1 ht, mul_pos (sub_pos.mpr hu01.2) ht, by
      simpa [hratio] using hu⟩
  · intro hx
    rcases hx with ⟨hx₁, hx₂, hratio⟩
    refine ⟨ex122PairToRatioSum x, ?_, ?_⟩
    · exact ⟨hratio, add_pos hx₁ hx₂⟩
    · exact ex122RatioSumToPair_pairToRatioSum hx₁ hx₂

/-- The same ratio-sum chart is injective on every source domain
`s × (0,∞)`. -/
theorem ex122RatioSumToPair_injOn_domain (s : Set ℝ) :
    Set.InjOn ex122RatioSumToPair (ex122RatioSumDomain s) := by
  intro y hy z hz h
  have hypos : 0 < y.2 := hy.2
  have hzpos : 0 < z.2 := hz.2
  calc
    y = ex122PairToRatioSum (ex122RatioSumToPair y) := by
      exact (ex122PairToRatioSum_ratioSumToPair (ne_of_gt hypos)).symm
    _ = ex122PairToRatioSum (ex122RatioSumToPair z) := by rw [h]
    _ = z := by
      exact ex122PairToRatioSum_ratioSumToPair (ne_of_gt hzpos)

/-- The ratio-sum chart is differentiable on every source domain. This supplies
the differentiability hypothesis for Mathlib's Jacobian change-of-variables
theorem. -/
theorem ex122RatioSumToPair_hasFDerivWithinAt_fderiv (s : Set ℝ) :
    ∀ y ∈ ex122RatioSumDomain s,
      HasFDerivWithinAt ex122RatioSumToPair
        (fderiv ℝ ex122RatioSumToPair y) (ex122RatioSumDomain s) y := by
  intro y _hy
  exact ((by
    unfold ex122RatioSumToPair
    fun_prop : DifferentiableAt ℝ ex122RatioSumToPair y).hasFDerivAt).hasFDerivWithinAt

theorem ex122RatioSumToPair_abs_fderiv_det_on_domain (s : Set ℝ) :
    ∀ y ∈ ex122RatioSumDomain s,
      |(fderiv ℝ ex122RatioSumToPair y).det| = y.2 := by
  intro y hy
  exact ex122RatioSumToPair_abs_fderiv_det_of_snd_pos hy.2

/-- Pair-coordinate version of `ex122GammaRatioLawTwo`. This exposes the
remaining blocker as the classical two-dimensional product-Gamma
change-of-variables problem. -/
def ex122GammaPairRatioLawTwo (α₁ α₂ β : ℝ) : Measure ℝ :=
  Measure.map ex122GammaPairRatioMapTwo
    (ex122GammaPairLawTwo α₁ α₂ β)

theorem measurable_ex122GammaPDF (α r : ℝ) :
    Measurable (ProbabilityTheory.gammaPDF α r) := by
  unfold ProbabilityTheory.gammaPDF
  fun_prop

theorem measurable_ex122BetaPDF (α₁ α₂ : ℝ) :
    Measurable (ProbabilityTheory.betaPDF α₁ α₂) := by
  unfold ProbabilityTheory.betaPDF
  fun_prop

/-- Product-set Tonelli helper for separated `ℝ≥0∞` integrands on
`s ×ˢ t` with Lebesgue product measure. -/
theorem ex122_setLIntegral_prod_mul
    {s t : Set ℝ} {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ z in s ×ˢ t, f z.1 * g z.2 ∂(volume : Measure (ℝ × ℝ))) =
      (∫⁻ x in s, f x ∂(volume : Measure ℝ)) *
        (∫⁻ y in t, g y ∂(volume : Measure ℝ)) := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.setLIntegral_prod]
  · exact MeasureTheory.lintegral_lintegral_mul
      (μ := (volume : Measure ℝ).restrict s)
      (ν := (volume : Measure ℝ).restrict t)
      hf.aemeasurable hg.aemeasurable
  · exact ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aemeasurable

/-- Since Lebesgue measure ignores the endpoint and Gamma pdfs integrate to one
on `[0,∞)`, the same normalization holds on `(0,∞)`. -/
theorem ex122_lintegral_Ioi_gammaPDF_eq_one
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ProbabilityTheory.gammaPDF a r t
        ∂(volume : Measure ℝ)) = 1 := by
  calc
    (∫⁻ t in Set.Ioi (0 : ℝ), ProbabilityTheory.gammaPDF a r t
        ∂(volume : Measure ℝ))
        = ∫⁻ t in Set.Ici (0 : ℝ), ProbabilityTheory.gammaPDF a r t
            ∂(volume : Measure ℝ) := by
          exact MeasureTheory.setLIntegral_congr
            (μ := (volume : Measure ℝ))
            (f := ProbabilityTheory.gammaPDF a r)
            (Ioi_ae_eq_Ici (a := (0 : ℝ)))
    _ = ∫⁻ t, ProbabilityTheory.gammaPDF a r t ∂(volume : Measure ℝ) := by
      have hneg :
          (∫⁻ t in (Set.Ici (0 : ℝ))ᶜ, ProbabilityTheory.gammaPDF a r t
              ∂(volume : Measure ℝ)) = 0 := by
        rw [Set.compl_Ici]
        exact ProbabilityTheory.lintegral_gammaPDF_of_nonpos
          (x := (0 : ℝ)) (a := a) (r := r) le_rfl
      have hsplit :=
        MeasureTheory.lintegral_add_compl
          (μ := (volume : Measure ℝ))
          (fun t => ProbabilityTheory.gammaPDF a r t)
          (A := Set.Ici (0 : ℝ)) measurableSet_Ici
      rw [hneg, add_zero] at hsplit
      exact hsplit
    _ = 1 := ProbabilityTheory.lintegral_gammaPDF_eq_one ha hr

/-- Real-valued version of Gamma pdf normalization on `(0,∞)`. This is the
one-dimensional total-mass integral needed after separating the normalized-Gamma
change of variables. -/
theorem ex122_integral_Ioi_gammaPDFReal_eq_one
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t in Set.Ioi (0 : ℝ), ProbabilityTheory.gammaPDFReal a r t
        ∂(volume : Measure ℝ)) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae]
  · simpa [ProbabilityTheory.gammaPDF] using
      congrArg ENNReal.toReal (ex122_lintegral_Ioi_gammaPDF_eq_one ha hr)
  · exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t _ht => ProbabilityTheory.gammaPDFReal_nonneg ha hr t)
  · exact (ProbabilityTheory.measurable_gammaPDFReal a r).aestronglyMeasurable

theorem ex122ProjectedGammaCOVDensity_eq_projectedDensity_on_openSimplex
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ} {y : Fin n → ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    (hy : ∀ i, 0 < y i) (hylast : 0 < ex122ProjectedLastCoord y) :
    ex122ProjectedGammaCOVDensity α β y =
      ex122DirichletProjectedDensity α y := by
  have hsum_pos : 0 < ∑ i : Fin (n + 1), α i := by
    have hne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := ⟨0, by simp⟩
    exact Finset.sum_pos (fun i _ => hα i) hne
  calc
    ex122ProjectedGammaCOVDensity α β y =
        ∫ s in Set.Ioi (0 : ℝ),
          ex122DirichletProjectedDensity α y *
            ProbabilityTheory.gammaPDFReal (∑ i : Fin (n + 1), α i) β⁻¹ s
          ∂(volume : Measure ℝ) := by
          unfold ex122ProjectedGammaCOVDensity
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro s hs
          calc
            (s ^ n *
                (∏ i : Fin n,
                  ProbabilityTheory.gammaPDFReal (α (Fin.castSucc i)) β⁻¹
                    (y i * s))) *
                ProbabilityTheory.gammaPDFReal (α (Fin.last n)) β⁻¹
                  (ex122ProjectedLastCoord y * s) =
              s ^ n *
                (∏ i : Fin n,
                  ProbabilityTheory.gammaPDFReal (α (Fin.castSucc i)) β⁻¹
                    (y i * s)) *
                ProbabilityTheory.gammaPDFReal (α (Fin.last n)) β⁻¹
                  (ex122ProjectedLastCoord y * s) := by
                ring
            _ = s ^ n *
                ex122GammaProductPDFReal α β (ex122ProjectedChart y s) := by
                exact ex122ProjectedGammaCOVIntegrand_eq_chart_productPDF α β y s
            _ = ex122DirichletProjectedDensity α y *
                ProbabilityTheory.gammaPDFReal (∑ i : Fin (n + 1), α i) β⁻¹ s := by
                exact ex122ProjectedGammaCOVIntegrand_factorized
                  α hα hβ hy hylast hs
    _ = ex122DirichletProjectedDensity α y *
        (∫ s in Set.Ioi (0 : ℝ),
          ProbabilityTheory.gammaPDFReal (∑ i : Fin (n + 1), α i) β⁻¹ s
          ∂(volume : Measure ℝ)) := by
          rw [integral_const_mul]
    _ = ex122DirichletProjectedDensity α y := by
          rw [ex122_integral_Ioi_gammaPDFReal_eq_one
            (ha := hsum_pos) (hr := inv_pos.mpr hβ), mul_one]

theorem ex122ProjectedGammaCOVDensity_eq_projectedDensity_of_mem_openSimplex
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ} {y : Fin n → ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    (hy : y ∈ ex122ProjectedSimplexInterior n) :
    ex122ProjectedGammaCOVDensity α β y =
      ex122DirichletProjectedDensity α y := by
  exact ex122ProjectedGammaCOVDensity_eq_projectedDensity_on_openSimplex
    α hα hβ hy.1 hy.2

theorem ex122ProjectedDensityObligations_of_lintegral_preimage
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    (hCOV : ex122ProjectedCOVLIntegralPreimageIdentity α β) :
    Ex122ProjectedDensityObligations α β := by
  refine ⟨?_, ?_, ?_⟩
  · exact ex122GammaProductLaw_eq_gammaProductDensityMeasure α hα hβ
  · exact ex122ProjectedDirichletLaw_eq_COVMeasure_of_lintegral_preimage
      α hα hβ hCOV
  · intro y hy
    exact ex122ProjectedGammaCOVDensity_eq_projectedDensity_of_mem_openSimplex
      α hα hβ hy

theorem ex122ProjectedDensityObligations_of_pos
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    Ex122ProjectedDensityObligations α β := by
  exact ex122ProjectedDensityObligations_of_lintegral_preimage
    α hα hβ (ex122ProjectedCOVLIntegralPreimageIdentity_of_pos α hα hβ)

theorem ex122ProjectedDirichletLaw_eq_projectedDensityMeasure_of_pos
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122ProjectedDirichletLaw α β = ex122ProjectedDensityMeasure α := by
  rw [ex122ProjectedDensityMeasure_eq_withDensity_DirichletPDF]
  simpa [ex122ProjectedDirichletLaw, ex122ProjectFirst, ex122DirichletLaw,
    ex122GammaProductLaw, ex122GammaScaleLaw, ex122NormalizedVector, ex122GammaTotal,
    ProjectedDirichletLaw, DirichletLaw, gammaProductLaw, gammaScaleLaw,
    sourceNormalizedVector, gammaVectorTotal, projectFirst] using
    ProjectedDirichletLaw_eq_withDensity_DirichletPDF_positive
      (n := n + 1) (Nat.succ_pos n) α β hα hβ

/-- The ordinary pair-coordinate Gamma product law is exactly the two-dimensional
Lebesgue density obtained by multiplying the two Mathlib Gamma pdfs. This isolates
the remaining blocker from product-measure bookkeeping. -/
theorem ex122GammaPairLawTwo_eq_withDensity_productGammaPDF
    (α₁ α₂ β : ℝ) :
    ex122GammaPairLawTwo α₁ α₂ β =
      (volume : Measure (ℝ × ℝ)).withDensity
        (fun x => ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
          ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2) := by
  unfold ex122GammaPairLawTwo ex122GammaScaleLaw ProbabilityTheory.gammaMeasure
  rw [prod_withDensity
    (measurable_ex122GammaPDF α₁ β⁻¹)
    (measurable_ex122GammaPDF α₂ β⁻¹)]
  rw [← Measure.volume_eq_prod ℝ ℝ]

/-- Applying the Jacobian theorem to the ratio-sum chart rewrites the
two-dimensional product-Gamma density over the chart image as an integral over
ratio `u` and total mass `t`; the Jacobian factor is exactly `t`. -/
theorem ex122_lintegral_image_ratioSumDomain_productGammaPDF
    (α₁ α₂ β : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫⁻ x in ex122RatioSumToPair '' ex122RatioSumDomain s,
      ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2 ∂(volume : Measure (ℝ × ℝ))) =
      ∫⁻ y in ex122RatioSumDomain s,
        ENNReal.ofReal y.2 *
          (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
            ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2)
          ∂(volume : Measure (ℝ × ℝ)) := by
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := (volume : Measure (ℝ × ℝ)))
    (hs := measurableSet_ex122RatioSumDomain hs)
    (hf' := ex122RatioSumToPair_hasFDerivWithinAt_fderiv s)
    (hf := ex122RatioSumToPair_injOn_domain s)
    (g := fun x : ℝ × ℝ =>
      ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2)]
  refine setLIntegral_congr_fun (measurableSet_ex122RatioSumDomain hs) ?_
  intro y hy
  change
    ENNReal.ofReal |(fderiv ℝ ex122RatioSumToPair y).det| *
      (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2) =
    ENNReal.ofReal y.2 *
      (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2)
  rw [ex122RatioSumToPair_abs_fderiv_det_on_domain s y hy]

/-- Interior ratio sets can therefore be pulled back to the ratio-total domain;
this is the concrete change-of-variables form immediately before separating
the remaining one-dimensional Gamma integral in `t`. -/
theorem ex122_lintegral_positiveRatioPreimage_eq_lintegral_ratioSumDomain
    (α₁ α₂ β : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hs01 : s ⊆ Set.Ioo (0 : ℝ) 1) :
    (∫⁻ x in ex122PositiveRatioPreimage s,
      ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2 ∂(volume : Measure (ℝ × ℝ))) =
      ∫⁻ y in ex122RatioSumDomain s,
        ENNReal.ofReal y.2 *
          (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
            ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2)
          ∂(volume : Measure (ℝ × ℝ)) := by
  rw [← ex122RatioSumToPair_image_domain_eq_positiveRatioPreimage hs01]
  exact ex122_lintegral_image_ratioSumDomain_productGammaPDF α₁ α₂ β hs

/-- Pointwise real-density factorization after the ratio-sum substitution:
the product of two same-rate Gamma densities times the Jacobian `t` separates
as the Beta density in `u` times the Gamma density of the total mass `t`. -/
theorem ex122_gammaPDFReal_ratioSum_mul_jacobian_eq_betaPDFReal_mul_gammaPDFReal
    {α₁ α₂ β u t : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hu0 : 0 < u) (hu1 : u < 1) (ht : 0 < t) :
    ProbabilityTheory.gammaPDFReal α₁ β⁻¹ (u * t) *
        ProbabilityTheory.gammaPDFReal α₂ β⁻¹ ((1 - u) * t) * t =
      ProbabilityTheory.betaPDFReal α₁ α₂ u *
        ProbabilityTheory.gammaPDFReal (α₁ + α₂) β⁻¹ t := by
  have hr : 0 < β⁻¹ := inv_pos.mpr hβ
  have hut : 0 ≤ u * t := (mul_pos hu0 ht).le
  have h1ut : 0 ≤ (1 - u) * t := (mul_pos (sub_pos.mpr hu1) ht).le
  have ht0 : 0 ≤ t := ht.le
  rw [ProbabilityTheory.gammaPDFReal, if_pos hut]
  rw [ProbabilityTheory.gammaPDFReal, if_pos h1ut]
  rw [ProbabilityTheory.gammaPDFReal, if_pos ht0]
  rw [ProbabilityTheory.betaPDFReal, if_pos ⟨hu0, hu1⟩]
  rw [ProbabilityTheory.beta]
  have hmul₁ : (u * t) ^ (α₁ - 1) = u ^ (α₁ - 1) * t ^ (α₁ - 1) := by
    exact Real.mul_rpow hu0.le ht.le
  have hmul₂ : ((1 - u) * t) ^ (α₂ - 1) =
      (1 - u) ^ (α₂ - 1) * t ^ (α₂ - 1) := by
    exact Real.mul_rpow (sub_pos.mpr hu1).le ht.le
  rw [hmul₁, hmul₂]
  have ht_pow :
      t ^ (α₁ - 1) * t ^ (α₂ - 1) * t = t ^ (α₁ + α₂ - 1) := by
    have hpow :=
      (Real.rpow_add ht (α₁ - 1) (α₂ - 1)).symm
    rw [hpow]
    have hpow_one := (Real.rpow_add ht (α₁ + α₂ - 2) 1)
    rw [Real.rpow_one] at hpow_one
    have hsum : α₁ - 1 + (α₂ - 1) = α₁ + α₂ - 2 := by ring
    have hsum2 : α₁ + α₂ - 2 + 1 = α₁ + α₂ - 1 := by ring
    rw [hsum, ← hpow_one, hsum2]
  rw [← ht_pow]
  rw [Real.rpow_add hr]
  have hexp :
      Real.exp (-(β⁻¹ * (u * t))) * Real.exp (-(β⁻¹ * ((1 - u) * t))) =
        Real.exp (-(β⁻¹ * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  field_simp [Real.Gamma_pos_of_pos hα₁, Real.Gamma_pos_of_pos hα₂,
    Real.Gamma_pos_of_pos (add_pos hα₁ hα₂)]

/-- The same pointwise factorization in the `ℝ≥0∞` pdfs used by lintegrals. -/
theorem ex122_gammaPDF_ratioSum_mul_jacobian_eq_betaPDF_mul_gammaPDF
    {α₁ α₂ β u t : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (hu0 : 0 < u) (hu1 : u < 1) (ht : 0 < t) :
    ENNReal.ofReal t *
        (ProbabilityTheory.gammaPDF α₁ β⁻¹ (u * t) *
          ProbabilityTheory.gammaPDF α₂ β⁻¹ ((1 - u) * t)) =
      ProbabilityTheory.betaPDF α₁ α₂ u *
        ProbabilityTheory.gammaPDF (α₁ + α₂) β⁻¹ t := by
  have hreal :=
    ex122_gammaPDFReal_ratioSum_mul_jacobian_eq_betaPDFReal_mul_gammaPDFReal
      hα₁ hα₂ hβ hu0 hu1 ht
  have hr : 0 < β⁻¹ := inv_pos.mpr hβ
  have hγ1_nonneg :
      0 ≤ ProbabilityTheory.gammaPDFReal α₁ β⁻¹ (u * t) :=
    ProbabilityTheory.gammaPDFReal_nonneg hα₁ hr (u * t)
  have hγ2_nonneg :
      0 ≤ ProbabilityTheory.gammaPDFReal α₂ β⁻¹ ((1 - u) * t) :=
    ProbabilityTheory.gammaPDFReal_nonneg hα₂ hr ((1 - u) * t)
  have hβ_nonneg :
      0 ≤ ProbabilityTheory.betaPDFReal α₁ α₂ u :=
    (ProbabilityTheory.betaPDFReal_pos hu0 hu1 hα₁ hα₂).le
  have hreal' :
      t *
          (ProbabilityTheory.gammaPDFReal α₁ β⁻¹ (u * t) *
            ProbabilityTheory.gammaPDFReal α₂ β⁻¹ ((1 - u) * t)) =
        ProbabilityTheory.betaPDFReal α₁ α₂ u *
          ProbabilityTheory.gammaPDFReal (α₁ + α₂) β⁻¹ t := by
    rw [← hreal]
    ring
  unfold ProbabilityTheory.gammaPDF ProbabilityTheory.betaPDF
  rw [← ENNReal.ofReal_mul hγ1_nonneg]
  rw [← ENNReal.ofReal_mul ht.le]
  rw [← ENNReal.ofReal_mul hβ_nonneg]
  exact congrArg ENNReal.ofReal hreal'

/-- After the ratio-sum change of variables, the integral over
`s × (0,∞)` separates into the Beta integral in the ratio coordinate and the
Gamma integral in the total-mass coordinate. -/
theorem ex122_lintegral_ratioSumDomain_eq_lintegral_betaPDF_mul_lintegral_gammaPDF
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    {s : Set ℝ} (hs : MeasurableSet s) (hs01 : s ⊆ Set.Ioo (0 : ℝ) 1) :
    (∫⁻ y in ex122RatioSumDomain s,
      ENNReal.ofReal y.2 *
        (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
          ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2)
        ∂(volume : Measure (ℝ × ℝ))) =
      (∫⁻ u in s, ProbabilityTheory.betaPDF α₁ α₂ u
          ∂(volume : Measure ℝ)) *
        (∫⁻ t in Set.Ioi (0 : ℝ),
          ProbabilityTheory.gammaPDF (α₁ + α₂) β⁻¹ t
          ∂(volume : Measure ℝ)) := by
  have hpoint :
      Set.EqOn
        (fun y : ℝ × ℝ =>
          ENNReal.ofReal y.2 *
            (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
              ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2))
        (fun y : ℝ × ℝ =>
          ProbabilityTheory.betaPDF α₁ α₂ y.1 *
            ProbabilityTheory.gammaPDF (α₁ + α₂) β⁻¹ y.2)
        (ex122RatioSumDomain s) := by
    intro y hy
    have hy01 := hs01 hy.1
    simpa [ex122RatioSumToPair] using
      (ex122_gammaPDF_ratioSum_mul_jacobian_eq_betaPDF_mul_gammaPDF
        hα₁ hα₂ hβ hy01.1 hy01.2 hy.2)
  calc
    (∫⁻ y in ex122RatioSumDomain s,
      ENNReal.ofReal y.2 *
        (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
          ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2)
        ∂(volume : Measure (ℝ × ℝ)))
        = ∫⁻ y in ex122RatioSumDomain s,
            ProbabilityTheory.betaPDF α₁ α₂ y.1 *
              ProbabilityTheory.gammaPDF (α₁ + α₂) β⁻¹ y.2
            ∂(volume : Measure (ℝ × ℝ)) := by
          exact setLIntegral_congr_fun (measurableSet_ex122RatioSumDomain hs) hpoint
    _ = (∫⁻ u in s, ProbabilityTheory.betaPDF α₁ α₂ u
            ∂(volume : Measure ℝ)) *
          (∫⁻ t in Set.Ioi (0 : ℝ),
            ProbabilityTheory.gammaPDF (α₁ + α₂) β⁻¹ t
            ∂(volume : Measure ℝ)) := by
        simpa [ex122RatioSumDomain] using
          (ex122_setLIntegral_prod_mul
            (s := s) (t := Set.Ioi (0 : ℝ))
            (f := ProbabilityTheory.betaPDF α₁ α₂)
            (g := ProbabilityTheory.gammaPDF (α₁ + α₂) β⁻¹)
            (measurable_ex122BetaPDF α₁ α₂)
            (measurable_ex122GammaPDF (α₁ + α₂) β⁻¹))

/-- The separated total-mass Gamma factor is normalized, leaving only the Beta
integral in the ratio coordinate. -/
theorem ex122_lintegral_ratioSumDomain_eq_lintegral_betaPDF
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    {s : Set ℝ} (hs : MeasurableSet s) (hs01 : s ⊆ Set.Ioo (0 : ℝ) 1) :
    (∫⁻ y in ex122RatioSumDomain s,
      ENNReal.ofReal y.2 *
        (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
          ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2)
        ∂(volume : Measure (ℝ × ℝ))) =
      ∫⁻ u in s, ProbabilityTheory.betaPDF α₁ α₂ u
        ∂(volume : Measure ℝ) := by
  rw [ex122_lintegral_ratioSumDomain_eq_lintegral_betaPDF_mul_lintegral_gammaPDF
    α₁ α₂ hα₁ hα₂ hβ hs hs01]
  rw [ex122_lintegral_Ioi_gammaPDF_eq_one
    (ha := add_pos hα₁ hα₂) (hr := inv_pos.mpr hβ), mul_one]

/-- For ratio sets inside `(0,1)`, the full Gamma-ratio preimage integral equals
the positive-quadrant preimage integral: every remaining point has at least one
negative coordinate, hence zero product-Gamma density. -/
theorem ex122_lintegral_preimage_eq_lintegral_positiveRatioPreimage
    (α₁ α₂ β : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hs01 : s ⊆ Set.Ioo (0 : ℝ) 1) :
    (∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s,
      ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2
        ∂(volume : Measure (ℝ × ℝ))) =
      ∫⁻ x in ex122PositiveRatioPreimage s,
        ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
          ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2
          ∂(volume : Measure (ℝ × ℝ)) := by
  let q : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2}
  let f : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
      ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2
  have hq : MeasurableSet q := by
    unfold q
    exact (measurable_fst measurableSet_Ioi).inter
      (measurable_snd measurableSet_Ioi)
  have hpre : MeasurableSet (ex122GammaPairRatioMapTwo ⁻¹' s) :=
    measurable_ex122GammaPairRatioMapTwo hs
  have hpos_eq :
      ex122PositiveRatioPreimage s = ex122GammaPairRatioMapTwo ⁻¹' s ∩ q := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.2, hx.1, hx.2.1⟩
    · intro hx
      exact ⟨hx.2.1, hx.2.2, hx.1⟩
  have hzero :
      Set.EqOn f 0 (ex122GammaPairRatioMapTwo ⁻¹' s \ q) := by
    intro x hx
    rcases hx with ⟨hxs, hxq⟩
    have hratio01 := hs01 hxs
    by_cases hx₁pos : 0 < x.1
    · have hx₂nonpos : x.2 ≤ 0 := by
        by_contra hx₂not
        exact hxq ⟨hx₁pos, lt_of_not_ge hx₂not⟩
      have hx₂ne : x.2 ≠ 0 := by
        intro hx₂eq
        by_cases hx₁zero : x.1 = 0
        · have hratio_zero : ex122GammaPairRatioMapTwo x = 0 := by
            unfold ex122GammaPairRatioMapTwo
            simp [hx₁zero]
          linarith [hratio01.1, hratio_zero]
        · have hratio_one : ex122GammaPairRatioMapTwo x = 1 := by
            unfold ex122GammaPairRatioMapTwo
            simp [hx₂eq, div_self hx₁zero]
          linarith [hratio01.2, hratio_one]
      have hx₂neg : x.2 < 0 := lt_of_le_of_ne hx₂nonpos hx₂ne
      simp [f, ProbabilityTheory.gammaPDF_of_neg hx₂neg]
    · have hx₁nonpos : x.1 ≤ 0 := le_of_not_gt hx₁pos
      have hx₁ne : x.1 ≠ 0 := by
        intro hx₁eq
        have hratio_zero : ex122GammaPairRatioMapTwo x = 0 := by
          unfold ex122GammaPairRatioMapTwo
          simp [hx₁eq]
        linarith [hratio01.1, hratio_zero]
      have hx₁neg : x.1 < 0 := lt_of_le_of_ne hx₁nonpos hx₁ne
      simp [f, ProbabilityTheory.gammaPDF_of_neg hx₁neg]
  have hdiff_zero :
      (∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s \ q, f x
          ∂(volume : Measure (ℝ × ℝ))) = 0 := by
    exact setLIntegral_eq_zero (hpre.diff hq) hzero
  have hsplit :=
    MeasureTheory.lintegral_inter_add_diff
      (μ := (volume : Measure (ℝ × ℝ)))
      (f := f) (A := ex122GammaPairRatioMapTwo ⁻¹' s) hq
  rw [hdiff_zero, add_zero] at hsplit
  calc
    (∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s,
      ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2
        ∂(volume : Measure (ℝ × ℝ)))
        = ∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s ∩ q, f x
            ∂(volume : Measure (ℝ × ℝ)) := by
          exact hsplit.symm
    _ = ∫⁻ x in ex122PositiveRatioPreimage s, f x
          ∂(volume : Measure (ℝ × ℝ)) := by
        rw [hpos_eq]

/-- The concrete preimage integral identity for interior ratio sets, after
Jacobian substitution, Tonelli separation, and Gamma normalization. -/
theorem ex122_lintegral_preimage_eq_lintegral_betaPDF
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    {s : Set ℝ} (hs : MeasurableSet s) (hs01 : s ⊆ Set.Ioo (0 : ℝ) 1) :
    (∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s,
      ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2
        ∂(volume : Measure (ℝ × ℝ))) =
      ∫⁻ y in s, ProbabilityTheory.betaPDF α₁ α₂ y
        ∂(volume : Measure ℝ) := by
  calc
    (∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s,
      ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
        ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2
        ∂(volume : Measure (ℝ × ℝ)))
        = ∫⁻ x in ex122PositiveRatioPreimage s,
            ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
              ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2
            ∂(volume : Measure (ℝ × ℝ)) := by
          exact ex122_lintegral_preimage_eq_lintegral_positiveRatioPreimage
            α₁ α₂ β hs hs01
    _ = ∫⁻ y in ex122RatioSumDomain s,
          ENNReal.ofReal y.2 *
            (ProbabilityTheory.gammaPDF α₁ β⁻¹ (ex122RatioSumToPair y).1 *
              ProbabilityTheory.gammaPDF α₂ β⁻¹ (ex122RatioSumToPair y).2)
          ∂(volume : Measure (ℝ × ℝ)) := by
        exact ex122_lintegral_positiveRatioPreimage_eq_lintegral_ratioSumDomain
          α₁ α₂ β hs hs01
    _ = ∫⁻ y in s, ProbabilityTheory.betaPDF α₁ α₂ y
          ∂(volume : Measure ℝ) := by
        exact ex122_lintegral_ratioSumDomain_eq_lintegral_betaPDF
          α₁ α₂ hα₁ hα₂ hβ hs hs01

/-- Exact measure-set form of the remaining two-dimensional change-of-variables
blocker: proving the pair-product Gamma ratio has Beta law is equivalent to this
concrete preimage integral identity for every measurable real set. -/
theorem ex122GammaPairRatioLawTwo_eq_betaMeasure_iff_lintegral_preimage
    (α₁ α₂ β : ℝ) :
    ex122GammaPairRatioLawTwo α₁ α₂ β =
        ProbabilityTheory.betaMeasure α₁ α₂ ↔
      ∀ s : Set ℝ, MeasurableSet s →
        (∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s,
          ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
            ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2 ∂(volume : Measure (ℝ × ℝ))) =
        (∫⁻ y in s, ProbabilityTheory.betaPDF α₁ α₂ y ∂(volume : Measure ℝ)) := by
  constructor
  · intro h s hs
    have hmeasure := congrArg (fun μ : Measure ℝ => μ s) h
    change
      (Measure.map ex122GammaPairRatioMapTwo
          (ex122GammaPairLawTwo α₁ α₂ β)) s =
        (ProbabilityTheory.betaMeasure α₁ α₂) s at hmeasure
    rw [ProbabilityTheory.betaMeasure,
      Measure.map_apply measurable_ex122GammaPairRatioMapTwo hs,
      ex122GammaPairLawTwo_eq_withDensity_productGammaPDF,
      withDensity_apply _
        (measurable_ex122GammaPairRatioMapTwo hs),
      withDensity_apply _ hs] at hmeasure
    exact hmeasure
  · intro h
    refine Measure.ext fun s hs => ?_
    rw [ex122GammaPairRatioLawTwo, ProbabilityTheory.betaMeasure,
      Measure.map_apply measurable_ex122GammaPairRatioMapTwo hs,
      ex122GammaPairLawTwo_eq_withDensity_productGammaPDF,
      withDensity_apply _
        (measurable_ex122GammaPairRatioMapTwo hs),
      withDensity_apply _ hs]
    exact h s hs

/-- The exact user-facing target statement, reduced to the same concrete
preimage-integral identity. The only unproved mathematical content is now the
interior nonlinear change of variables evaluating this integral as the Beta pdf. -/
theorem ex122_pair_product_gamma_ratio_eq_betaMeasure_iff_lintegral_preimage
    (α₁ α₂ β : ℝ) :
    Measure.map (fun x : ℝ × ℝ => x.1 / (x.1 + x.2))
        ((ex122GammaScaleLaw α₁ β).prod (ex122GammaScaleLaw α₂ β)) =
        ProbabilityTheory.betaMeasure α₁ α₂ ↔
      ∀ s : Set ℝ, MeasurableSet s →
        (∫⁻ x in (fun x : ℝ × ℝ => x.1 / (x.1 + x.2)) ⁻¹' s,
          ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
            ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2 ∂(volume : Measure (ℝ × ℝ))) =
        (∫⁻ y in s, ProbabilityTheory.betaPDF α₁ α₂ y ∂(volume : Measure ℝ)) := by
  simpa [ex122GammaPairRatioLawTwo, ex122GammaPairRatioMapTwo,
    ex122GammaPairLawTwo] using
    ex122GammaPairRatioLawTwo_eq_betaMeasure_iff_lintegral_preimage α₁ α₂ β

theorem ex122GammaRatioLawTwo_eq_pairRatioLawTwo
    (α₁ α₂ β : ℝ) :
    ex122GammaRatioLawTwo α₁ α₂ β =
      ex122GammaPairRatioLawTwo α₁ α₂ β := by
  unfold ex122GammaRatioLawTwo ex122GammaPairRatioLawTwo ex122GammaPairLawTwo
  have hpi :
      ex122GammaProductLaw (ex122TwoParameterAlpha α₁ α₂) β =
        Measure.pi ![ex122GammaScaleLaw α₁ β, ex122GammaScaleLaw α₂ β] := by
    unfold ex122GammaProductLaw
    congr with i
    fin_cases i <;> simp [ex122TwoParameterAlpha]
  rw [hpi]
  have hmp :
      MeasurePreserving MeasurableEquiv.finTwoArrow
        (Measure.pi ![ex122GammaScaleLaw α₁ β, ex122GammaScaleLaw α₂ β])
        ((ex122GammaScaleLaw α₁ β).prod (ex122GammaScaleLaw α₂ β)) :=
    measurePreserving_finTwoArrow_vec
      (ex122GammaScaleLaw α₁ β) (ex122GammaScaleLaw α₂ β)
  rw [← hmp.map_eq]
  rw [Measure.map_map measurable_ex122GammaPairRatioMapTwo hmp.measurable]
  apply Measure.map_congr
  filter_upwards with x
  simp [ex122GammaRatioMapTwo, ex122GammaPairRatioMapTwo, MeasurableEquiv.finTwoArrow]

theorem ex122GammaRatioLawTwo_isProbability
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122GammaRatioLawTwo α₁ α₂ β) := by
  unfold ex122GammaRatioLawTwo
  have hα : ∀ i : Fin 2, 0 < ex122TwoParameterAlpha α₁ α₂ i := by
    intro i
    fin_cases i <;> simp [ex122TwoParameterAlpha, hα₁, hα₂]
  letI :
      IsProbabilityMeasure
        (ex122GammaProductLaw (ex122TwoParameterAlpha α₁ α₂) β) :=
    ex122GammaProductLaw_isProbability
      (ex122TwoParameterAlpha α₁ α₂) hα hβ
  exact Measure.isProbabilityMeasure_map measurable_ex122GammaRatioMapTwo.aemeasurable

/-- The Gamma-ratio law has no mass outside the open unit interval. Thus the
remaining Gamma-ratio-to-Beta blocker is purely the interior density/change of
variables calculation, not a support or endpoint-mass issue. -/
theorem ex122GammaRatioLawTwo_supported_on_Ioo
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ∀ᵐ y ∂ex122GammaRatioLawTwo α₁ α₂ β, y ∈ Set.Ioo 0 1 := by
  unfold ex122GammaRatioLawTwo
  change
    ∀ᵐ y ∂Measure.map ex122GammaRatioMapTwo
      (ex122GammaProductLaw (ex122TwoParameterAlpha α₁ α₂) β),
      0 < y ∧ y < 1
  rw [MeasureTheory.ae_map_iff measurable_ex122GammaRatioMapTwo.aemeasurable
    measurableSet_Ioo]
  have hα : ∀ i : Fin 2, 0 < ex122TwoParameterAlpha α₁ α₂ i := by
    intro i
    fin_cases i <;> simp [ex122TwoParameterAlpha, hα₁, hα₂]
  filter_upwards
    [ex122GammaProductLaw_coordinates_positive_ae
      (ex122TwoParameterAlpha α₁ α₂) hα hβ] with x hx
  have hx0 : 0 < x 0 := hx 0
  have hx1 : 0 < x 1 := hx 1
  have hsum : 0 < x 0 + x 1 := add_pos hx0 hx1
  constructor
  · exact div_pos hx0 hsum
  · have hlt : x 0 < x 0 + x 1 := by linarith
    have hdivlt :
        x 0 / (x 0 + x 1) < (x 0 + x 1) / (x 0 + x 1) :=
      div_lt_div_of_pos_right hlt hsum
    simpa [ex122GammaRatioMapTwo, div_self (ne_of_gt hsum)] using hdivlt

theorem ex122GammaRatioLawTwo_Ioo_probability_one
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ex122GammaRatioLawTwo α₁ α₂ β (Set.Ioo 0 1) = 1 := by
  letI : IsProbabilityMeasure (ex122GammaRatioLawTwo α₁ α₂ β) :=
    ex122GammaRatioLawTwo_isProbability α₁ α₂ hα₁ hα₂ hβ
  exact (MeasureTheory.mem_ae_iff_prob_eq_one
    (μ := ex122GammaRatioLawTwo α₁ α₂ β) measurableSet_Ioo).1
    (ex122GammaRatioLawTwo_supported_on_Ioo α₁ α₂ hα₁ hα₂ hβ)

/-- If a measure is supported on a measurable region, measurable-set masses may
be computed after intersecting with that region. -/
theorem ex122_measure_apply_eq_inter_of_ae_mem
    {μ : Measure ℝ} {t s : Set ℝ}
    (ht : ∀ᵐ x ∂μ, x ∈ t) (hs : MeasurableSet s) :
    μ s = μ (s ∩ t) := by
  have hrestrict : μ.restrict t = μ :=
    Measure.restrict_eq_self_of_ae_mem ht
  have happly := congrArg (fun ν : Measure ℝ => ν s) hrestrict
  have hst : μ (s ∩ t) = μ s := by
    simpa [Measure.restrict_apply hs] using happly
  exact hst.symm

/-- To prove equality of two real measures supported on `(0, 1)`, it suffices
to check measurable subsets of `(0, 1)`. -/
theorem ex122_measure_ext_of_forall_measurableSet_Ioo
    {μ ν : Measure ℝ}
    (hμ : ∀ᵐ y ∂μ, y ∈ Set.Ioo 0 1)
    (hν : ∀ᵐ y ∂ν, y ∈ Set.Ioo 0 1)
    (h :
      ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo 0 1 →
        μ s = ν s) :
    μ = ν := by
  ext s hs
  rw [ex122_measure_apply_eq_inter_of_ae_mem hμ hs,
    ex122_measure_apply_eq_inter_of_ae_mem hν hs]
  exact h (s ∩ Set.Ioo 0 1) (hs.inter measurableSet_Ioo) Set.inter_subset_right

theorem ex122_betaMeasure_supported_on_Ioo (α₁ α₂ : ℝ) :
    ∀ᵐ y ∂ProbabilityTheory.betaMeasure α₁ α₂, y ∈ Set.Ioo 0 1 := by
  rw [ae_iff]
  have hcompl :
      {y : ℝ | ¬ y ∈ Set.Ioo (0 : ℝ) 1} =
        Set.Iic (0 : ℝ) ∪ Set.Ici (1 : ℝ) := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hy
      simpa only [Set.mem_union, Set.mem_Iic, Set.mem_Ici] using hy
    · intro hy
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici] at hy
      simpa only [Set.mem_Ioo, not_and_or, not_lt] using hy
  rw [hcompl, ProbabilityTheory.betaMeasure]
  exact measure_union_null
    (by
      rw [withDensity_apply _ measurableSet_Iic]
      exact setLIntegral_eq_zero measurableSet_Iic
        (fun y hy => ProbabilityTheory.betaPDF_eq_zero_of_nonpos hy))
    (by
      rw [withDensity_apply _ measurableSet_Ici]
      exact setLIntegral_eq_zero measurableSet_Ici
        (fun y hy => ProbabilityTheory.betaPDF_eq_zero_of_one_le hy))

theorem ex122_betaMeasure_Ioo_probability_one
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ProbabilityTheory.betaMeasure α₁ α₂ (Set.Ioo 0 1) = 1 := by
  letI : IsProbabilityMeasure (ProbabilityTheory.betaMeasure α₁ α₂) :=
    ProbabilityTheory.isProbabilityMeasureBeta hα₁ hα₂
  exact (MeasureTheory.mem_ae_iff_prob_eq_one
    (μ := ProbabilityTheory.betaMeasure α₁ α₂) measurableSet_Ioo).1
    (ex122_betaMeasure_supported_on_Ioo α₁ α₂)

theorem ex122GammaPairRatioLawTwo_isProbability
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122GammaPairRatioLawTwo α₁ α₂ β) := by
  simpa [ex122GammaRatioLawTwo_eq_pairRatioLawTwo α₁ α₂ β] using
    ex122GammaRatioLawTwo_isProbability α₁ α₂ hα₁ hα₂ hβ

theorem ex122GammaPairRatioLawTwo_supported_on_Ioo
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ∀ᵐ y ∂ex122GammaPairRatioLawTwo α₁ α₂ β, y ∈ Set.Ioo 0 1 := by
  simpa [ex122GammaRatioLawTwo_eq_pairRatioLawTwo α₁ α₂ β] using
    ex122GammaRatioLawTwo_supported_on_Ioo α₁ α₂ hα₁ hα₂ hβ

theorem ex122GammaPairRatioLawTwo_Ioo_probability_one
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ex122GammaPairRatioLawTwo α₁ α₂ β (Set.Ioo 0 1) = 1 := by
  letI : IsProbabilityMeasure (ex122GammaPairRatioLawTwo α₁ α₂ β) :=
    ex122GammaPairRatioLawTwo_isProbability α₁ α₂ hα₁ hα₂ hβ
  exact (MeasureTheory.mem_ae_iff_prob_eq_one
    (μ := ex122GammaPairRatioLawTwo α₁ α₂ β) measurableSet_Ioo).1
    (ex122GammaPairRatioLawTwo_supported_on_Ioo α₁ α₂ hα₁ hα₂ hβ)

/-- Interior-only form of the remaining nonlinear ratio-transform blocker. Since
both sides are supported on `(0, 1)`, the concrete preimage-integral identity
only has to be proved for measurable subsets of that open interval. -/
theorem ex122GammaPairRatioLawTwo_eq_betaMeasure_iff_lintegral_preimage_Ioo
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ex122GammaPairRatioLawTwo α₁ α₂ β =
        ProbabilityTheory.betaMeasure α₁ α₂ ↔
      ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo 0 1 →
        (∫⁻ x in ex122GammaPairRatioMapTwo ⁻¹' s,
          ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
            ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2 ∂(volume : Measure (ℝ × ℝ))) =
        (∫⁻ y in s, ProbabilityTheory.betaPDF α₁ α₂ y ∂(volume : Measure ℝ)) := by
  constructor
  · intro h s hs _hsub
    exact
      (ex122GammaPairRatioLawTwo_eq_betaMeasure_iff_lintegral_preimage
        α₁ α₂ β).1 h s hs
  · intro h
    apply ex122_measure_ext_of_forall_measurableSet_Ioo
      (ex122GammaPairRatioLawTwo_supported_on_Ioo α₁ α₂ hα₁ hα₂ hβ)
      (ex122_betaMeasure_supported_on_Ioo α₁ α₂)
    intro s hs hsub
    rw [ex122GammaPairRatioLawTwo, ProbabilityTheory.betaMeasure,
      Measure.map_apply measurable_ex122GammaPairRatioMapTwo hs,
      ex122GammaPairLawTwo_eq_withDensity_productGammaPDF,
      withDensity_apply _ (measurable_ex122GammaPairRatioMapTwo hs),
      withDensity_apply _ hs]
    exact h s hs hsub

theorem ex122_pair_product_gamma_ratio_eq_betaMeasure_iff_lintegral_preimage_Ioo
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    Measure.map (fun x : ℝ × ℝ => x.1 / (x.1 + x.2))
        ((ex122GammaScaleLaw α₁ β).prod (ex122GammaScaleLaw α₂ β)) =
        ProbabilityTheory.betaMeasure α₁ α₂ ↔
      ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioo 0 1 →
        (∫⁻ x in (fun x : ℝ × ℝ => x.1 / (x.1 + x.2)) ⁻¹' s,
          ProbabilityTheory.gammaPDF α₁ β⁻¹ x.1 *
            ProbabilityTheory.gammaPDF α₂ β⁻¹ x.2 ∂(volume : Measure (ℝ × ℝ))) =
        (∫⁻ y in s, ProbabilityTheory.betaPDF α₁ α₂ y ∂(volume : Measure ℝ)) := by
  simpa [ex122GammaPairRatioLawTwo, ex122GammaPairRatioMapTwo,
    ex122GammaPairLawTwo] using
    ex122GammaPairRatioLawTwo_eq_betaMeasure_iff_lintegral_preimage_Ioo
      α₁ α₂ hα₁ hα₂ hβ

/-- The pair-coordinate Gamma ratio has Mathlib's Beta law. This discharges the
previous measure-level blocker by the concrete preimage integral identity. -/
theorem ex122GammaPairRatioLawTwo_eq_betaMeasure
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ex122GammaPairRatioLawTwo α₁ α₂ β =
      ProbabilityTheory.betaMeasure α₁ α₂ := by
  exact
    (ex122GammaPairRatioLawTwo_eq_betaMeasure_iff_lintegral_preimage_Ioo
      (β := β) α₁ α₂ hα₁ hα₂ hβ).2
      (fun s hs hs01 =>
        ex122_lintegral_preimage_eq_lintegral_betaPDF
          α₁ α₂ hα₁ hα₂ hβ hs hs01)

theorem ex122_pair_product_gamma_ratio_eq_betaMeasure
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    Measure.map (fun x : ℝ × ℝ => x.1 / (x.1 + x.2))
        ((ex122GammaScaleLaw α₁ β).prod (ex122GammaScaleLaw α₂ β)) =
        ProbabilityTheory.betaMeasure α₁ α₂ := by
  simpa [ex122GammaPairRatioLawTwo, ex122GammaPairRatioMapTwo,
    ex122GammaPairLawTwo] using
    ex122GammaPairRatioLawTwo_eq_betaMeasure
      α₁ α₂ hα₁ hα₂ hβ

theorem ex122GammaRatioLawTwo_eq_betaMeasure
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ex122GammaRatioLawTwo α₁ α₂ β =
      ProbabilityTheory.betaMeasure α₁ α₂ := by
  rw [ex122GammaRatioLawTwo_eq_pairRatioLawTwo]
  exact ex122GammaPairRatioLawTwo_eq_betaMeasure
    α₁ α₂ hα₁ hα₂ hβ

/-- In the two-parameter case, the post-Jacobian total-mass integral evaluates
to the projected Dirichlet density on the open projected simplex. This is the
`n = 1` instance of the `gammaIntegralNormalizes` obligation away from boundary
faces. -/
theorem ex122ProjectedGammaCOVDensity_two_eq_projectedDensity_on_Ioo
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (y : Fin 1 → ℝ) (hy0 : 0 < y 0) (hy1 : y 0 < 1) :
    ex122ProjectedGammaCOVDensity (ex122TwoParameterAlpha α₁ α₂) β y =
      ex122DirichletProjectedDensity (ex122TwoParameterAlpha α₁ α₂) y := by
  calc
    ex122ProjectedGammaCOVDensity (ex122TwoParameterAlpha α₁ α₂) β y
        = ∫ s in Set.Ioi (0 : ℝ),
            ProbabilityTheory.betaPDFReal α₁ α₂ (y 0) *
              ProbabilityTheory.gammaPDFReal (α₁ + α₂) β⁻¹ s
            ∂(volume : Measure ℝ) := by
          unfold ex122ProjectedGammaCOVDensity
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro s hs
          have hfactor :=
            ex122_gammaPDFReal_ratioSum_mul_jacobian_eq_betaPDFReal_mul_gammaPDFReal
              hα₁ hα₂ hβ hy0 hy1 hs
          simpa [ex122TwoParameterAlpha, ex122ProjectedLastCoord,
            Fin.prod_univ_one, Fin.sum_univ_one, pow_one, mul_comm, mul_left_comm,
            mul_assoc] using hfactor
    _ = ProbabilityTheory.betaPDFReal α₁ α₂ (y 0) *
          (∫ s in Set.Ioi (0 : ℝ),
            ProbabilityTheory.gammaPDFReal (α₁ + α₂) β⁻¹ s
            ∂(volume : Measure ℝ)) := by
        rw [integral_const_mul]
    _ = ProbabilityTheory.betaPDFReal α₁ α₂ (y 0) := by
        rw [ex122_integral_Ioi_gammaPDFReal_eq_one
          (ha := add_pos hα₁ hα₂) (hr := inv_pos.mpr hβ), mul_one]
    _ = ex122DirichletProjectedDensity (ex122TwoParameterAlpha α₁ α₂) y := by
        rw [ex122_betaPDFReal_eq_betaDensity_on_Ioo hα₁ hα₂ hy0 hy1]
        exact (ex122_dirichletProjectedDensity_two_eq_betaDensity α₁ α₂ y).symm

/-- The real first-coordinate projected Dirichlet law is definitionally the
Gamma-ratio pushforward after composing the two projection maps. -/
theorem ex122ProjectedDirichletLawFirstCoordTwo_eq_gammaRatioLawTwo
    (α₁ α₂ β : ℝ) :
    ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β =
      ex122GammaRatioLawTwo α₁ α₂ β := by
  unfold ex122ProjectedDirichletLawFirstCoordTwo ex122ProjectedDirichletLaw
    ex122DirichletLaw ex122GammaRatioLawTwo
  rw [Measure.map_map (measurable_pi_apply 0) measurable_ex122ProjectFirst]
  rw [Measure.map_map ((measurable_pi_apply 0).comp measurable_ex122ProjectFirst)
    measurable_ex122NormalizedVector]
  congr 1
  funext x
  simp [Function.comp_def, ex122ProjectFirst, ex122NormalizedVector, ex122GammaRatioMapTwo,
    ex122GammaTotal, Fin.sum_univ_two]

theorem ex122ProjectedDirichletLawFirstCoordTwo_eq_betaMeasure
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β =
      ProbabilityTheory.betaMeasure α₁ α₂ := by
  rw [ex122ProjectedDirichletLawFirstCoordTwo_eq_gammaRatioLawTwo]
  exact ex122GammaRatioLawTwo_eq_betaMeasure
    α₁ α₂ hα₁ hα₂ hβ

theorem ex122_betaMeasure_eq_projectedDensityMeasureTwo
    (α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ProbabilityTheory.betaMeasure α₁ α₂ =
      ex122ProjectedDensityMeasureTwo α₁ α₂ := by
  simpa [ex122ProjectedDensityMeasureTwo] using
    ex122_betaMeasure_eq_withDensity_projectedDensity_two α₁ α₂ hα₁ hα₂

theorem ex122ProjectedDirichletLawFirstCoordTwo_eq_projectedDensityMeasureTwo
    (α₁ α₂ : ℝ) {β : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β) :
    ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β =
      ex122ProjectedDensityMeasureTwo α₁ α₂ := by
  rw [ex122ProjectedDirichletLawFirstCoordTwo_eq_betaMeasure
    α₁ α₂ hα₁ hα₂ hβ]
  exact ex122_betaMeasure_eq_projectedDensityMeasureTwo α₁ α₂ hα₁ hα₂

/-- Minimal audited form of the remaining gap: after the already-proved
density-measure-to-Beta theorem, proving the projected-density equality is
equivalent to proving the Gamma-ratio pushforward has Mathlib's Beta law. -/
theorem ex122ProjectedDensityLaw_gap_iff_gammaRatioLawTwo_eq_betaMeasure
    (α₁ α₂ β : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β =
        ex122ProjectedDensityMeasureTwo α₁ α₂ ↔
      ex122GammaRatioLawTwo α₁ α₂ β =
        ProbabilityTheory.betaMeasure α₁ α₂ := by
  constructor
  · intro hProjectedDensityLaw
    rw [← ex122ProjectedDirichletLawFirstCoordTwo_eq_gammaRatioLawTwo]
    rw [hProjectedDensityLaw]
    exact (ex122_betaMeasure_eq_projectedDensityMeasureTwo α₁ α₂ hα₁ hα₂).symm
  · intro hRatio
    rw [ex122ProjectedDirichletLawFirstCoordTwo_eq_gammaRatioLawTwo]
    rw [hRatio]
    exact ex122_betaMeasure_eq_projectedDensityMeasureTwo α₁ α₂ hα₁ hα₂

/-- The normalized-Gamma construction for two source variables gives a real
first-coordinate law equal to the real-coordinate projection of the existing
Dirichlet pushforward law. -/
theorem ex122_independent_gamma_firstCoord_hasLaw_projectedDirichletLaw_two
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α₁ α₂ β : ℝ)
    (X : Fin 2 → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i)
      (ex122GammaScaleLaw ((ex122TwoParameterAlpha α₁ α₂) i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    HasLaw
      (fun ω => ex122NormalizedVector (fun i : Fin 2 => X i ω) 0)
      (ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β)
      P := by
  have hproj :
      HasLaw
        (fun ω i =>
          ex122NormalizedVector (fun j : Fin 2 => X j ω) (Fin.castSucc i))
        (ex122ProjectedDirichletLaw (ex122TwoParameterAlpha α₁ α₂) β)
        P := by
    exact ex122_projectFirst_hasLaw_projectedDirichlet
      (n := 1) P (ex122TwoParameterAlpha α₁ α₂) β X hXlaw hIndep
  have heval :
      HasLaw
        (fun y : Fin 1 → ℝ => y 0)
        (ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β)
        (ex122ProjectedDirichletLaw (ex122TwoParameterAlpha α₁ α₂) β) := by
    refine ⟨(measurable_pi_apply 0).aemeasurable, rfl⟩
  simpa [Function.comp_def, Fin.castSucc,
    ex122ProjectedDirichletLawFirstCoordTwo] using heval.comp hproj

/-- If the remaining projected-density law is supplied for the `n = 2` real
first-coordinate pushforward, the existing Beta density theorem immediately
identifies that pushforward with Mathlib's `betaMeasure`. -/
theorem ex122ProjectedDirichletLawFirstCoordTwo_eq_betaMeasure_of_projectedDensityLaw
    (α₁ α₂ β : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hProjectedDensityLaw :
      ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β =
        ex122ProjectedDensityMeasureTwo α₁ α₂) :
    ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β =
      ProbabilityTheory.betaMeasure α₁ α₂ := by
  rw [hProjectedDensityLaw]
  exact (ex122_betaMeasure_eq_projectedDensityMeasureTwo α₁ α₂ hα₁ hα₂).symm

/-- Conditional composition of the current proof spine: once the missing
`n = 2` projected-density equality is proved, the normalized-Gamma first
coordinate has Mathlib's Beta law. -/
theorem ex122_independent_gamma_firstCoord_hasLaw_betaMeasure_two_of_projectedDensityLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α₁ α₂ β : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (X : Fin 2 → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i)
      (ex122GammaScaleLaw ((ex122TwoParameterAlpha α₁ α₂) i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hProjectedDensityLaw :
      ex122ProjectedDirichletLawFirstCoordTwo α₁ α₂ β =
        ex122ProjectedDensityMeasureTwo α₁ α₂) :
    HasLaw
      (fun ω => ex122NormalizedVector (fun i : Fin 2 => X i ω) 0)
      (ProbabilityTheory.betaMeasure α₁ α₂)
      P := by
  have hfirst :=
    ex122_independent_gamma_firstCoord_hasLaw_projectedDirichletLaw_two
      P α₁ α₂ β X hXlaw hIndep
  have hlawEq :=
    ex122ProjectedDirichletLawFirstCoordTwo_eq_betaMeasure_of_projectedDensityLaw
      α₁ α₂ β hα₁ hα₂ hProjectedDensityLaw
  rwa [← hlawEq]

/-- Unconditional `n = 2` Beta law for the first normalized Gamma coordinate. -/
theorem ex122_independent_gamma_firstCoord_hasLaw_betaMeasure_two
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α₁ α₂ β : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ : 0 < β)
    (X : Fin 2 → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i)
      (ex122GammaScaleLaw ((ex122TwoParameterAlpha α₁ α₂) i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    HasLaw
      (fun ω => ex122NormalizedVector (fun i : Fin 2 => X i ω) 0)
      (ProbabilityTheory.betaMeasure α₁ α₂)
      P := by
  have hfirst :=
    ex122_independent_gamma_firstCoord_hasLaw_projectedDirichletLaw_two
      P α₁ α₂ β X hXlaw hIndep
  have hlawEq :=
    ex122ProjectedDirichletLawFirstCoordTwo_eq_betaMeasure
      α₁ α₂ hα₁ hα₂ hβ
  rwa [← hlawEq]

/-- The displayed sample parameter vector `(1, 1, 2)`. -/
def ex122SampleAlpha : Fin 3 → ℝ :=
  fun i => if i = 0 then 1 else if i = 1 then 1 else 2

theorem ex122SampleAlpha_pos : ∀ i, 0 < ex122SampleAlpha i := by
  intro i
  fin_cases i <;> norm_num [ex122SampleAlpha]

/-- The theorem-backed package for Example 1.2.2. -/
structure DirichletExample where
  parameter_count : ℕ
  alpha : Fin parameter_count → ℝ
  gammaScale : ℝ
  simplex : Set (Fin parameter_count → ℝ)
  projectionMap : (Fin parameter_count → ℝ) → Fin (parameter_count - 1) → ℝ
  projectedDensity : (Fin (parameter_count - 1) → ℝ) → ℝ
  betaDensity : ℝ → ℝ
  gammaProductLaw : Measure (Fin parameter_count → ℝ)
  dirichletLaw : Measure (Fin parameter_count → ℝ)
  projectedLaw : Measure (Fin (parameter_count - 1) → ℝ)
  alpha_pos : ∀ i, 0 < alpha i
  gammaScale_pos : 0 < gammaScale
  gammaProductLaw_eq :
    gammaProductLaw = ex122GammaProductLaw alpha gammaScale
  dirichletLaw_eq_normalized :
    dirichletLaw =
      Measure.map (fun x : Fin parameter_count → ℝ => ex122NormalizedVector x) gammaProductLaw
  projectedLaw_eq :
    projectedLaw = Measure.map projectionMap dirichletLaw
  dirichletLaw_isProbability : IsProbabilityMeasure dirichletLaw
  projectedLaw_isProbability : IsProbabilityMeasure projectedLaw
  normalized_mem_simplex :
    ∀ x : Fin parameter_count → ℝ,
      (∀ i, 0 ≤ x i) →
      0 < ex122GammaTotal x →
      ex122NormalizedVector x ∈ simplex
  dirichletLaw_simplex_probability_one :
    dirichletLaw simplex = 1
  independent_gamma_normalized_hasLaw :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Fin parameter_count → Ω → ℝ),
      (∀ i, HasLaw (X i) (ex122GammaScaleLaw (alpha i) gammaScale) P) →
      ProbabilityTheory.iIndepFun X P →
      HasLaw (fun ω => ex122NormalizedVector (fun i => X i ω)) dirichletLaw P
  independent_gamma_normalized_simplex_ae :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Fin parameter_count → Ω → ℝ),
      (∀ i, HasLaw (X i) (ex122GammaScaleLaw (alpha i) gammaScale) P) →
      ProbabilityTheory.iIndepFun X P →
      ∀ᵐ ω ∂P, ex122NormalizedVector (fun i => X i ω) ∈ simplex
  independent_gamma_projected_hasLaw :
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Fin parameter_count → Ω → ℝ),
      (∀ i, HasLaw (X i) (ex122GammaScaleLaw (alpha i) gammaScale) P) →
      ProbabilityTheory.iIndepFun X P →
      HasLaw
        (fun ω => projectionMap (ex122NormalizedVector (fun i => X i ω)))
        projectedLaw
        P
  simplex_volume_zero :
    (volume : Measure (Fin parameter_count → ℝ)) simplex = 0

/-- Exported declaration for Example 1.2.2, specialized to the displayed `(1,1,2)` sample. -/
def ex_1_2_2 : DirichletExample where
  parameter_count := 3
  alpha := ex122SampleAlpha
  gammaScale := 1
  simplex := ex122DirichletSimplex 2
  projectionMap := ex122ProjectFirst
  projectedDensity := ex122DirichletProjectedDensity ex122SampleAlpha
  betaDensity := ex122BetaDensity 1 1
  gammaProductLaw := ex122GammaProductLaw ex122SampleAlpha 1
  dirichletLaw := ex122DirichletLaw ex122SampleAlpha 1
  projectedLaw := ex122ProjectedDirichletLaw ex122SampleAlpha 1
  alpha_pos := ex122SampleAlpha_pos
  gammaScale_pos := by norm_num
  gammaProductLaw_eq := rfl
  dirichletLaw_eq_normalized := rfl
  projectedLaw_eq := rfl
  dirichletLaw_isProbability := ex122DirichletLaw_isProbability
    ex122SampleAlpha ex122SampleAlpha_pos (by norm_num)
  projectedLaw_isProbability := ex122ProjectedDirichletLaw_isProbability
    ex122SampleAlpha ex122SampleAlpha_pos (by norm_num)
  normalized_mem_simplex := by
    intro x hx hV
    exact ex122_normalized_mem_simplex x hx hV
  dirichletLaw_simplex_probability_one :=
    ex122DirichletLaw_simplex_probability_one ex122SampleAlpha ex122SampleAlpha_pos (by norm_num)
  independent_gamma_normalized_hasLaw := by
    intro Ω _ P _ X hXlaw hIndep
    exact ex122_independent_gamma_normalized_hasLaw_dirichlet P ex122SampleAlpha 1 X hXlaw hIndep
  independent_gamma_normalized_simplex_ae := by
    intro Ω _ P _ X hXlaw hIndep
    exact ex122_independent_gamma_normalized_simplex_ae P ex122SampleAlpha
      ex122SampleAlpha_pos (by norm_num) X hXlaw hIndep
  independent_gamma_projected_hasLaw := by
    intro Ω _ P _ X hXlaw hIndep
    simpa [ex122ProjectFirst] using
      (ex122_projectFirst_hasLaw_projectedDirichlet P ex122SampleAlpha 1 X hXlaw hIndep)
  simplex_volume_zero := ex122DirichletSimplex_volume_zero 2
