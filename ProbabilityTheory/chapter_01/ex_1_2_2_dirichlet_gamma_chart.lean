import ToyApollo.Output.ex_1_2_2_dirichlet_gamma_core
import ToyApollo.Support.DirichletGammaDensity

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section
/-- Projection from the simplex coordinates to the first `n` coordinates. -/
def ex122ProjectFirst {n : ℕ} (y : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => y (Fin.castSucc i)

theorem measurable_ex122ProjectFirst {n : ℕ} :
    Measurable (ex122ProjectFirst : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by
  simpa [ex122ProjectFirst] using (measurable_projectFirst (n := n + 1))

/-- Law of the lower-dimensional projection of the Dirichlet vector. -/
def ex122ProjectedDirichletLaw {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.map (ex122ProjectFirst : (Fin (n + 1) → ℝ) → Fin n → ℝ)
    (ex122DirichletLaw α β)

theorem ex122ProjectedDirichletLaw_isProbability {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122ProjectedDirichletLaw α β) := by
  simpa [ex122ProjectedDirichletLaw] using ProjectedDirichletLaw_isProbability α hα hβ

theorem ex122_projectFirst_hasLaw_projectedDirichlet
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : Fin (n + 1) → ℝ) (β : ℝ)
    (X : Fin (n + 1) → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (ex122GammaScaleLaw (α i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    HasLaw
      (fun ω i => ex122NormalizedVector (fun j => X j ω) (Fin.castSucc i))
      (ex122ProjectedDirichletLaw α β)
      P := by
  simpa [ex122GammaScaleLaw, ex122NormalizedVector, ex122ProjectedDirichletLaw,
    ex122ProjectFirst, projectFirst] using
    projected_normalized_hasLaw_projectedDirichlet P α β X hXlaw hIndep

/-- Last coordinate after projecting the Dirichlet simplex to the first `n` coordinates. -/
def ex122ProjectedLastCoord {n : ℕ} (y : Fin n → ℝ) : ℝ := 1 - ∑ i, y i

/-- The inverse projected-simplex chart at total mass `s`: the first `n`
coordinates are `y_i s`, and the final coordinate is
`(1 - ∑ y_i) s`. -/
def ex122ProjectedChart {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
    Fin (n + 1) → ℝ :=
  fun i =>
    if h : i = Fin.last n then
      ex122ProjectedLastCoord y * s
    else
      y (Fin.castPred i h) * s

theorem ex122ProjectedChart_castSucc {n : ℕ} (y : Fin n → ℝ) (s : ℝ)
    (i : Fin n) :
    ex122ProjectedChart y s (Fin.castSucc i) = y i * s := by
  simp [ex122ProjectedChart]

theorem ex122ProjectedChart_last {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
    ex122ProjectedChart y s (Fin.last n) = ex122ProjectedLastCoord y * s := by
  simp [ex122ProjectedChart]

theorem measurable_ex122ProjectedChart_pair {n : ℕ} :
    Measurable
      (fun z : (Fin n → ℝ) × ℝ => ex122ProjectedChart z.1 z.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i = Fin.last n
  · simp [ex122ProjectedChart, hi]
    have hlast :
        Continuous fun z : (Fin n → ℝ) × ℝ => ex122ProjectedLastCoord z.1 := by
      unfold ex122ProjectedLastCoord
      exact continuous_const.sub
        (continuous_finset_sum Finset.univ fun i _ =>
          (continuous_apply i).comp continuous_fst)
    exact hlast.measurable.mul measurable_snd
  · simp [ex122ProjectedChart, hi]
    exact (measurable_fst.eval (a := Fin.castPred i hi)).mul measurable_snd

theorem measurable_ex122ProjectedChart_fiber {n : ℕ} (y : Fin n → ℝ) :
    Measurable (fun t : ℝ => ex122ProjectedChart y t) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases hi : i = Fin.last n
  · simp [ex122ProjectedChart, hi]
    exact measurable_const.mul measurable_id
  · simp [ex122ProjectedChart, hi]
    exact measurable_const.mul measurable_id

/-- Normalizing constant in the projected Dirichlet density formula. -/
def ex122DirichletNormalizer {n : ℕ} (α : Fin (n + 1) → ℝ) : ℝ :=
  Real.Gamma (∑ i, α i) / ∏ i, Real.Gamma (α i)

/-- The lower-dimensional Dirichlet density on the first `n` coordinates. -/
def ex122DirichletProjectedDensity {n : ℕ} (α : Fin (n + 1) → ℝ)
    (y : Fin n → ℝ) : ℝ :=
  ex122DirichletNormalizer α *
    (∏ i : Fin n, (y i) ^ (α (Fin.castSucc i) - 1)) *
      (ex122ProjectedLastCoord y) ^ (α (Fin.last n) - 1)

theorem ex122_dirichletProjectedDensity_formula {n : ℕ} (α : Fin (n + 1) → ℝ)
    (y : Fin n → ℝ) :
    ex122DirichletProjectedDensity α y =
      ex122DirichletNormalizer α *
        (∏ i : Fin n, (y i) ^ (α (Fin.castSucc i) - 1)) *
          (ex122ProjectedLastCoord y) ^ (α (Fin.last n) - 1) := rfl

theorem continuous_ex122ProjectedLastCoord {n : ℕ} :
    Continuous (ex122ProjectedLastCoord : (Fin n → ℝ) → ℝ) := by
  unfold ex122ProjectedLastCoord
  exact continuous_const.sub
    (continuous_finset_sum Finset.univ fun i _ => continuous_apply i)

/-- The closed projected simplex supporting the lower-dimensional Dirichlet
density from equation (1.4). -/
def ex122ProjectedSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ 0 ≤ ex122ProjectedLastCoord y}

/-- The open projected simplex. This is the part of the closed support where
the Gamma-product COV integrand is on the positive branch of every Gamma pdf. -/
def ex122ProjectedSimplexInterior (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 < y i) ∧ 0 < ex122ProjectedLastCoord y}

theorem ex122ProjectedSimplexInterior_subset_simplex {n : ℕ} :
    ex122ProjectedSimplexInterior n ⊆ ex122ProjectedSimplex n := by
  intro y hy
  exact ⟨fun i => le_of_lt (hy.1 i), le_of_lt hy.2⟩

theorem measurableSet_ex122ProjectedSimplex (n : ℕ) :
    MeasurableSet (ex122ProjectedSimplex n) := by
  have hnonneg : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter fun i : Fin n =>
        isClosed_le continuous_const (continuous_apply i))
  have hlast : IsClosed {y : Fin n → ℝ | 0 ≤ ex122ProjectedLastCoord y} := by
    exact isClosed_le continuous_const continuous_ex122ProjectedLastCoord
  simpa [ex122ProjectedSimplex, Set.inter_def] using
    (hnonneg.inter hlast).measurableSet

theorem measurableSet_ex122ProjectedSimplexInterior (n : ℕ) :
    MeasurableSet (ex122ProjectedSimplexInterior n) := by
  have hpos : MeasurableSet {y : Fin n → ℝ | ∀ i, 0 < y i} := by
    simpa [Set.setOf_forall] using
      (MeasurableSet.iInter fun i : Fin n =>
        (isOpen_lt continuous_const (continuous_apply i)).measurableSet)
  have hlast : MeasurableSet {y : Fin n → ℝ | 0 < ex122ProjectedLastCoord y} := by
    exact (isOpen_lt continuous_const continuous_ex122ProjectedLastCoord).measurableSet
  simpa [ex122ProjectedSimplexInterior, Set.inter_def] using
    hpos.inter hlast

/-- A projected coordinate face has zero Lebesgue measure. -/
theorem ex122ProjectedCoord_zero_volume_zero {n : ℕ} (i : Fin n) :
    (volume : Measure (Fin n → ℝ)) {y | y i = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i 0

/-- The reconstructed final-coordinate face has zero Lebesgue measure. -/
theorem ex122ProjectedLastCoord_zero_volume_zero (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) {y | ex122ProjectedLastCoord y = 0} = 0 := by
  refine measure_mono_null ?_
    (Measure.addHaar_affineSubspace volume (fintypeAffineCoords (Fin n) ℝ) ?_)
  · intro y hy
    exact (mem_fintypeAffineCoords_iff_sum).2 (by
      simp [ex122ProjectedLastCoord] at hy
      linarith)
  · intro htop
    have hzero_mem :
        (0 : Fin n → ℝ) ∈ (⊤ : AffineSubspace ℝ (Fin n → ℝ)) := by
      simp
    have hzero_mem' :
        (0 : Fin n → ℝ) ∈ fintypeAffineCoords (Fin n) ℝ := by
      simp [htop] at hzero_mem ⊢
    have hsum : (∑ i : Fin n, (0 : Fin n → ℝ) i) = (1 : ℝ) :=
      (mem_fintypeAffineCoords_iff_sum).1 hzero_mem'
    simp at hsum

/-- The closed projected simplex and its open interior differ only on a
Lebesgue-null finite union of faces. Thus endpoint values of the displayed
density are irrelevant for the induced `withDensity` measure. -/
theorem ex122ProjectedSimplex_diff_interior_volume_zero (n : ℕ) :
    (volume : Measure (Fin n → ℝ))
      (ex122ProjectedSimplex n \ ex122ProjectedSimplexInterior n) = 0 := by
  have hcoords :
      (volume : Measure (Fin n → ℝ)) (⋃ i : Fin n, {y | y i = 0}) = 0 := by
    exact measure_iUnion_null fun i => ex122ProjectedCoord_zero_volume_zero i
  have hlast :
      (volume : Measure (Fin n → ℝ)) {y | ex122ProjectedLastCoord y = 0} = 0 :=
    ex122ProjectedLastCoord_zero_volume_zero n
  refine measure_mono_null ?_ (measure_union_null hcoords hlast)
  intro y hy
  rcases hy with ⟨hyClosed, hyNotInterior⟩
  by_cases hcoordpos : ∀ i, 0 < y i
  · right
    have hnotlast : ¬ 0 < ex122ProjectedLastCoord y := by
      intro hlastpos
      exact hyNotInterior ⟨hcoordpos, hlastpos⟩
    exact le_antisymm (not_lt.mp hnotlast) hyClosed.2
  · left
    push_neg at hcoordpos
    rcases hcoordpos with ⟨i, hi⟩
    exact Set.mem_iUnion.2
      ⟨i, le_antisymm hi (hyClosed.1 i)⟩

theorem ex122ProjectedSimplex_closed_imp_interior_ae (n : ℕ) :
    ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      y ∈ ex122ProjectedSimplex n → y ∈ ex122ProjectedSimplexInterior n := by
  rw [ae_iff]
  refine measure_mono_null ?_ (ex122ProjectedSimplex_diff_interior_volume_zero n)
  intro y hy
  by_cases hclosed : y ∈ ex122ProjectedSimplex n
  · exact ⟨hclosed, fun hinterior => hy (fun _ => hinterior)⟩
  · exact False.elim (hy fun h => False.elim (hclosed h))

/-- The projected coordinates and the reconstructed last coordinate add to one.
This is the algebraic core used by the projected simplex chart. -/
theorem ex122_sum_add_projectedLastCoord {n : ℕ} (y : Fin n → ℝ) :
    (∑ i, y i) + ex122ProjectedLastCoord y = 1 := by
  simp [ex122ProjectedLastCoord]

/-- The projected source chart preserves total mass:
`x_i = y_i s` and `x_last = (1 - ∑ y_i) s` have total `s`. -/
theorem ex122_projected_chart_total_mass {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
    (∑ i : Fin n, y i * s) + ex122ProjectedLastCoord y * s = s := by
  calc
    (∑ i : Fin n, y i * s) + ex122ProjectedLastCoord y * s =
        ((∑ i : Fin n, y i) + ex122ProjectedLastCoord y) * s := by
          rw [← Finset.sum_mul]
          ring
    _ = s := by
          rw [ex122_sum_add_projectedLastCoord y]
          ring

/-- The explicit projected chart has source total mass `s`. This is the
coordinate-level invariant needed by the arbitrary-`n`
change-of-variables/Jacobian route. -/
theorem ex122GammaTotal_projectedChart {n : ℕ} (y : Fin n → ℝ) (s : ℝ) :
    ex122GammaTotal (ex122ProjectedChart y s) = s := by
  simp [ex122GammaTotal, Fin.sum_univ_castSucc,
    ex122ProjectedChart_castSucc, ex122ProjectedChart_last,
    ex122_projected_chart_total_mass]

/-- Positivity of the first projected-chart coordinates on the open projected
simplex and positive total-mass fiber. This is the local branch condition for
the arbitrary-`n` Gamma pdf factorization. -/
theorem ex122ProjectedChart_castSucc_pos {n : ℕ} {y : Fin n → ℝ} {s : ℝ}
    (hy : ∀ i, 0 < y i) (hs : 0 < s) (i : Fin n) :
    0 < ex122ProjectedChart y s (Fin.castSucc i) := by
  rw [ex122ProjectedChart_castSucc]
  exact mul_pos (hy i) hs

/-- Positivity of the reconstructed final projected-chart coordinate. -/
theorem ex122ProjectedChart_last_pos {n : ℕ} {y : Fin n → ℝ} {s : ℝ}
    (hylast : 0 < ex122ProjectedLastCoord y) (hs : 0 < s) :
    0 < ex122ProjectedChart y s (Fin.last n) := by
  rw [ex122ProjectedChart_last]
  exact mul_pos hylast hs

/-- All coordinates of the arbitrary projected chart are positive on the open
projected simplex and positive total-mass fiber. -/
theorem ex122ProjectedChart_pos {n : ℕ} {y : Fin n → ℝ} {s : ℝ}
    (hy : ∀ i, 0 < y i) (hylast : 0 < ex122ProjectedLastCoord y)
    (hs : 0 < s) :
    ∀ i : Fin (n + 1), 0 < ex122ProjectedChart y s i := by
  intro i
  by_cases h : i = Fin.last n
  · subst i
    exact ex122ProjectedChart_last_pos hylast hs
  · rw [ex122ProjectedChart]
    simp [h, mul_pos (hy (Fin.castPred i h)) hs]

/-- Splitting a parameter sum into the projected coordinates and the final
coordinate. This is the exponent bookkeeping needed in the arbitrary-`n`
Gamma-to-Dirichlet density factorization. -/
theorem ex122_sum_alpha_castSucc_add_last {n : ℕ} (α : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, α (Fin.castSucc i)) + α (Fin.last n) =
      ∑ i : Fin (n + 1), α i := by
  exact (Fin.sum_univ_castSucc α).symm

/-- Product analogue of `ex122_sum_alpha_castSucc_add_last`, used for the
Gamma normalizing constants in the arbitrary-`n` projected density formula. -/
theorem ex122_prod_Gamma_castSucc_mul_last {n : ℕ} (α : Fin (n + 1) → ℝ) :
    (∏ i : Fin n, Real.Gamma (α (Fin.castSucc i))) *
        Real.Gamma (α (Fin.last n)) =
      ∏ i : Fin (n + 1), Real.Gamma (α i) := by
  exact (Fin.prod_univ_castSucc fun i => Real.Gamma (α i)).symm

theorem ex122_prod_Gamma_inv_castSucc_mul_last {n : ℕ}
    (α : Fin (n + 1) → ℝ) :
    (∏ i : Fin n, (Real.Gamma (α (Fin.castSucc i)))⁻¹) *
        (Real.Gamma (α (Fin.last n)))⁻¹ =
      (∏ i : Fin (n + 1), Real.Gamma (α i))⁻¹ := by
  simp [← ex122_prod_Gamma_castSucc_mul_last α, Finset.prod_inv_distrib,
    mul_comm]

/-- Splits the projected-coordinate rpow factors after substituting
`x_i = y_i s`. This is the reusable finite-product algebra behind the
arbitrary-`n` pointwise density factorization. -/
theorem ex122_prod_projected_mul_rpow_split {n : ℕ}
    (α : Fin n → ℝ) {y : Fin n → ℝ} {s : ℝ}
    (hy : ∀ i, 0 ≤ y i) (hs : 0 ≤ s) :
    (∏ i : Fin n, (y i * s) ^ (α i - 1)) =
      (∏ i : Fin n, (y i) ^ (α i - 1)) *
        (∏ i : Fin n, s ^ (α i - 1)) := by
  calc
    (∏ i : Fin n, (y i * s) ^ (α i - 1)) =
        ∏ i : Fin n, (y i) ^ (α i - 1) * s ^ (α i - 1) := by
          refine Finset.prod_congr rfl ?_
          intro i _
          exact Real.mul_rpow (hy i) hs
    _ = (∏ i : Fin n, (y i) ^ (α i - 1)) *
          (∏ i : Fin n, s ^ (α i - 1)) := by
        rw [Finset.prod_mul_distrib]

/-- The shifted shape exponents from the first projected coordinates, the
last coordinate, and the Jacobian dimension combine to the total Gamma shape
minus one. -/
theorem ex122_sum_alpha_sub_one_castSucc_add_last_add_dim {n : ℕ}
    (α : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (α (Fin.castSucc i) - 1)) +
        (α (Fin.last n) - 1) + n =
      (∑ i : Fin (n + 1), α i) - 1 := by
  have hsum := ex122_sum_alpha_castSucc_add_last α
  rw [Finset.sum_sub_distrib]
  simp
  linarith

theorem ex122_prod_univ_rpow_eq_rpow_sum {ι : Type*} [Fintype ι]
    {a : ℝ} (f : ι → ℝ) (ha : 0 < a) :
    (∏ i, a ^ f i) = a ^ (∑ i, f i) := by
  exact (Real.rpow_sum_of_pos ha f Finset.univ).symm

theorem ex122_rate_rpow_castSucc_mul_last {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ} (hβ : 0 < β) :
    (∏ i : Fin n, β⁻¹ ^ α (Fin.castSucc i)) *
        β⁻¹ ^ α (Fin.last n) =
      β⁻¹ ^ (∑ i : Fin (n + 1), α i) := by
  have hr : 0 < β⁻¹ := inv_pos.mpr hβ
  rw [ex122_prod_univ_rpow_eq_rpow_sum
    (fun i : Fin n => α (Fin.castSucc i)) hr]
  rw [← Real.rpow_add hr]
  rw [ex122_sum_alpha_castSucc_add_last α]

theorem ex122_jacobian_s_rpow_factor {n : ℕ}
    (α : Fin (n + 1) → ℝ) {s : ℝ} (hs : 0 < s) :
    s ^ n *
        ((∏ i : Fin n, s ^ (α (Fin.castSucc i) - 1)) *
          s ^ (α (Fin.last n) - 1)) =
      s ^ ((∑ i : Fin (n + 1), α i) - 1) := by
  rw [← Real.rpow_natCast s n]
  rw [ex122_prod_univ_rpow_eq_rpow_sum
    (fun i : Fin n => α (Fin.castSucc i) - 1) hs]
  have htail :
      s ^ (∑ i : Fin n, (α (Fin.castSucc i) - 1)) *
          s ^ (α (Fin.last n) - 1) =
        s ^ ((∑ i : Fin n, (α (Fin.castSucc i) - 1)) +
          (α (Fin.last n) - 1)) := by
    exact (Real.rpow_add hs
      (∑ i : Fin n, (α (Fin.castSucc i) - 1))
      (α (Fin.last n) - 1)).symm
  rw [htail]
  have hhead :
      s ^ (n : ℝ) *
          s ^ ((∑ i : Fin n, (α (Fin.castSucc i) - 1)) +
            (α (Fin.last n) - 1)) =
        s ^ ((n : ℝ) +
          ((∑ i : Fin n, (α (Fin.castSucc i) - 1)) +
            (α (Fin.last n) - 1))) := by
    exact (Real.rpow_add hs (n : ℝ)
      ((∑ i : Fin n, (α (Fin.castSucc i) - 1)) +
        (α (Fin.last n) - 1))).symm
  rw [hhead]
  congr 1
  have h :=
    ex122_sum_alpha_sub_one_castSucc_add_last_add_dim α
  linarith

theorem ex122_exp_projectedChart_factor {n : ℕ}
    (y : Fin n → ℝ) (β s : ℝ) :
    (∏ i : Fin n, Real.exp (-(β⁻¹ * (y i * s)))) *
        Real.exp (-(β⁻¹ * (ex122ProjectedLastCoord y * s))) =
      Real.exp (-(β⁻¹ * s)) := by
  rw [← Real.exp_sum]
  rw [← Real.exp_add]
  congr 1
  have htotal := ex122_projected_chart_total_mass y s
  have hneg :
      (∑ i : Fin n, -(β⁻¹ * (y i * s))) =
        - (∑ i : Fin n, β⁻¹ * (y i * s)) := by
    simp
  have hsum :
      (∑ i : Fin n, β⁻¹ * (y i * s)) =
        β⁻¹ * (∑ i : Fin n, y i * s) := by
    rw [Finset.mul_sum]
  rw [hneg, hsum]
  rw [← neg_add, ← mul_add, htotal]

/-- The ENNReal density corresponding to the displayed projected density
formula (1.4), including the source support restriction. -/
def ex122ProjectedDensityENNReal {n : ℕ} (α : Fin (n + 1) → ℝ)
    (y : Fin n → ℝ) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal
      (if y ∈ ex122ProjectedSimplex n then
        ex122DirichletProjectedDensity α y
      else 0)

/-- The law-level measure corresponding to the displayed projected density
formula (1.4), including the source support restriction. -/
def ex122ProjectedDensityMeasure {n : ℕ} (α : Fin (n + 1) → ℝ) :
    Measure (Fin n → ℝ) :=
  (volume : Measure (Fin n → ℝ)).withDensity
    (ex122ProjectedDensityENNReal α)

theorem ex122ProjectedDensityMeasure_formula {n : ℕ}
    (α : Fin (n + 1) → ℝ) :
    ex122ProjectedDensityMeasure α =
      (volume : Measure (Fin n → ℝ)).withDensity
        (ex122ProjectedDensityENNReal α) := rfl

theorem ex122ProjectedDensityENNReal_eq_DirichletPDF {n : ℕ}
    (α : Fin (n + 1) → ℝ) (y : Fin n → ℝ) :
    ex122ProjectedDensityENNReal α y = ENNReal.ofReal (DirichletPDF α y) := by
  classical
  by_cases hy : y ∈ ex122ProjectedSimplex n
  · have hyD : DirichletSimplex (n := n + 1) y := by
      simpa [ex122ProjectedSimplex, DirichletSimplex, ex122ProjectedLastCoord,
        simplexLastCoord, sub_eq_add_neg, sub_nonneg] using hy
    rw [ex122ProjectedDensityENNReal]
    simp [hy]
    rw [DirichletPDF_formula_on_simplex (n := n + 1) (hn := Nat.succ_pos n)
      (alpha := α) (x := y) hyD]
    apply congrArg ENNReal.ofReal
    simp only [ex122DirichletProjectedDensity, ex122DirichletNormalizer,
      ex122ProjectedLastCoord, dirichletNormalizer, simplexLastCoord]
    refine congrArg₂
      (fun p l => ((Real.Gamma (∑ i, α i) / ∏ i, Real.Gamma (α i)) * p) * l)
      ?_ ?_
    · refine Finset.prod_congr rfl ?_
      intro i _
      congr 2
    · congr 1
  · have hyD : ¬ DirichletSimplex (n := n + 1) y := by
      intro hD
      apply hy
      simpa [ex122ProjectedSimplex, DirichletSimplex, ex122ProjectedLastCoord,
        simplexLastCoord, sub_eq_add_neg, sub_nonneg] using hD
    rw [ex122ProjectedDensityENNReal]
    simp [hy]
    simp [DirichletPDF, hyD]

theorem ex122ProjectedDensityMeasure_eq_withDensity_DirichletPDF {n : ℕ}
    (α : Fin (n + 1) → ℝ) :
    ex122ProjectedDensityMeasure α =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun y => ENNReal.ofReal (DirichletPDF α y)) := by
  unfold ex122ProjectedDensityMeasure
  refine withDensity_congr_ae ?_
  exact Filter.Eventually.of_forall fun y =>
    ex122ProjectedDensityENNReal_eq_DirichletPDF α y

/-- Product of the one-dimensional Gamma pdfs for the independent source
Gamma vector. This is the density side of the joint Gamma product law. -/
def ex122GammaProductPDFReal {n : ℕ} (α : Fin n → ℝ) (β : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∏ i, ProbabilityTheory.gammaPDFReal (α i) β⁻¹ (x i)

theorem measurable_ex122GammaProductPDFReal {n : ℕ}
    (α : Fin n → ℝ) (β : ℝ) :
    Measurable (ex122GammaProductPDFReal α β) := by
  unfold ex122GammaProductPDFReal
  fun_prop

theorem ex122GammaProductPDFReal_nonneg {n : ℕ}
    {α : Fin n → ℝ} {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) (x : Fin n → ℝ) :
    0 ≤ ex122GammaProductPDFReal α β x := by
  unfold ex122GammaProductPDFReal
  exact Finset.prod_nonneg fun i _ =>
    ProbabilityTheory.gammaPDFReal_nonneg (hα i) (inv_pos.mpr hβ) (x i)

/-- The Gamma product pdf evaluated on the arbitrary projected chart splits
into the first projected coordinates and the reconstructed last coordinate.
This removes the `Fin (n + 1)` chart indexing from the remaining pointwise COV
integrand factorization. -/
theorem ex122GammaProductPDFReal_projectedChart {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) (y : Fin n → ℝ) (s : ℝ) :
    ex122GammaProductPDFReal α β (ex122ProjectedChart y s) =
      (∏ i : Fin n,
        ProbabilityTheory.gammaPDFReal (α (Fin.castSucc i)) β⁻¹ (y i * s)) *
      ProbabilityTheory.gammaPDFReal (α (Fin.last n)) β⁻¹
        (ex122ProjectedLastCoord y * s) := by
  unfold ex122GammaProductPDFReal
  rw [Fin.prod_univ_castSucc]
  simp [ex122ProjectedChart_castSucc, ex122ProjectedChart_last, mul_comm]

theorem ex122GammaProductPDFReal_projectedChart_gammaPDFReal_formula {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) {y : Fin n → ℝ} {s : ℝ}
    (hy : ∀ i, 0 < y i) (hylast : 0 < ex122ProjectedLastCoord y)
    (hs : 0 < s) :
    ex122GammaProductPDFReal α β (ex122ProjectedChart y s) =
      (∏ i : Fin n,
        β⁻¹ ^ α (Fin.castSucc i) / Real.Gamma (α (Fin.castSucc i)) *
          (y i * s) ^ (α (Fin.castSucc i) - 1) *
          Real.exp (-(β⁻¹ * (y i * s)))) *
      (β⁻¹ ^ α (Fin.last n) / Real.Gamma (α (Fin.last n)) *
        (ex122ProjectedLastCoord y * s) ^ (α (Fin.last n) - 1) *
        Real.exp (-(β⁻¹ * (ex122ProjectedLastCoord y * s)))) := by
  rw [ex122GammaProductPDFReal_projectedChart]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro i _
    rw [ProbabilityTheory.gammaPDFReal,
      if_pos (mul_pos (hy i) hs).le]
  · rw [ProbabilityTheory.gammaPDFReal,
      if_pos (mul_pos hylast hs).le]

theorem ex122ProjectedGammaCOVIntegrand_factorized {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ} {y : Fin n → ℝ} {s : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    (hy : ∀ i, 0 < y i) (hylast : 0 < ex122ProjectedLastCoord y)
    (hs : 0 < s) :
    s ^ n * ex122GammaProductPDFReal α β (ex122ProjectedChart y s) =
      ex122DirichletProjectedDensity α y *
        ProbabilityTheory.gammaPDFReal (∑ i : Fin (n + 1), α i) β⁻¹ s := by
  have hr : 0 < β⁻¹ := inv_pos.mpr hβ
  have hsum_pos : 0 < ∑ i : Fin (n + 1), α i := by
    have hne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := ⟨0, by simp⟩
    exact Finset.sum_pos (fun i _ => hα i) hne
  rw [ex122GammaProductPDFReal_projectedChart_gammaPDFReal_formula
    α β hy hylast hs]
  unfold ex122DirichletProjectedDensity ex122DirichletNormalizer
  rw [ProbabilityTheory.gammaPDFReal, if_pos hs.le]
  simp_rw [div_eq_mul_inv]
  simp_rw [Real.mul_rpow (le_of_lt (hy _)) (le_of_lt hs)]
  rw [Real.mul_rpow (le_of_lt hylast) (le_of_lt hs)]
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_mul_distrib]
  rw [← ex122_rate_rpow_castSucc_mul_last α hβ]
  rw [← ex122_prod_Gamma_inv_castSucc_mul_last α]
  rw [← ex122_jacobian_s_rpow_factor α hs]
  rw [← ex122_exp_projectedChart_factor y β s]
  field_simp [Real.Gamma_pos_of_pos hsum_pos]
  have hexp_arg :
      ∀ i : Fin n, -(β⁻¹ * (y i * s)) = -(s * β⁻¹ * y i) := by
    intro i
    ring
  try simp_rw [hexp_arg]
  ring_nf
  have hexp_arg_nf :
      ∀ i : Fin n, -(y i * s * β⁻¹) = -(s * β⁻¹ * y i) := by
    intro i
    ring
  simp_rw [hexp_arg_nf]
  rw [Finset.prod_mul_distrib]
  ring_nf

/-- The source COV integrand can be rewritten as the joint Gamma product pdf
on the explicit projected chart times the Jacobian factor `s ^ n`. -/
theorem ex122ProjectedGammaCOVIntegrand_eq_chart_productPDF {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) (y : Fin n → ℝ) (s : ℝ) :
    s ^ n *
        (∏ i : Fin n,
          ProbabilityTheory.gammaPDFReal (α (Fin.castSucc i)) β⁻¹ (y i * s)) *
        ProbabilityTheory.gammaPDFReal (α (Fin.last n)) β⁻¹
          (ex122ProjectedLastCoord y * s) =
      s ^ n * ex122GammaProductPDFReal α β (ex122ProjectedChart y s) := by
  rw [ex122GammaProductPDFReal_projectedChart]
  ring

/-- The joint Gamma product density measure expected from independence. -/
def ex122GammaProductDensityMeasure {n : ℕ} (α : Fin n → ℝ) (β : ℝ) :
    Measure (Fin n → ℝ) :=
  (volume : Measure (Fin n → ℝ)).withDensity
    (fun x => ENNReal.ofReal (ex122GammaProductPDFReal α β x))

theorem ex122GammaProductPDFReal_ennreal_eq_prod_gammaPDF {n : ℕ}
    (α : Fin n → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) (x : Fin n → ℝ) :
    ENNReal.ofReal (ex122GammaProductPDFReal α β x) =
      ∏ i, ProbabilityTheory.gammaPDF (α i) β⁻¹ (x i) := by
  unfold ex122GammaProductPDFReal ProbabilityTheory.gammaPDF
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact ProbabilityTheory.gammaPDFReal_nonneg (hα i) (inv_pos.mpr hβ) (x i)

theorem ex122GammaProductDensityMeasure_eq_withDensity_prod_gammaPDF {n : ℕ}
    (α : Fin n → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122GammaProductDensityMeasure α β =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ∏ i, ProbabilityTheory.gammaPDF (α i) β⁻¹ (x i)) := by
  unfold ex122GammaProductDensityMeasure
  refine withDensity_congr_ae ?_
  exact Filter.Eventually.of_forall fun x =>
    ex122GammaProductPDFReal_ennreal_eq_prod_gammaPDF α hα hβ x

theorem ex122_lintegral_fin_product_eq_product_lintegral {n : ℕ}
    (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    (∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) ∂(Measure.pi μ)) =
      ∏ i, ∫⁻ t, f i t ∂(μ i) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hrest :
          (∫⁻ x : Fin n → ℝ, ∏ i, f (Fin.succ i) (x i)
              ∂(Measure.pi (fun i : Fin n => μ (Fin.succ i)))) =
            ∏ i : Fin n, ∫⁻ t, f (Fin.succ i) t ∂(μ (Fin.succ i)) := by
        exact ih (fun i => μ (Fin.succ i)) (fun i => f (Fin.succ i))
          (fun i => hf (Fin.succ i))
      have hprod_meas :
          AEMeasurable (fun x : Fin n → ℝ => ∏ i, f (Fin.succ i) (x i))
            (Measure.pi (fun i : Fin n => μ (Fin.succ i))) := by
        have hraw : AEMeasurable
            (∏ i : Fin n, fun x : Fin n → ℝ => f (Fin.succ i) (x i))
            (Measure.pi (fun i : Fin n => μ (Fin.succ i))) := by
          exact Finset.aemeasurable_prod Finset.univ (fun i _ =>
            (hf (Fin.succ i)).comp_quasiMeasurePreserving
              (Measure.quasiMeasurePreserving_eval
                (fun i : Fin n => μ (Fin.succ i)) i))
        exact hraw.congr
          (Filter.Eventually.of_forall fun x => by simp [Finset.prod_apply])
      calc
        (∫⁻ x : Fin (n + 1) → ℝ, ∏ i, f i (x i) ∂(Measure.pi μ))
            = ∫⁻ z : ℝ × (Fin n → ℝ),
                f 0 z.1 * ∏ i : Fin n, f (Fin.succ i) (z.2 i)
                ∂((μ 0).prod
                  (Measure.pi (fun i : Fin n => μ (Fin.succ i)))) := by
              have hmp := ((measurePreserving_piFinSuccAbove μ 0).symm)
              rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
              refine lintegral_congr fun z => ?_
              simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
                Fin.prod_univ_succ, Fin.cons_succ, Fin.zero_succAbove]
        _ = (∫⁻ t, f 0 t ∂(μ 0)) *
              ∫⁻ x : Fin n → ℝ, ∏ i, f (Fin.succ i) (x i)
                ∂(Measure.pi (fun i : Fin n => μ (Fin.succ i))) := by
              rw [lintegral_prod_mul (μ := μ 0)
                (ν := Measure.pi (fun i : Fin n => μ (Fin.succ i)))
                (f := f 0)
                (g := fun x : Fin n → ℝ => ∏ i, f (Fin.succ i) (x i))
                (hf := hf 0) (hg := hprod_meas)]
        _ = ∏ i, ∫⁻ t, f i t ∂(μ i) := by
              rw [hrest, Fin.prod_univ_succ]

theorem ex122_pi_withDensity_eq_withDensity_product {n : ℕ}
    (f : Fin n → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i))] :
    Measure.pi (fun i : Fin n => (volume : Measure ℝ).withDensity (f i)) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq
    (μ := fun i : Fin n => (volume : Measure ℝ).withDensity (f i)) ?_
  intro s hs
  have hrect : MeasurableSet (Set.univ.pi s) :=
    MeasurableSet.pi Set.countable_univ fun i _ => hs i
  rw [withDensity_apply _ hrect]
  rw [← lintegral_indicator hrect]
  rw [volume_pi]
  calc
    (∫⁻ x : Fin n → ℝ,
        (Set.pi Set.univ s).indicator (fun x => ∏ i, f i (x i)) x
        ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)))
        = ∫⁻ x : Fin n → ℝ, ∏ i, (s i).indicator (f i) (x i)
          ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
            refine lintegral_congr fun x => ?_
            by_cases hx : x ∈ Set.pi Set.univ s
            · rw [Set.indicator_of_mem hx]
              apply Finset.prod_congr rfl
              intro i _
              exact (Set.indicator_of_mem (hx i trivial) (f i)).symm
            · rw [Set.indicator_of_notMem hx]
              have hzero : ∃ i, (s i).indicator (f i) (x i) = 0 := by
                by_contra hnot
                push_neg at hnot
                have hx' : x ∈ Set.pi Set.univ s := by
                  intro i _
                  by_contra hxis
                  exact hnot i (Set.indicator_of_notMem hxis (f i))
                exact hx hx'
              rcases hzero with ⟨i, hi⟩
              rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    _ = ∏ i, ∫⁻ t, (s i).indicator (f i) t ∂(volume : Measure ℝ) := by
            rw [ex122_lintegral_fin_product_eq_product_lintegral]
            intro i
            exact (hf i).aemeasurable.indicator (hs i)
    _ = ∏ i, ((volume : Measure ℝ).withDensity (f i)) (s i) := by
            congr with i
            rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

theorem ex122GammaProductLaw_eq_gammaProductDensityMeasure {n : ℕ}
    (α : Fin n → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122GammaProductLaw α β = ex122GammaProductDensityMeasure α β := by
  rw [ex122GammaProductDensityMeasure_eq_withDensity_prod_gammaPDF α hα hβ]
  unfold ex122GammaProductLaw ex122GammaScaleLaw ProbabilityTheory.gammaMeasure
  haveI : ∀ i, SigmaFinite
      ((volume : Measure ℝ).withDensity
        ((fun i : Fin n => ProbabilityTheory.gammaPDF (α i) β⁻¹) i)) := by
    intro i
    unfold ProbabilityTheory.gammaPDF
    infer_instance
  exact ex122_pi_withDensity_eq_withDensity_product
    (fun i : Fin n => ProbabilityTheory.gammaPDF (α i) β⁻¹)
    (fun i => by
      unfold ProbabilityTheory.gammaPDF
      exact (ProbabilityTheory.measurable_gammaPDFReal (α i) β⁻¹).ennreal_ofReal)

/-- Source-side total-mass integral obtained after the change of variables
`x_i = y_i s` for the first `n` coordinates and
`x_last = (1 - sum y_i) s`. The factor `s ^ n` is the Jacobian. -/
def ex122ProjectedGammaCOVDensity {n : ℕ} (α : Fin (n + 1) → ℝ)
    (β : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ),
    s ^ n *
      (∏ i : Fin n,
        ProbabilityTheory.gammaPDFReal (α (Fin.castSucc i)) β⁻¹ (y i * s)) *
      ProbabilityTheory.gammaPDFReal (α (Fin.last n)) β⁻¹
        (ex122ProjectedLastCoord y * s)

theorem ex122ProjectedGammaCOVDensity_source_integral {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) (y : Fin n → ℝ) :
    ex122ProjectedGammaCOVDensity α β y =
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ n *
          (∏ i : Fin n,
            ProbabilityTheory.gammaPDFReal (α (Fin.castSucc i)) β⁻¹ (y i * s)) *
          ProbabilityTheory.gammaPDFReal (α (Fin.last n)) β⁻¹
            (ex122ProjectedLastCoord y * s) := rfl

theorem ex122ProjectedGammaCOVDensity_source_integral_chart_productPDF
    {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ) (y : Fin n → ℝ) :
    ex122ProjectedGammaCOVDensity α β y =
      ∫ s in Set.Ioi (0 : ℝ),
        s ^ n * ex122GammaProductPDFReal α β (ex122ProjectedChart y s) := by
  rw [ex122ProjectedGammaCOVDensity_source_integral]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by
    exact ex122ProjectedGammaCOVIntegrand_eq_chart_productPDF α β y s

/-- ENNReal form of the COV density, with the same projected-simplex support
restriction as equation (1.4). -/
def ex122ProjectedCOVDensityENNReal {n : ℕ} (α : Fin (n + 1) → ℝ)
    (β : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal
      (if y ∈ ex122ProjectedSimplex n then
        ex122ProjectedGammaCOVDensity α β y
      else 0)

theorem ex122ProjectedCOVDensityENNReal_eq_zero_off_simplex {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) {y : Fin n → ℝ}
    (hy : y ∉ ex122ProjectedSimplex n) :
    ex122ProjectedCOVDensityENNReal α β y = 0 := by
  unfold ex122ProjectedCOVDensityENNReal
  simp [hy]

theorem ex122ProjectedCOVDensityENNReal_eq_ofReal_on_interior {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) {y : Fin n → ℝ}
    (hy : y ∈ ex122ProjectedSimplexInterior n) :
    ex122ProjectedCOVDensityENNReal α β y =
      ENNReal.ofReal (ex122ProjectedGammaCOVDensity α β y) := by
  have hyClosed : y ∈ ex122ProjectedSimplex n :=
    ex122ProjectedSimplexInterior_subset_simplex hy
  unfold ex122ProjectedCOVDensityENNReal
  simp [hyClosed]

theorem ex122_lintegral_projectedCOVDensity_eq_interior
    {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    (∫⁻ y in s, ex122ProjectedCOVDensityENNReal α β y
      ∂(volume : Measure (Fin n → ℝ))) =
    (∫⁻ y in s ∩ ex122ProjectedSimplexInterior n,
      ex122ProjectedCOVDensityENNReal α β y
        ∂(volume : Measure (Fin n → ℝ))) := by
  rw [← lintegral_indicator hs]
  rw [← lintegral_indicator
    (hs.inter (measurableSet_ex122ProjectedSimplexInterior n))]
  refine lintegral_congr_ae ?_
  filter_upwards [ex122ProjectedSimplex_closed_imp_interior_ae n] with y hInterior
  by_cases hys : y ∈ s
  · by_cases hyClosed : y ∈ ex122ProjectedSimplex n
    · have hyInterior : y ∈ ex122ProjectedSimplexInterior n :=
        hInterior hyClosed
      simp [Set.indicator_of_mem, hys, hyInterior]
    · have hzero :
          ex122ProjectedCOVDensityENNReal α β y = 0 :=
        ex122ProjectedCOVDensityENNReal_eq_zero_off_simplex α β hyClosed
      have hyNotInterior : y ∉ ex122ProjectedSimplexInterior n := by
        intro hyInterior
        exact hyClosed (ex122ProjectedSimplexInterior_subset_simplex hyInterior)
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hys,
        hyNotInterior, hzero]
  · simp [Set.indicator_of_notMem, hys]

/-- The projected measure produced by the normalized-Gamma change of variables
before evaluating the total-mass Gamma integral. -/
def ex122ProjectedCOVMeasure {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ) :
    Measure (Fin n → ℝ) :=
  (volume : Measure (Fin n → ℝ)).withDensity
    (ex122ProjectedCOVDensityENNReal α β)

/-- The lower-dimensional normalization map obtained by keeping the first `n`
coordinates of the normalized Gamma vector. -/
def ex122ProjectedNormalize {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => x (Fin.castSucc i) / ex122GammaTotal x

theorem measurable_ex122ProjectedNormalize {n : ℕ} :
    Measurable (ex122ProjectedNormalize : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by
  unfold ex122ProjectedNormalize ex122GammaTotal
  fun_prop

theorem ex122ProjectedDirichletLaw_eq_map_projectedNormalize {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) :
    ex122ProjectedDirichletLaw α β =
      Measure.map (ex122ProjectedNormalize : (Fin (n + 1) → ℝ) → Fin n → ℝ)
        (ex122GammaProductLaw α β) := by
  unfold ex122ProjectedDirichletLaw ex122DirichletLaw
  rw [Measure.map_map measurable_ex122ProjectFirst measurable_ex122NormalizedVector]
  rfl

theorem ex122ProjectedDirichletLaw_eq_map_projectedNormalize_density {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122ProjectedDirichletLaw α β =
      Measure.map (ex122ProjectedNormalize : (Fin (n + 1) → ℝ) → Fin n → ℝ)
        (ex122GammaProductDensityMeasure α β) := by
  rw [ex122ProjectedDirichletLaw_eq_map_projectedNormalize,
    ex122GammaProductLaw_eq_gammaProductDensityMeasure α hα hβ]

/-- The remaining measure-level COV/Jacobian identity, stated as concrete
preimage integrals over all measurable target sets. -/
def ex122ProjectedCOVLIntegralPreimageIdentity {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) : Prop :=
  ∀ s : Set (Fin n → ℝ), MeasurableSet s →
    (∫⁻ x in
        (ex122ProjectedNormalize :
            (Fin (n + 1) → ℝ) → Fin n → ℝ) ⁻¹' s,
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) =
    (∫⁻ y in s, ex122ProjectedCOVDensityENNReal α β y
        ∂(volume : Measure (Fin n → ℝ)))

/-- The local chart domain for the remaining arbitrary-dimensional projected
COV step: projected coordinates in a target set and positive total mass. -/
def ex122ProjectedPositiveChartDomain {n : ℕ}
    (s : Set (Fin n → ℝ)) : Set ((Fin n → ℝ) × ℝ) :=
  s ×ˢ Set.Ioi (0 : ℝ)

theorem measurableSet_ex122ProjectedPositiveChartDomain {n : ℕ}
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (ex122ProjectedPositiveChartDomain (n := n) s) := by
  exact hs.prod measurableSet_Ioi

theorem ex122ProjectedPositiveChartDomain_lintegral_eq_iterated
    {n : ℕ} {s : Set (Fin n → ℝ)}
    (g : ((Fin n → ℝ) × ℝ) → ℝ≥0∞)
    (hg : AEMeasurable g
      ((volume : Measure ((Fin n → ℝ) × ℝ)).restrict
        (ex122ProjectedPositiveChartDomain (n := n) s))) :
    (∫⁻ z in ex122ProjectedPositiveChartDomain (n := n) s,
      g z ∂(volume : Measure ((Fin n → ℝ) × ℝ))) =
    (∫⁻ y in s,
      ∫⁻ t in Set.Ioi (0 : ℝ), g (y, t)
        ∂(volume : Measure ℝ)
      ∂(volume : Measure (Fin n → ℝ))) := by
  rw [ex122ProjectedPositiveChartDomain, Measure.volume_eq_prod]
  exact MeasureTheory.setLIntegral_prod g
    (by simpa [ex122ProjectedPositiveChartDomain] using hg)

/-- Normalizing the explicit positive chart recovers the projected point when
the total-mass parameter is nonzero. -/
theorem ex122ProjectedNormalize_projectedChart {n : ℕ}
    (y : Fin n → ℝ) {t : ℝ} (ht : t ≠ 0) :
    ex122ProjectedNormalize (ex122ProjectedChart y t) = y := by
  ext i
  rw [ex122ProjectedNormalize, ex122GammaTotal_projectedChart,
    ex122ProjectedChart_castSucc]
  exact div_eq_of_eq_mul ht rfl

/-- Positive-total-mass version of `ex122ProjectedNormalize_projectedChart`. -/
theorem ex122ProjectedNormalize_projectedChart_of_pos {n : ℕ}
    (y : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ex122ProjectedNormalize (ex122ProjectedChart y t) = y :=
  ex122ProjectedNormalize_projectedChart y (ne_of_gt ht)

/-- The explicit chart has positive ambient coordinates on the open projected
simplex and positive total-mass fiber. -/
theorem ex122ProjectedChart_pos_of_mem_interior {n : ℕ}
    {y : Fin n → ℝ} {t : ℝ}
    (hy : y ∈ ex122ProjectedSimplexInterior n) (ht : 0 < t) :
    ∀ i : Fin (n + 1), 0 < ex122ProjectedChart y t i := by
  exact ex122ProjectedChart_pos hy.1 hy.2 ht

theorem measurableSet_ex122ProjectedPositivePreimage {n : ℕ}
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    MeasurableSet
      {x : Fin (n + 1) → ℝ |
        (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s} := by
  have hpos : MeasurableSet {x : Fin (n + 1) → ℝ | ∀ i, 0 < x i} := by
    simpa [Set.setOf_forall] using
      (MeasurableSet.iInter fun i : Fin (n + 1) =>
        (isOpen_lt continuous_const (continuous_apply i)).measurableSet)
  exact hpos.inter (hs.preimage measurable_ex122ProjectedNormalize)

/-- On target subsets of the open projected simplex, the positive chart lands
inside the positive normalized preimage of the target. -/
theorem ex122ProjectedPositiveChart_mapsTo_positivePreimage {n : ℕ}
    {s : Set (Fin n → ℝ)}
    (hs_sub : s ⊆ ex122ProjectedSimplexInterior n) :
    Set.MapsTo
      (fun z : (Fin n → ℝ) × ℝ => ex122ProjectedChart z.1 z.2)
      (ex122ProjectedPositiveChartDomain (n := n) s)
      {x : Fin (n + 1) → ℝ |
        (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s} := by
  intro z hz
  rcases hz with ⟨hzs, hzt⟩
  exact ⟨ex122ProjectedChart_pos_of_mem_interior (hs_sub hzs) hzt,
    by simpa [ex122ProjectedNormalize_projectedChart_of_pos z.1 hzt] using hzs⟩

/-- The positive chart is injective on any positive total-mass chart domain. -/
theorem ex122ProjectedPositiveChart_injOn {n : ℕ}
    (s : Set (Fin n → ℝ)) :
    Set.InjOn
      (fun z : (Fin n → ℝ) × ℝ => ex122ProjectedChart z.1 z.2)
      (ex122ProjectedPositiveChartDomain (n := n) s) := by
  intro z hz w hw hzw
  have hzpos : 0 < z.2 := hz.2
  have hwpos : 0 < w.2 := hw.2
  have hsecond : z.2 = w.2 := by
    calc
      z.2 = ex122GammaTotal (ex122ProjectedChart z.1 z.2) := by
        rw [ex122GammaTotal_projectedChart]
      _ = ex122GammaTotal (ex122ProjectedChart w.1 w.2) :=
        congrArg ex122GammaTotal hzw
      _ = w.2 := by
        rw [ex122GammaTotal_projectedChart]
  have hfirst : z.1 = w.1 := by
    calc
      z.1 = ex122ProjectedNormalize (ex122ProjectedChart z.1 z.2) := by
        rw [ex122ProjectedNormalize_projectedChart_of_pos z.1 hzpos]
      _ = ex122ProjectedNormalize (ex122ProjectedChart w.1 w.2) :=
        congrArg ex122ProjectedNormalize hzw
      _ = w.1 := by
        rw [ex122ProjectedNormalize_projectedChart_of_pos w.1 hwpos]
  exact Prod.ext hfirst hsecond

/-- A point with all positive ambient Gamma coordinates has positive total mass. -/
theorem ex122GammaTotal_pos_of_all_pos {n : ℕ}
    {x : Fin (n + 1) → ℝ} (hx : ∀ i, 0 < x i) :
    0 < ex122GammaTotal x := by
  unfold ex122GammaTotal
  exact Finset.sum_pos (fun i _ => hx i)
    ⟨Fin.last n, Finset.mem_univ (Fin.last n)⟩

/-- Projected normalization preserves positivity of the retained coordinates. -/
theorem ex122ProjectedNormalize_pos_of_all_pos {n : ℕ}
    {x : Fin (n + 1) → ℝ} (hx : ∀ i, 0 < x i) :
    ∀ i : Fin n, 0 < ex122ProjectedNormalize x i := by
  intro i
  exact div_pos (hx (Fin.castSucc i))
    (ex122GammaTotal_pos_of_all_pos hx)

/-- The reconstructed last projected coordinate of a normalized positive vector
is the last ambient coordinate divided by the total mass. -/
theorem ex122ProjectedLastCoord_projectedNormalize {n : ℕ}
    {x : Fin (n + 1) → ℝ} (htotal : ex122GammaTotal x ≠ 0) :
    ex122ProjectedLastCoord (ex122ProjectedNormalize x) =
      x (Fin.last n) / ex122GammaTotal x := by
  unfold ex122ProjectedLastCoord ex122ProjectedNormalize
  rw [← Finset.sum_div]
  have hsplit :
      (∑ i : Fin (n + 1), x i) =
        (∑ i : Fin n, x (Fin.castSucc i)) + x (Fin.last n) := by
    simpa using Fin.sum_univ_castSucc x
  have htotal_eq :
      ex122GammaTotal x =
        (∑ i : Fin n, x (Fin.castSucc i)) + x (Fin.last n) := by
    simpa [ex122GammaTotal] using hsplit
  field_simp [htotal, htotal_eq]
  linarith

/-- Positive ambient coordinates normalize into the open projected simplex. -/
theorem ex122ProjectedNormalize_mem_interior_of_all_pos {n : ℕ}
    {x : Fin (n + 1) → ℝ} (hx : ∀ i, 0 < x i) :
    ex122ProjectedNormalize x ∈ ex122ProjectedSimplexInterior n := by
  refine ⟨ex122ProjectedNormalize_pos_of_all_pos hx, ?_⟩
  rw [ex122ProjectedLastCoord_projectedNormalize
    (ne_of_gt (ex122GammaTotal_pos_of_all_pos hx))]
  exact div_pos (hx (Fin.last n))
    (ex122GammaTotal_pos_of_all_pos hx)

/-- Normalization plus total mass is the inverse of the positive projected chart
on nonzero-total ambient points. -/
theorem ex122ProjectedChart_projectedNormalize_gammaTotal {n : ℕ}
    {x : Fin (n + 1) → ℝ} (htotal : ex122GammaTotal x ≠ 0) :
    ex122ProjectedChart (ex122ProjectedNormalize x) (ex122GammaTotal x) = x := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [ex122ProjectedChart_castSucc, ex122ProjectedNormalize]
    field_simp [htotal]
  · rw [ex122ProjectedChart_last,
      ex122ProjectedLastCoord_projectedNormalize htotal]
    field_simp [htotal]

/-- On target subsets of the open projected simplex, the positive chart image is
exactly the positive ambient preimage of the projected-normalization map. -/
theorem ex122ProjectedPositiveChart_image_positivePreimage {n : ℕ}
    {s : Set (Fin n → ℝ)}
    (hs_sub : s ⊆ ex122ProjectedSimplexInterior n) :
    (fun z : (Fin n → ℝ) × ℝ => ex122ProjectedChart z.1 z.2) ''
        ex122ProjectedPositiveChartDomain (n := n) s =
      {x : Fin (n + 1) → ℝ |
        (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s} := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ex122ProjectedPositiveChart_mapsTo_positivePreimage hs_sub hz
  · intro x hx
    refine ⟨(ex122ProjectedNormalize x, ex122GammaTotal x), ?_, ?_⟩
    · exact ⟨hx.2, ex122GammaTotal_pos_of_all_pos hx.1⟩
    · simpa using
        ex122ProjectedChart_projectedNormalize_gammaTotal
          (ne_of_gt (ex122GammaTotal_pos_of_all_pos hx.1))

/-- Coordinate split from projected coordinates plus total mass to the ambient
Gamma-product coordinate space. This is only a measure-preserving coordinate
bridge; the nonlinear Jacobian step is still carried by the chart map itself. -/
noncomputable def ex122ProdChartToPi (n : ℕ) :
    ((Fin n → ℝ) × ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
  MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm)

theorem ex122ProdChartToPi_measurePreserving (n : ℕ) :
    MeasurePreserving (ex122ProdChartToPi n) := by
  unfold ex122ProdChartToPi
  exact
    (Measure.measurePreserving_swap
      (μ := (volume : Measure (Fin n → ℝ)))
      (ν := (volume : Measure ℝ))).trans
      ((volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm)

@[simp] theorem ex122ProdChartToPi_castSucc {n : ℕ}
    (z : (Fin n → ℝ) × ℝ) (i : Fin n) :
    ex122ProdChartToPi n z (Fin.castSucc i) = z.1 i := by
  simp [ex122ProdChartToPi, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]
  change z.1 i = z.1 i
  rfl

@[simp] theorem ex122ProdChartToPi_last {n : ℕ}
    (z : (Fin n → ℝ) × ℝ) :
    ex122ProdChartToPi n z (Fin.last n) = z.2 := by
  simp [ex122ProdChartToPi, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]
  change z.2 = z.2
  rfl

/-- Euclidean-space version of `ex122ProdChartToPi`, matching the domain shape
expected by Mathlib's finite-dimensional Jacobian theorem. -/
noncomputable def ex122ProdChartToEuclidean (n : ℕ) :
    ((Fin n → ℝ) × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
  (ex122ProdChartToPi n).trans
    (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))

theorem ex122ProdChartToEuclidean_measurePreserving (n : ℕ) :
    MeasurePreserving (ex122ProdChartToEuclidean n) := by
  have hp : MeasurePreserving (ex122ProdChartToPi n) :=
    ex122ProdChartToPi_measurePreserving n
  have ht :
      MeasurePreserving
        (⇑(MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))) := by
    rw [MeasurableEquiv.coe_toLp 2 (Fin (n + 1) → ℝ)]
    exact PiLp.volume_preserving_toLp (Fin (n + 1))
  unfold ex122ProdChartToEuclidean
  exact hp.trans ht

/-- Same-space scaling part of the projected chart. The full ambient chart is
this nonlinear scaling followed by the linear completion of the last coordinate. -/
def ex122ProjectedScaleTotalMap {n : ℕ} :
    ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ :=
  fun p => (fun i => p.1 i * p.2, p.2)

theorem measurable_ex122ProjectedScaleTotalMap {n : ℕ} :
    Measurable (ex122ProjectedScaleTotalMap :
      ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) := by
  unfold ex122ProjectedScaleTotalMap
  fun_prop

theorem differentiable_ex122ProjectedScaleTotalMap {n : ℕ} :
    Differentiable ℝ
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) := by
  unfold ex122ProjectedScaleTotalMap
  fun_prop

theorem ex122ProjectedScaleTotalMap_hasFDerivWithinAt
    {n : ℕ} (s : Set ((Fin n → ℝ) × ℝ))
    (p : (Fin n → ℝ) × ℝ) :
    HasFDerivWithinAt
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ)
      (fderiv ℝ
        (ex122ProjectedScaleTotalMap :
          ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) p)
      s p := by
  exact
    (differentiable_ex122ProjectedScaleTotalMap.differentiableAt.hasFDerivAt).hasFDerivWithinAt

instance ex122ProjectedScaleTotalProductVolume_isAddHaar {n : ℕ} :
    Measure.IsAddHaarMeasure
      (volume : Measure ((Fin n → ℝ) × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Diagonal part of the derivative of `(y, t) ↦ (t • y, t)`. -/
def ex122ProjectedScaleTotalDiagonalLinearMap {n : ℕ} (t : ℝ) :
    ((Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) × ℝ :=
  LinearMap.prodMap
    (t • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

theorem ex122ProjectedScaleTotalDiagonalLinearMap_det
    {n : ℕ} (t : ℝ) :
    (ex122ProjectedScaleTotalDiagonalLinearMap (n := n) t).det = t ^ n := by
  unfold ex122ProjectedScaleTotalDiagonalLinearMap
  rw [LinearMap.det_prodMap]
  rw [LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id]
  simp [Fintype.card_fin]

/-- Shear part of the derivative of `(y, t) ↦ (t • y, t)`. -/
def ex122ProjectedScaleTotalShearLinearMap {n : ℕ} (y : Fin n → ℝ) :
    ((Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) × ℝ :=
  LinearMap.transvection
    (LinearMap.snd ℝ (Fin n → ℝ) ℝ)
    (y, 0)

theorem ex122ProjectedScaleTotalShearLinearMap_apply
    {n : ℕ} (y : Fin n → ℝ)
    (q : (Fin n → ℝ) × ℝ) :
    ex122ProjectedScaleTotalShearLinearMap y q = (q.1 + q.2 • y, q.2) := by
  ext i <;> simp [ex122ProjectedScaleTotalShearLinearMap, LinearMap.transvection.apply]

theorem ex122ProjectedScaleTotalShearLinearMap_det
    {n : ℕ} (y : Fin n → ℝ) :
    (ex122ProjectedScaleTotalShearLinearMap y).det = 1 := by
  unfold ex122ProjectedScaleTotalShearLinearMap
  rw [LinearMap.transvection.det]
  simp

/-- Explicit derivative of the same-space scaling chart. -/
def ex122ProjectedScaleTotalFDerivLinearMap {n : ℕ}
    (p : (Fin n → ℝ) × ℝ) :
    ((Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) × ℝ :=
  (ex122ProjectedScaleTotalShearLinearMap p.1).comp
    (ex122ProjectedScaleTotalDiagonalLinearMap p.2)

theorem ex122ProjectedScaleTotalFDerivLinearMap_apply
    {n : ℕ} (p q : (Fin n → ℝ) × ℝ) :
    ex122ProjectedScaleTotalFDerivLinearMap p q =
      (fun i => p.2 * q.1 i + q.2 * p.1 i, q.2) := by
  ext i <;>
    simp [ex122ProjectedScaleTotalFDerivLinearMap,
      ex122ProjectedScaleTotalShearLinearMap_apply,
      ex122ProjectedScaleTotalDiagonalLinearMap]

theorem ex122ProjectedScaleTotalFDerivLinearMap_det
    {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    (ex122ProjectedScaleTotalFDerivLinearMap p).det = p.2 ^ n := by
  unfold ex122ProjectedScaleTotalFDerivLinearMap
  rw [LinearMap.det_comp]
  rw [ex122ProjectedScaleTotalShearLinearMap_det,
    ex122ProjectedScaleTotalDiagonalLinearMap_det]
  simp

theorem ex122ProjectedScaleTotalFDerivLinearMap_toContinuousLinearMap_eq
    {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    LinearMap.toContinuousLinearMap (ex122ProjectedScaleTotalFDerivLinearMap p) =
      (p.2 • (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ) +
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight p.1).prod
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ) := by
  ext q i <;>
    simp [ex122ProjectedScaleTotalFDerivLinearMap_apply]

theorem ex122ProjectedScaleTotalMap_hasFDerivAt_explicit
    {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    HasFDerivAt
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ)
      (LinearMap.toContinuousLinearMap
        (ex122ProjectedScaleTotalFDerivLinearMap p))
      p := by
  rw [ex122ProjectedScaleTotalFDerivLinearMap_toContinuousLinearMap_eq]
  have hfirst :
      HasFDerivAt
        (fun q : (Fin n → ℝ) × ℝ => q.2 • q.1)
        (p.2 • (ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ) +
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).smulRight p.1)
        p :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).smul
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hsecond :
      HasFDerivAt
        (fun q : (Fin n → ℝ) × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ)
        p :=
    hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  convert hfirst.prodMk hsecond using 1
  apply funext
  intro q
  apply Prod.ext
  · funext i
    simp [ex122ProjectedScaleTotalMap, smul_eq_mul, mul_comm]
  · simp [ex122ProjectedScaleTotalMap]

theorem ex122ProjectedScaleTotalMap_fderiv_eq
    {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    fderiv ℝ
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ)
      p =
      LinearMap.toContinuousLinearMap
        (ex122ProjectedScaleTotalFDerivLinearMap p) := by
  exact (ex122ProjectedScaleTotalMap_hasFDerivAt_explicit p).fderiv

theorem ex122ProjectedScaleTotalMap_fderiv_det
    {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    (fderiv ℝ
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ)
      p).det = p.2 ^ n := by
  rw [ex122ProjectedScaleTotalMap_fderiv_eq]
  simp [ex122ProjectedScaleTotalFDerivLinearMap_det]

theorem ex122ProjectedScaleTotalMap_injOn_positiveTotal {n : ℕ} :
    Set.InjOn
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ)
      {p : (Fin n → ℝ) × ℝ | 0 < p.2} := by
  intro p hp q hq hpq
  have ht_eq : p.2 = q.2 := by
    simpa [ex122ProjectedScaleTotalMap] using congrArg Prod.snd hpq
  have hy_eq : p.1 = q.1 := by
    funext i
    have hcoord := congrFun (congrArg Prod.fst hpq) i
    simp [ex122ProjectedScaleTotalMap] at hcoord
    have ht_ne : p.2 ≠ 0 := hp.ne'
    rw [← ht_eq] at hcoord
    calc
      p.1 i = (p.1 i * p.2) / p.2 := by field_simp [ht_ne]
      _ = (q.1 i * p.2) / p.2 := by rw [hcoord]
      _ = q.1 i := by field_simp [ht_ne]
  exact Prod.ext hy_eq ht_eq

theorem ex122ProjectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_fderiv_mul
    {n : ℕ} {s : Set ((Fin n → ℝ) × ℝ)} (hs : MeasurableSet s)
    (hinj : Set.InjOn
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) s)
    (g : ((Fin n → ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (ex122ProjectedScaleTotalMap :
          ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) '' s,
        g y =
      ∫⁻ p in s,
        ENNReal.ofReal
          |(fderiv ℝ
            (ex122ProjectedScaleTotalMap :
              ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) p).det| *
          g (ex122ProjectedScaleTotalMap p) := by
  exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure ((Fin n → ℝ) × ℝ)) hs
    (fun p _ => ex122ProjectedScaleTotalMap_hasFDerivWithinAt s p) hinj g

theorem ex122ProjectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_totalPow_mul
    {n : ℕ} {s : Set ((Fin n → ℝ) × ℝ)} (hs : MeasurableSet s)
    (hinj : Set.InjOn
      (ex122ProjectedScaleTotalMap :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) s)
    (g : ((Fin n → ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (ex122ProjectedScaleTotalMap :
          ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) '' s,
        g y =
      ∫⁻ p in s,
        ENNReal.ofReal |p.2 ^ n| *
          g (ex122ProjectedScaleTotalMap p) := by
  rw [ex122ProjectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_fderiv_mul
    hs hinj g]
  exact setLIntegral_congr_fun hs fun p _ => by
    rw [ex122ProjectedScaleTotalMap_fderiv_det]

theorem ex122ProjectedScaleTotalMap_lintegral_image_eq_lintegral_totalPow_mul_of_subset_positive
    {n : ℕ} {s : Set ((Fin n → ℝ) × ℝ)} (hs : MeasurableSet s)
    (hpos : s ⊆ {p : (Fin n → ℝ) × ℝ | 0 < p.2})
    (g : ((Fin n → ℝ) × ℝ) → ℝ≥0∞) :
    ∫⁻ y in
        (ex122ProjectedScaleTotalMap :
          ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) '' s,
        g y =
      ∫⁻ p in s,
        ENNReal.ofReal (p.2 ^ n) *
          g (ex122ProjectedScaleTotalMap p) := by
  have hinj :
      Set.InjOn
        (ex122ProjectedScaleTotalMap :
          ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) s :=
    ex122ProjectedScaleTotalMap_injOn_positiveTotal.mono hpos
  rw [ex122ProjectedScaleTotalMap_lintegral_image_eq_lintegral_abs_det_totalPow_mul
    hs hinj g]
  exact setLIntegral_congr_fun hs fun p hp => by
    have hpow_nonneg : 0 ≤ p.2 ^ n :=
      pow_nonneg (le_of_lt (hpos hp)) _
    rw [abs_of_nonneg hpow_nonneg]

/-- Linear functional summing the first projected coordinates. -/
def ex122ProjectedFirstCoordSumLinearMap {n : ℕ} :
    ((Fin n → ℝ) × ℝ) →ₗ[ℝ] ℝ where
  toFun p := ∑ i : Fin n, p.1 i
  map_add' p q := by
    simp [Finset.sum_add_distrib]
  map_smul' c p := by
    simp [← Finset.mul_sum]

/-- Determinant-one shear converting total mass to the completed last
coordinate: `(u, t) ↦ (u, t - ∑ u_i)`. -/
def ex122ProjectedCompletionShearLinearMap {n : ℕ} :
    ((Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin n → ℝ) × ℝ :=
  LinearMap.transvection
    (ex122ProjectedFirstCoordSumLinearMap (n := n))
    (0, -1)

theorem ex122ProjectedCompletionShearLinearMap_apply
    {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    ex122ProjectedCompletionShearLinearMap p =
      (p.1, p.2 - ∑ i : Fin n, p.1 i) := by
  apply Prod.ext
  · funext i
    simp [ex122ProjectedCompletionShearLinearMap,
      ex122ProjectedFirstCoordSumLinearMap, LinearMap.transvection.apply]
  · simp [ex122ProjectedCompletionShearLinearMap,
      ex122ProjectedFirstCoordSumLinearMap, LinearMap.transvection.apply]
    ring

theorem ex122ProjectedCompletionShearLinearMap_det
    {n : ℕ} :
    (ex122ProjectedCompletionShearLinearMap (n := n)).det = 1 := by
  unfold ex122ProjectedCompletionShearLinearMap
  rw [LinearMap.transvection.det]
  change 1 + (∑ i : Fin n, (0 : Fin n → ℝ) i) = 1
  simp

theorem ex122ProjectedCompletionShearLinearMap_measurePreserving
    {n : ℕ} :
    MeasurePreserving
      (ex122ProjectedCompletionShearLinearMap (n := n) :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) := by
  have hdet_ne :
      (ex122ProjectedCompletionShearLinearMap (n := n)).det ≠ 0 := by
    rw [ex122ProjectedCompletionShearLinearMap_det]
    norm_num
  haveI : Measure.IsAddHaarMeasure (volume : Measure ((Fin n → ℝ) × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  refine
    ⟨(ex122ProjectedCompletionShearLinearMap (n := n)).continuous_of_finiteDimensional.measurable,
      ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure ((Fin n → ℝ) × ℝ)) hdet_ne]
  rw [ex122ProjectedCompletionShearLinearMap_det]
  simp

/-- Linear completion from scaled projected coordinates and total mass to the
ambient Gamma-product coordinates. -/
def ex122ProjectedLinearCompletionMap {n : ℕ} :
    ((Fin n → ℝ) × ℝ) → Fin (n + 1) → ℝ :=
  fun p => ex122ProdChartToPi n (ex122ProjectedCompletionShearLinearMap p)

theorem ex122ProjectedLinearCompletionMap_measurePreserving {n : ℕ} :
    MeasurePreserving
      (ex122ProjectedLinearCompletionMap :
        ((Fin n → ℝ) × ℝ) → Fin (n + 1) → ℝ) := by
  unfold ex122ProjectedLinearCompletionMap
  exact (ex122ProdChartToPi_measurePreserving n).comp
    (ex122ProjectedCompletionShearLinearMap_measurePreserving (n := n))

/-- The determinant-one shear is a measurable embedding, since it is a finite
dimensional linear equivalence. -/
theorem ex122ProjectedCompletionShearLinearMap_measurableEmbedding
    {n : ℕ} :
    MeasurableEmbedding
      (ex122ProjectedCompletionShearLinearMap (n := n) :
        ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) := by
  have hdet_ne :
      (ex122ProjectedCompletionShearLinearMap (n := n)).det ≠ 0 := by
    rw [ex122ProjectedCompletionShearLinearMap_det]
    norm_num
  let e :=
    (ex122ProjectedCompletionShearLinearMap (n := n)).equivOfDetNeZero hdet_ne
  simpa [e, LinearEquiv.coe_toContinuousLinearEquiv'] using
    e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding

/-- The linear completion map is a measurable embedding. -/
theorem ex122ProjectedLinearCompletionMap_measurableEmbedding {n : ℕ} :
    MeasurableEmbedding
      (ex122ProjectedLinearCompletionMap :
        ((Fin n → ℝ) × ℝ) → Fin (n + 1) → ℝ) := by
  unfold ex122ProjectedLinearCompletionMap
  exact (ex122ProdChartToPi n).measurableEmbedding.comp
    (ex122ProjectedCompletionShearLinearMap_measurableEmbedding (n := n))

@[simp] theorem ex122ProjectedLinearCompletionMap_castSucc {n : ℕ}
    (p : (Fin n → ℝ) × ℝ) (i : Fin n) :
    ex122ProjectedLinearCompletionMap p (Fin.castSucc i) = p.1 i := by
  simp [ex122ProjectedLinearCompletionMap,
    ex122ProjectedCompletionShearLinearMap_apply]

@[simp] theorem ex122ProjectedLinearCompletionMap_last {n : ℕ}
    (p : (Fin n → ℝ) × ℝ) :
    ex122ProjectedLinearCompletionMap p (Fin.last n) =
      p.2 - ∑ i : Fin n, p.1 i := by
  simp [ex122ProjectedLinearCompletionMap,
    ex122ProjectedCompletionShearLinearMap_apply]

theorem ex122ProjectedChart_eq_linearCompletion_comp_scale {n : ℕ}
    (p : (Fin n → ℝ) × ℝ) :
    ex122ProjectedChart p.1 p.2 =
      ex122ProjectedLinearCompletionMap
        (ex122ProjectedScaleTotalMap p) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [ex122ProjectedScaleTotalMap, ex122ProjectedChart_castSucc]
  · simp [ex122ProjectedScaleTotalMap, ex122ProjectedChart_last,
      ex122ProjectedLastCoord]
    have hsum :
        (∑ i : Fin n, p.1 i * p.2) =
          (∑ i : Fin n, p.1 i) * p.2 := by
      simpa using
        (Finset.sum_mul (s := Finset.univ) (f := fun i : Fin n => p.1 i)
          (a := p.2)).symm
    rw [hsum]
    ring

/-- The explicit positive chart image is the linear-completion image of the
same-space scaling image. -/
theorem ex122ProjectedPositiveChart_image_eq_linearCompletion_scale_image
    {n : ℕ} (s : Set (Fin n → ℝ)) :
    (fun z : (Fin n → ℝ) × ℝ => ex122ProjectedChart z.1 z.2) ''
        ex122ProjectedPositiveChartDomain (n := n) s =
      (ex122ProjectedLinearCompletionMap :
          ((Fin n → ℝ) × ℝ) → Fin (n + 1) → ℝ) ''
        ((ex122ProjectedScaleTotalMap :
            ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) ''
          ex122ProjectedPositiveChartDomain (n := n) s) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨ex122ProjectedScaleTotalMap z, ⟨z, hz, rfl⟩,
      (ex122ProjectedChart_eq_linearCompletion_comp_scale z).symm⟩
  · intro x hx
    rcases hx with ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, ex122ProjectedChart_eq_linearCompletion_comp_scale z⟩

/-- Smaller named arbitrary-dimensional blocker. It isolates the nonlinear
Jacobian theorem still needed for `ex122ProjectedCOVLIntegralPreimageIdentity`:
on the open projected simplex and positive total-mass fiber, the normalized
preimage integral should equal the integral over the explicit chart with
Jacobian factor `t ^ n`. Boundary and support reductions are separate from this
local chart statement. -/
def ex122ProjectedPositiveChartLIntegralIdentity {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) : Prop :=
  ∀ s : Set (Fin n → ℝ), MeasurableSet s →
    s ⊆ ex122ProjectedSimplexInterior n →
    (∫⁻ x in
        {x : Fin (n + 1) → ℝ |
          (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s},
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) =
    (∫⁻ z in ex122ProjectedPositiveChartDomain s,
      ENNReal.ofReal
        (z.2 ^ n *
          ex122GammaProductPDFReal α β (ex122ProjectedChart z.1 z.2))
        ∂(volume : Measure ((Fin n → ℝ) × ℝ)))

/-- The local positive-chart Jacobian identity follows by decomposing the chart
into the same-space scaling map, whose determinant is `t ^ n`, followed by the
measure-preserving linear completion map. -/
theorem ex122ProjectedPositiveChartLIntegralIdentity_proved {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) :
    ex122ProjectedPositiveChartLIntegralIdentity α β := by
  intro s hs hs_sub
  let D : Set ((Fin n → ℝ) × ℝ) :=
    ex122ProjectedPositiveChartDomain (n := n) s
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (ex122GammaProductPDFReal α β x)
  let scaleImage : Set ((Fin n → ℝ) × ℝ) :=
    (ex122ProjectedScaleTotalMap :
      ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ) '' D
  have hD_meas : MeasurableSet D := by
    exact measurableSet_ex122ProjectedPositiveChartDomain hs
  have hD_pos : D ⊆ {p : (Fin n → ℝ) × ℝ | 0 < p.2} := by
    intro p hp
    exact hp.2
  calc
    (∫⁻ x in
        {x : Fin (n + 1) → ℝ |
          (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s},
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) =
      ∫⁻ x in
        (fun z : (Fin n → ℝ) × ℝ => ex122ProjectedChart z.1 z.2) '' D,
        F x ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
        rw [ex122ProjectedPositiveChart_image_positivePreimage hs_sub]
    _ =
      ∫⁻ x in
        (ex122ProjectedLinearCompletionMap :
          ((Fin n → ℝ) × ℝ) → Fin (n + 1) → ℝ) '' scaleImage,
        F x ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
        rw [ex122ProjectedPositiveChart_image_eq_linearCompletion_scale_image
          (n := n) s]
    _ =
      ∫⁻ z in scaleImage,
        F (ex122ProjectedLinearCompletionMap z)
          ∂(volume : Measure ((Fin n → ℝ) × ℝ)) := by
        exact
          (MeasureTheory.MeasurePreserving.setLIntegral_comp_emb
            (ex122ProjectedLinearCompletionMap_measurePreserving (n := n))
            (ex122ProjectedLinearCompletionMap_measurableEmbedding (n := n))
            F scaleImage).symm
    _ =
      ∫⁻ z in D,
        ENNReal.ofReal (z.2 ^ n) *
          F (ex122ProjectedLinearCompletionMap
            (ex122ProjectedScaleTotalMap z))
          ∂(volume : Measure ((Fin n → ℝ) × ℝ)) := by
        exact
          ex122ProjectedScaleTotalMap_lintegral_image_eq_lintegral_totalPow_mul_of_subset_positive
            hD_meas hD_pos
            (fun z => F (ex122ProjectedLinearCompletionMap z))
    _ =
      ∫⁻ z in ex122ProjectedPositiveChartDomain s,
        ENNReal.ofReal
          (z.2 ^ n *
            ex122GammaProductPDFReal α β (ex122ProjectedChart z.1 z.2))
          ∂(volume : Measure ((Fin n → ℝ) × ℝ)) := by
        refine setLIntegral_congr_fun hD_meas ?_
        intro z hz
        have hpow_nonneg : 0 ≤ z.2 ^ n :=
          pow_nonneg (le_of_lt (hD_pos hz)) n
        have hcomp :
            ex122ProjectedLinearCompletionMap
                (ex122ProjectedScaleTotalMap z) =
              ex122ProjectedChart z.1 z.2 :=
          (ex122ProjectedChart_eq_linearCompletion_comp_scale z).symm
        calc
          ENNReal.ofReal (z.2 ^ n) *
              F (ex122ProjectedLinearCompletionMap
                (ex122ProjectedScaleTotalMap z))
              = ENNReal.ofReal (z.2 ^ n) *
                  F (ex122ProjectedChart z.1 z.2) := by
                rw [hcomp]
          _ = ENNReal.ofReal
                (z.2 ^ n *
                  ex122GammaProductPDFReal α β
                    (ex122ProjectedChart z.1 z.2)) := by
                dsimp [F]
                exact (ENNReal.ofReal_mul hpow_nonneg).symm

theorem ex122ProjectedNormalize_preimage_lintegral_support_reduce {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    (∫⁻ x in
        (ex122ProjectedNormalize :
          (Fin (n + 1) → ℝ) → Fin n → ℝ) ⁻¹' s,
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) =
    (∫⁻ x in
        {x : Fin (n + 1) → ℝ |
          (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s},
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) := by
  have hae :
      ((ex122ProjectedNormalize :
          (Fin (n + 1) → ℝ) → Fin n → ℝ) ⁻¹' s)
        =ᵐ[ex122GammaProductLaw α β]
      {x : Fin (n + 1) → ℝ |
        (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s} := by
    filter_upwards
      [ex122GammaProductLaw_coordinates_positive_ae α hα hβ] with x hx
    exact propext
      ⟨fun hxmem => ⟨hx, hxmem⟩,
        fun hxmem => hxmem.2⟩
  have hmeasure :
      ex122GammaProductLaw α β
          ((ex122ProjectedNormalize :
            (Fin (n + 1) → ℝ) → Fin n → ℝ) ⁻¹' s) =
      ex122GammaProductLaw α β
          {x : Fin (n + 1) → ℝ |
            (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s} := by
    exact measure_congr hae
  rw [ex122GammaProductLaw_eq_gammaProductDensityMeasure α hα hβ] at hmeasure
  unfold ex122GammaProductDensityMeasure at hmeasure
  rw [withDensity_apply _
        (hs.preimage measurable_ex122ProjectedNormalize),
      withDensity_apply _
        (measurableSet_ex122ProjectedPositivePreimage hs)] at hmeasure
  exact hmeasure

theorem ofReal_ex122ProjectedGammaCOVDensity_eq_lintegral_source_integral_ae_restrict
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      y ∈ s ∩ ex122ProjectedSimplexInterior n →
        ENNReal.ofReal (ex122ProjectedGammaCOVDensity α β y) =
          ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal
              (t ^ n *
                ex122GammaProductPDFReal α β
                  (ex122ProjectedChart y t)) := by
  let A : Set (Fin n → ℝ) := s ∩ ex122ProjectedSimplexInterior n
  let inner : (Fin n → ℝ) → ℝ≥0∞ := fun y =>
    ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal
        (t ^ n *
          ex122GammaProductPDFReal α β
            (ex122ProjectedChart y t))
  have hA : MeasurableSet A := by
    exact hs.inter (measurableSet_ex122ProjectedSimplexInterior n)
  have hG_meas :
      Measurable fun z : (Fin n → ℝ) × ℝ =>
        ENNReal.ofReal
          (z.2 ^ n *
            ex122GammaProductPDFReal α β
              (ex122ProjectedChart z.1 z.2)) := by
    have hreal :
        Measurable fun z : (Fin n → ℝ) × ℝ =>
          z.2 ^ n *
            ex122GammaProductPDFReal α β
              (ex122ProjectedChart z.1 z.2) := by
      exact
        (measurable_snd.pow_const n).mul
          ((measurable_ex122GammaProductPDFReal α β).comp
            (measurable_ex122ProjectedChart_pair (n := n)))
    exact hreal.ennreal_ofReal
  have hinner_meas :
      AEMeasurable inner
        ((volume : Measure (Fin n → ℝ)).restrict A) := by
    have hmeas :
        Measurable fun y : Fin n → ℝ =>
          ∫⁻ t : ℝ,
            ENNReal.ofReal
              (t ^ n *
                ex122GammaProductPDFReal α β
                  (ex122ProjectedChart y t))
            ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      simpa using
        (hG_meas.lintegral_prod_right'
          (ν := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))))
    simpa [inner] using hmeas.aemeasurable.restrict
  have hchart_finite :
      (∫⁻ z in ex122ProjectedPositiveChartDomain (n := n) A,
        ENNReal.ofReal
          (z.2 ^ n *
            ex122GammaProductPDFReal α β
              (ex122ProjectedChart z.1 z.2))
        ∂(volume : Measure ((Fin n → ℝ) × ℝ))) ≠ ∞ := by
    have hpre_finite :
        (∫⁻ x in
            {x : Fin (n + 1) → ℝ |
              (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ A},
          ENNReal.ofReal (ex122GammaProductPDFReal α β x)
            ∂(volume : Measure (Fin (n + 1) → ℝ))) ≠ ∞ := by
      have hmeasure_ne_top :
          ex122GammaProductLaw α β
            {x : Fin (n + 1) → ℝ |
              (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ A} ≠ ∞ := by
        letI : IsProbabilityMeasure (ex122GammaProductLaw α β) :=
          ex122GammaProductLaw_isProbability α hα hβ
        exact measure_ne_top (ex122GammaProductLaw α β) _
      rw [ex122GammaProductLaw_eq_gammaProductDensityMeasure α hα hβ] at hmeasure_ne_top
      unfold ex122GammaProductDensityMeasure at hmeasure_ne_top
      rw [withDensity_apply _
        (measurableSet_ex122ProjectedPositivePreimage hA)] at hmeasure_ne_top
      exact hmeasure_ne_top
    have hsub : A ⊆ ex122ProjectedSimplexInterior n := by
      intro y hy
      exact hy.2
    have hcov :=
      ex122ProjectedPositiveChartLIntegralIdentity_proved α β A hA hsub
    rwa [← hcov]
  have hinner_set_finite :
      (∫⁻ y in A, inner y ∂(volume : Measure (Fin n → ℝ))) ≠ ∞ := by
    rw [← ex122ProjectedPositiveChartDomain_lintegral_eq_iterated
      (n := n) (s := A)
      (fun z : (Fin n → ℝ) × ℝ =>
        ENNReal.ofReal
          (z.2 ^ n *
            ex122GammaProductPDFReal α β
              (ex122ProjectedChart z.1 z.2)))]
    · exact hchart_finite
    · exact hG_meas.aemeasurable.restrict
  have hinner_lt_top_restrict :
      ∀ᵐ y ∂((volume : Measure (Fin n → ℝ)).restrict A),
        inner y < ∞ :=
    ae_lt_top' hinner_meas hinner_set_finite
  have hinner_lt_top :
      ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
        y ∈ A → inner y < ∞ := by
    rwa [ae_restrict_iff' hA] at hinner_lt_top_restrict
  filter_upwards [hinner_lt_top] with y hy_finite hyA
  have hreal_to_lintegral :
      ex122ProjectedGammaCOVDensity α β y = (inner y).toReal := by
    rw [ex122ProjectedGammaCOVDensity_source_integral_chart_productPDF]
    have hnonneg :
        0 ≤ᵐ[((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))]
          fun t : ℝ =>
            t ^ n *
              ex122GammaProductPDFReal α β
                (ex122ProjectedChart y t) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg (pow_nonneg (le_of_lt ht) n)
        (ex122GammaProductPDFReal_nonneg hα hβ _)
    have hstrong :
        AEStronglyMeasurable
          (fun t : ℝ =>
            t ^ n *
              ex122GammaProductPDFReal α β
                (ex122ProjectedChart y t))
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
      have hmeas :
          Measurable fun t : ℝ =>
            t ^ n *
              ex122GammaProductPDFReal α β
                (ex122ProjectedChart y t) := by
        exact
          (measurable_id.pow_const n).mul
            ((measurable_ex122GammaProductPDFReal α β).comp
              (measurable_ex122ProjectedChart_fiber y))
      exact hmeas.aestronglyMeasurable.restrict
    rw [integral_eq_lintegral_of_nonneg_ae hnonneg hstrong]
  rw [hreal_to_lintegral]
  exact ENNReal.ofReal_toReal (ne_of_lt (hy_finite hyA))

theorem ex122_lintegral_positiveChartDomain_eq_lintegral_COVDensity
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    (∫⁻ z in
        ex122ProjectedPositiveChartDomain (n := n)
          (s ∩ ex122ProjectedSimplexInterior n),
      ENNReal.ofReal
        (z.2 ^ n *
          ex122GammaProductPDFReal α β
            (ex122ProjectedChart z.1 z.2))
      ∂(volume : Measure ((Fin n → ℝ) × ℝ))) =
    (∫⁻ y in s,
      ex122ProjectedCOVDensityENNReal α β y
      ∂(volume : Measure (Fin n → ℝ))) := by
  let A : Set (Fin n → ℝ) := s ∩ ex122ProjectedSimplexInterior n
  let g : ((Fin n → ℝ) × ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal
      (z.2 ^ n *
        ex122GammaProductPDFReal α β
          (ex122ProjectedChart z.1 z.2))
  have hA : MeasurableSet A := by
    exact hs.inter (measurableSet_ex122ProjectedSimplexInterior n)
  have hg_meas : Measurable g := by
    have hreal :
        Measurable fun z : (Fin n → ℝ) × ℝ =>
          z.2 ^ n *
            ex122GammaProductPDFReal α β
              (ex122ProjectedChart z.1 z.2) := by
      exact (measurable_snd.pow_const n).mul
        ((measurable_ex122GammaProductPDFReal α β).comp
          (measurable_ex122ProjectedChart_pair (n := n)))
    exact hreal.ennreal_ofReal
  have hOfReal :=
    ofReal_ex122ProjectedGammaCOVDensity_eq_lintegral_source_integral_ae_restrict
      α hα hβ hs
  calc
    (∫⁻ z in
        ex122ProjectedPositiveChartDomain (n := n)
          (s ∩ ex122ProjectedSimplexInterior n),
      ENNReal.ofReal
        (z.2 ^ n *
          ex122GammaProductPDFReal α β
            (ex122ProjectedChart z.1 z.2))
      ∂(volume : Measure ((Fin n → ℝ) × ℝ))) =
      (∫⁻ y in A,
        ∫⁻ t in Set.Ioi (0 : ℝ), g (y, t)
          ∂(volume : Measure ℝ)
        ∂(volume : Measure (Fin n → ℝ))) := by
        change
          (∫⁻ z in ex122ProjectedPositiveChartDomain (n := n) A,
            g z ∂(volume : Measure ((Fin n → ℝ) × ℝ))) =
          (∫⁻ y in A,
            ∫⁻ t in Set.Ioi (0 : ℝ), g (y, t)
              ∂(volume : Measure ℝ)
            ∂(volume : Measure (Fin n → ℝ)))
        exact ex122ProjectedPositiveChartDomain_lintegral_eq_iterated
          (n := n) (s := A) g hg_meas.aemeasurable.restrict
    _ =
      (∫⁻ y in A,
        ENNReal.ofReal (ex122ProjectedGammaCOVDensity α β y)
        ∂(volume : Measure (Fin n → ℝ))) := by
        refine setLIntegral_congr_fun_ae hA ?_
        filter_upwards [hOfReal] with y hy yA
        simpa [g] using (hy yA).symm
    _ =
      (∫⁻ y in A,
        ex122ProjectedCOVDensityENNReal α β y
        ∂(volume : Measure (Fin n → ℝ))) := by
        refine setLIntegral_congr_fun hA ?_
        intro y hy
        exact
          (ex122ProjectedCOVDensityENNReal_eq_ofReal_on_interior
            α β hy.2).symm
    _ =
      (∫⁻ y in s,
      ex122ProjectedCOVDensityENNReal α β y
        ∂(volume : Measure (Fin n → ℝ))) := by
        rw [show A = s ∩ ex122ProjectedSimplexInterior n from rfl]
        exact
          (ex122_lintegral_projectedCOVDensity_eq_interior
            α β hs).symm

theorem ex122ProjectedCOVLIntegralPreimageIdentity_of_pos
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122ProjectedCOVLIntegralPreimageIdentity α β := by
  intro s hs
  let A : Set (Fin n → ℝ) := s ∩ ex122ProjectedSimplexInterior n
  have hA : MeasurableSet A := by
    exact hs.inter (measurableSet_ex122ProjectedSimplexInterior n)
  have hA_sub : A ⊆ ex122ProjectedSimplexInterior n := by
    intro y hy
    exact hy.2
  have hpos_preimage :
      {x : Fin (n + 1) → ℝ |
        (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s} =
      {x : Fin (n + 1) → ℝ |
        (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ A} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,
        ⟨hx.2, ex122ProjectedNormalize_mem_interior_of_all_pos hx.1⟩⟩
    · intro hx
      exact ⟨hx.1, hx.2.1⟩
  calc
    (∫⁻ x in
        (ex122ProjectedNormalize :
          (Fin (n + 1) → ℝ) → Fin n → ℝ) ⁻¹' s,
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) =
    (∫⁻ x in
        {x : Fin (n + 1) → ℝ |
          (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ s},
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) := by
      exact ex122ProjectedNormalize_preimage_lintegral_support_reduce
        α hα hβ hs
    _ =
    (∫⁻ x in
        {x : Fin (n + 1) → ℝ |
          (∀ i, 0 < x i) ∧ ex122ProjectedNormalize x ∈ A},
      ENNReal.ofReal (ex122GammaProductPDFReal α β x)
        ∂(volume : Measure (Fin (n + 1) → ℝ))) := by
      rw [hpos_preimage]
    _ =
    (∫⁻ z in ex122ProjectedPositiveChartDomain (n := n) A,
      ENNReal.ofReal
        (z.2 ^ n *
          ex122GammaProductPDFReal α β
            (ex122ProjectedChart z.1 z.2))
      ∂(volume : Measure ((Fin n → ℝ) × ℝ))) := by
      exact ex122ProjectedPositiveChartLIntegralIdentity_proved
        α β A hA hA_sub
    _ =
    (∫⁻ y in s,
      ex122ProjectedCOVDensityENNReal α β y
        ∂(volume : Measure (Fin n → ℝ))) := by
      exact ex122_lintegral_positiveChartDomain_eq_lintegral_COVDensity
        α hα hβ hs

/-- A concrete measure-level COV bridge: after the joint Gamma product density
has been established, it remains only to prove the measurable-set preimage
integral identity for the nonlinear map
`x ↦ (x₁ / ∑ xᵢ, ..., xₙ / ∑ xᵢ)`. -/
theorem ex122ProjectedDirichletLaw_eq_COVMeasure_of_lintegral_preimage {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    (hCOV : ex122ProjectedCOVLIntegralPreimageIdentity α β) :
    ex122ProjectedDirichletLaw α β = ex122ProjectedCOVMeasure α β := by
  rw [ex122ProjectedDirichletLaw_eq_map_projectedNormalize_density α hα hβ]
  unfold ex122GammaProductDensityMeasure ex122ProjectedCOVMeasure
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_ex122ProjectedNormalize hs]
  rw [withDensity_apply _ (hs.preimage measurable_ex122ProjectedNormalize)]
  rw [withDensity_apply _ hs]
  exact hCOV s hs

theorem ex122ProjectedDirichletLaw_eq_COVMeasure_of_pos {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122ProjectedDirichletLaw α β = ex122ProjectedCOVMeasure α β := by
  exact ex122ProjectedDirichletLaw_eq_COVMeasure_of_lintegral_preimage
    α hα hβ (ex122ProjectedCOVLIntegralPreimageIdentity_of_pos α hα hβ)

/-- Reusable obligations for the general projected density law. The first field
is the joint Gamma density bridge, the second is the multivariate
change-of-variables/Jacobian bridge, and the third is the one-dimensional
total-mass Gamma integral that reduces the COV density to equation (1.4). -/
structure Ex122ProjectedDensityObligations {n : ℕ}
    (α : Fin (n + 1) → ℝ) (β : ℝ) : Prop where
  jointGammaDensity :
    ex122GammaProductLaw α β = ex122GammaProductDensityMeasure α β
  changeOfVariablesWithJacobian :
    ex122ProjectedDirichletLaw α β = ex122ProjectedCOVMeasure α β
  gammaIntegralNormalizes :
    ∀ y, y ∈ ex122ProjectedSimplexInterior n →
      ex122ProjectedGammaCOVDensity α β y =
        ex122DirichletProjectedDensity α y

theorem ex122ProjectedCOVMeasure_eq_projectedDensityMeasure_of_integral_eval
    {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ)
    (hEval : ∀ y, y ∈ ex122ProjectedSimplex n →
      ex122ProjectedGammaCOVDensity α β y =
        ex122DirichletProjectedDensity α y) :
    ex122ProjectedCOVMeasure α β = ex122ProjectedDensityMeasure α := by
  unfold ex122ProjectedCOVMeasure ex122ProjectedDensityMeasure
  refine withDensity_congr_ae ?_
  exact Filter.Eventually.of_forall fun y => by
    unfold ex122ProjectedCOVDensityENNReal ex122ProjectedDensityENNReal
    classical
    by_cases hy : y ∈ ex122ProjectedSimplex n
    · simp [hy, hEval y hy]
    · simp [hy]

/-- For the projected density measure, open-simplex equality is enough: the
closed support differs from the open projected simplex by a null union of faces. -/
theorem ex122ProjectedCOVMeasure_eq_projectedDensityMeasure_of_integral_eval_open
    {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ)
    (hEval : ∀ y, y ∈ ex122ProjectedSimplexInterior n →
      ex122ProjectedGammaCOVDensity α β y =
        ex122DirichletProjectedDensity α y) :
    ex122ProjectedCOVMeasure α β = ex122ProjectedDensityMeasure α := by
  unfold ex122ProjectedCOVMeasure ex122ProjectedDensityMeasure
  refine withDensity_congr_ae ?_
  filter_upwards [ex122ProjectedSimplex_closed_imp_interior_ae n] with y hInterior
  unfold ex122ProjectedCOVDensityENNReal ex122ProjectedDensityENNReal
  classical
  by_cases hy : y ∈ ex122ProjectedSimplex n
  · have hEq := hEval y (hInterior hy)
    simp [hy, hEq]
  · simp [hy]

/-- General law-level projected density equality reduced to the reusable
change-of-variables, Jacobian, and normalization obligations. The fully closed
target is the same conclusion without the `Ex122ProjectedDensityObligations`
premise. -/
theorem ex122ProjectedDirichletLaw_eq_projectedDensityMeasure_of_obligations
    {n : ℕ} (α : Fin (n + 1) → ℝ) {β : ℝ}
    (_hα : ∀ i, 0 < α i) (_hβ : 0 < β)
    (h : Ex122ProjectedDensityObligations α β) :
    ex122ProjectedDirichletLaw α β = ex122ProjectedDensityMeasure α := by
  rw [h.changeOfVariablesWithJacobian]
  exact ex122ProjectedCOVMeasure_eq_projectedDensityMeasure_of_integral_eval_open
    α β h.gammaIntegralNormalizes
