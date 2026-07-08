import Mathlib
import ToyApollo.Output.def_1_2
import ToyApollo.Output.def_1_4
import ToyApollo.Output.thm_1_3
import ToyApollo.Output.thm_1_4
import ToyApollo.Output.thm_1_2
import ToyApollo.Output.ex_1_2_1
import ToyApollo.Output.rs_stieltjes_step_support
import ToyApollo.Output.thm_7_9_double_filter_support

open MeasureTheory intervalIntegral Set Filter
open scoped Real ENNReal

namespace Ex132

noncomputable section

/-! ### Standard normal density -/

/-- Standard normal density `φ(x) = (√(2π))⁻¹ · e^{-x²/2}`. -/
def standardNormalKernel (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- The kernel is exactly Mathlib's `gaussianPDFReal 0 1`. -/
theorem standardNormalKernel_eq_gaussianPDFReal (x : ℝ) :
    standardNormalKernel x = ProbabilityTheory.gaussianPDFReal 0 1 x := by
  unfold standardNormalKernel ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]

/-- The kernel is even. -/
theorem standardNormalKernel_even (x : ℝ) :
    standardNormalKernel (-x) = standardNormalKernel x := by
  simp [standardNormalKernel]

/-- The kernel is continuous. -/
theorem continuous_standardNormalKernel : Continuous standardNormalKernel := by
  unfold standardNormalKernel
  fun_prop

/-- The kernel is nonnegative. -/
theorem standardNormalKernel_nonneg (x : ℝ) : 0 ≤ standardNormalKernel x := by
  unfold standardNormalKernel
  positivity

/-! ### The parameter `p = P(Z > 3/2)` and the two integrators. -/

/-- The atom mass `p = P(Z > 3/2)`, valued in `ℝ`. -/
def pTail : ℝ := (standardGaussianLaw (Set.Ici (3 / 2 : ℝ))).toReal

/-- `α₁` — the two-atom step of Example 1.3.2. Each summand is the raw
`if x < c then 0 else p` matching `rsIntegral_singleJumpStep_exists`. -/
def alpha1 (p : ℝ) : ℝ → ℝ :=
  fun x => (if x < (-3 / 2 : ℝ) then (0 : ℝ) else p) + (if x < (3 / 2 : ℝ) then (0 : ℝ) else p)

/-- `α₂` — the corrected mixed continuous part (author erratum: no `(1-2p)`
prefactor on the middle branch). -/
def alpha2 (p : ℝ) : ℝ → ℝ :=
  fun x =>
    if x < (-3 / 2 : ℝ) then 0
    else if x < (3 / 2 : ℝ) then ∫ t in (-3 / 2 : ℝ)..x, standardNormalKernel t
    else 1 - 2 * p

/-- The globally-`C¹` antiderivative `β(x) = ∫_{-3/2}^x φ` used to instantiate `thm_1_4`. -/
def beta : ℝ → ℝ := fun x => ∫ t in (-3 / 2 : ℝ)..x, standardNormalKernel t

/-! ### The interior integral `∫_{-3/2}^{3/2} y·φ(y) = 0` by oddness. -/

/-- The integrand `y ↦ y·φ(y)` is odd. -/
theorem mixedIntegrand_odd (x : ℝ) :
    (-x) * standardNormalKernel (-x) = -(x * standardNormalKernel x) := by
  rw [standardNormalKernel_even]; ring

/-- `∫_{-3/2}^{3/2} y·φ(y) dy = 0`. -/
theorem interior_integral_zero :
    ∫ y in (-(3 / 2 : ℝ))..(3 / 2 : ℝ), y * standardNormalKernel y = 0 := by
  set c : ℝ := 3 / 2 with hc
  set g : ℝ → ℝ := fun y => y * standardNormalKernel y with hg
  -- `integral_comp_neg`: ∫_{-c}^{c} g(-x) dx = ∫_{-c}^{c} g x dx  (since `-b..-a = -c..c`).
  have hcomp :
      ∫ x in (-c : ℝ)..c, g (-x) = ∫ x in (-c : ℝ)..c, g x := by
    have h := intervalIntegral.integral_comp_neg (f := g) (a := (-c : ℝ)) (b := c)
    simp only [neg_neg] at h
    exact h
  have hodd : ∫ x in (-c : ℝ)..c, g (-x) = -∫ x in (-c : ℝ)..c, g x := by
    have hpt : ∀ x, g (-x) = -g x := by
      intro x; simp only [hg]; exact mixedIntegrand_odd x
    calc
      ∫ x in (-c : ℝ)..c, g (-x) = ∫ x in (-c : ℝ)..c, -g x := by
            simp only [hpt]
      _ = -∫ x in (-c : ℝ)..c, g x := by rw [intervalIntegral.integral_neg]
  have hself : ∫ x in (-c : ℝ)..c, g x = -∫ x in (-c : ℝ)..c, g x := by
    calc ∫ x in (-c : ℝ)..c, g x = ∫ x in (-c : ℝ)..c, g (-x) := hcomp.symm
      _ = -∫ x in (-c : ℝ)..c, g x := hodd
  linarith [hself]

/-! ### `β` is globally `C¹`, monotone, and `HasDerivAt β (φ x) x`. -/

/-- FTC: `β(x) = ∫_{-3/2}^x φ` has derivative `φ x` at every `x`. -/
theorem beta_hasDerivAt (x : ℝ) : HasDerivAt beta (standardNormalKernel x) x := by
  have h := (continuous_standardNormalKernel.integral_hasStrictDerivAt (-3 / 2 : ℝ) x).hasDerivAt
  exact h

/-- `β` is monotone (its derivative `φ ≥ 0` everywhere). -/
theorem beta_monotone : Monotone beta := by
  apply monotone_of_deriv_nonneg
  · exact fun x => (beta_hasDerivAt x).differentiableAt
  · intro x
    rw [(beta_hasDerivAt x).deriv]
    exact standardNormalKernel_nonneg x

/-! ### Gaussian mass identities (obligation 3b foundations). -/

/-- `standardGaussianLaw s = ENNReal.ofReal (∫ x in s, φ x)`. -/
theorem standardGaussianLaw_apply (s : Set ℝ) :
    standardGaussianLaw s = ENNReal.ofReal (∫ x in s, standardNormalKernel x) := by
  have h := ProbabilityTheory.gaussianReal_apply_eq_integral 0 (v := 1) (by norm_num) s
  rw [show standardGaussianLaw = ProbabilityTheory.gaussianReal 0 1 from rfl, h]
  congr 1
  have hfun : standardNormalKernel = ProbabilityTheory.gaussianPDFReal 0 1 :=
    funext standardNormalKernel_eq_gaussianPDFReal
  rw [hfun]

/-- The density is integrable (so all set integrals are finite). -/
theorem integrable_standardNormalKernel : Integrable standardNormalKernel := by
  have h := ProbabilityTheory.integrable_gaussianPDFReal 0 1
  refine (integrable_congr ?_).mpr h
  filter_upwards with x
  exact standardNormalKernel_eq_gaussianPDFReal x

/-- Symmetry of the standard Gaussian: `standardGaussianLaw (Iic (-a)) = standardGaussianLaw (Ici a)`. -/
theorem standardGaussianLaw_Iic_neg_eq_Ici (a : ℝ) :
    standardGaussianLaw (Set.Iic (-a)) = standardGaussianLaw (Set.Ici a) := by
  have hmap : Measure.map (fun x => -x) standardGaussianLaw = standardGaussianLaw := by
    have h := ProbabilityTheory.gaussianReal_map_neg (μ := 0) (v := 1)
    simpa [standardGaussianLaw] using h
  have hmeas : Measurable (fun x : ℝ => -x) := measurable_neg
  calc standardGaussianLaw (Set.Iic (-a))
      = Measure.map (fun x => -x) standardGaussianLaw (Set.Iic (-a)) := by rw [hmap]
    _ = standardGaussianLaw ((fun x => -x) ⁻¹' Set.Iic (-a)) := by
          rw [Measure.map_apply hmeas measurableSet_Iic]
    _ = standardGaussianLaw (Set.Ici a) := by
          congr 1
          ext x
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]

/-- `pTail` as a real integral over `Ici (3/2)`. -/
theorem pTail_eq_integral_Ici :
    pTail = ∫ x in Set.Ici (3 / 2 : ℝ), standardNormalKernel x := by
  unfold pTail
  rw [standardGaussianLaw_apply]
  rw [ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Ici (fun x _ => standardNormalKernel_nonneg x)

/-- `Ici` and `Ioi` set-integrals of `φ` agree (the atom `{3/2}` is Lebesgue-null). -/
theorem integral_Ici_eq_Ioi (a : ℝ) :
    ∫ x in Set.Ici a, standardNormalKernel x = ∫ x in Set.Ioi a, standardNormalKernel x := by
  have hdisj : Disjoint (Set.Ioi a) ({a} : Set ℝ) := by
    rw [Set.disjoint_singleton_right]; exact lt_irrefl a
  rw [← Set.Ioi_union_left, setIntegral_union hdisj
    (measurableSet_singleton a) (integrable_standardNormalKernel.integrableOn)
    (integrable_standardNormalKernel.integrableOn)]
  simp

theorem integral_Iic_eq_Iio (a : ℝ) :
    ∫ x in Set.Iic a, standardNormalKernel x = ∫ x in Set.Iio a, standardNormalKernel x := by
  have hdisj : Disjoint (Set.Iio a) ({a} : Set ℝ) := by
    rw [Set.disjoint_singleton_right]; exact lt_irrefl a
  rw [← Set.Iio_union_right, setIntegral_union hdisj
    (measurableSet_singleton a) (integrable_standardNormalKernel.integrableOn)
    (integrable_standardNormalKernel.integrableOn)]
  simp

/-- `pTail` also equals the left-tail integral `∫_{Iic (-3/2)} φ` (symmetry). -/
theorem pTail_eq_integral_Iic :
    pTail = ∫ x in Set.Iic (-3 / 2 : ℝ), standardNormalKernel x := by
  have hnegeq : (Set.Iic (-(3 / 2) : ℝ)) = (Set.Iic (-3 / 2 : ℝ)) := by norm_num
  have hsym := standardGaussianLaw_Iic_neg_eq_Ici (3 / 2 : ℝ)
  rw [hnegeq] at hsym
  have hleft : standardGaussianLaw (Set.Iic (-3 / 2 : ℝ)) =
      ENNReal.ofReal (∫ x in Set.Iic (-3 / 2 : ℝ), standardNormalKernel x) :=
    standardGaussianLaw_apply _
  have hright : standardGaussianLaw (Set.Ici (3 / 2 : ℝ)) =
      ENNReal.ofReal (∫ x in Set.Ici (3 / 2 : ℝ), standardNormalKernel x) :=
    standardGaussianLaw_apply _
  have hL : (0 : ℝ) ≤ ∫ x in Set.Iic (-3 / 2 : ℝ), standardNormalKernel x :=
    setIntegral_nonneg measurableSet_Iic (fun x _ => standardNormalKernel_nonneg x)
  have hR : (0 : ℝ) ≤ ∫ x in Set.Ici (3 / 2 : ℝ), standardNormalKernel x :=
    setIntegral_nonneg measurableSet_Ici (fun x _ => standardNormalKernel_nonneg x)
  have heq : ENNReal.ofReal (∫ x in Set.Iic (-3 / 2 : ℝ), standardNormalKernel x) =
      ENNReal.ofReal (∫ x in Set.Ici (3 / 2 : ℝ), standardNormalKernel x) := by
    rw [← hleft, ← hright]; exact hsym
  have hval := (ENNReal.ofReal_eq_ofReal_iff hL hR).mp heq
  rw [pTail_eq_integral_Ici]
  linarith [hval]

/-- Total mass: `∫ φ = 1`. -/
theorem integral_standardNormalKernel_univ :
    ∫ x, standardNormalKernel x = 1 := by
  have h := ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (v := 1) (by norm_num)
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall standardNormalKernel_eq_gaussianPDFReal)

/-- Plateau continuity: `β(3/2) = ∫_{-3/2}^{3/2} φ = 1 - 2·pTail`. -/
theorem beta_at_right : beta (3 / 2 : ℝ) = 1 - 2 * pTail := by
  -- `∫_{Iic -3/2} φ + ∫_{Ioi -3/2} φ = ∫ φ = 1`.
  have hsplit1 :
      (∫ x in Set.Iic (-3 / 2 : ℝ), standardNormalKernel x) +
        (∫ x in (Set.Iic (-3 / 2 : ℝ))ᶜ, standardNormalKernel x) =
        ∫ x, standardNormalKernel x :=
    integral_add_compl measurableSet_Iic integrable_standardNormalKernel
  have hcompl : (Set.Iic (-3 / 2 : ℝ))ᶜ = Set.Ioi (-3 / 2 : ℝ) := by
    ext x; simp
  rw [hcompl] at hsplit1
  -- `∫_{-3/2}^{3/2} φ + ∫_{Ioi 3/2} φ = ∫_{Ioi -3/2} φ`.
  have hsplit2 :
      (∫ x in (-3 / 2 : ℝ)..(3 / 2 : ℝ), standardNormalKernel x) +
        (∫ x in Set.Ioi (3 / 2 : ℝ), standardNormalKernel x) =
        ∫ x in Set.Ioi (-3 / 2 : ℝ), standardNormalKernel x :=
    intervalIntegral.integral_interval_add_Ioi
      (integrable_standardNormalKernel.integrableOn)
      (integrable_standardNormalKernel.integrableOn)
  have hRight : (∫ x in Set.Ioi (3 / 2 : ℝ), standardNormalKernel x) = pTail := by
    rw [pTail_eq_integral_Ici, integral_Ici_eq_Ioi]
  have hLeft : (∫ x in Set.Iic (-3 / 2 : ℝ), standardNormalKernel x) = pTail :=
    pTail_eq_integral_Iic.symm
  have hUniv : (∫ x, standardNormalKernel x) = 1 := integral_standardNormalKernel_univ
  have hbeta : beta (3 / 2 : ℝ) = ∫ x in (-3 / 2 : ℝ)..(3 / 2 : ℝ), standardNormalKernel x := rfl
  rw [hbeta]
  rw [hRight] at hsplit2
  rw [hLeft, hUniv] at hsplit1
  -- hsplit1 : pTail + ∫_{Ioi -3/2} φ = 1
  -- hsplit2 : ∫_{-3/2}^{3/2} φ + pTail = ∫_{Ioi -3/2} φ
  linarith [hsplit1, hsplit2]

/-- On `Icc (-3/2) (3/2)`, `α₂` (with `p = pTail`) agrees with `β`. -/
theorem alpha2_eq_beta_on_Icc :
    ∀ x ∈ Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ), beta x = alpha2 pTail x := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  rcases lt_or_ge x (3 / 2 : ℝ) with hlt | hge
  · have hnl : ¬ x < (-3 / 2 : ℝ) := not_lt.mpr hlo
    simp only [alpha2, beta, hnl, if_false, hlt, if_true]
  · have hx32 : x = (3 / 2 : ℝ) := le_antisymm hhi hge
    have hnl : ¬ x < (-3 / 2 : ℝ) := not_lt.mpr hlo
    have hnr : ¬ x < (3 / 2 : ℝ) := not_lt.mpr hge
    simp only [alpha2, hnl, if_false, hnr, if_false]
    rw [hx32]
    exact beta_at_right

/-! ### RS integrability of `id` against monotone integrators on any interval. -/

/-- For any monotone integrator `α` and any `a < b`, `id` is RS-integrable on `[a,b]`
(the integrand `id` is continuous everywhere, so the discontinuity set is empty). -/
theorem rsIntegrable_id_of_monotone {α : ℝ → ℝ} (hα : Monotone α) {a b : ℝ} (hab : a < b) :
    RSIntegrable (fun y => y) α a b := by
  refine rsIntegrable_of_bounded_finite_discontinuities hab hα ?_ ?_ ?_ ?_
  · exact (isCompact_Icc.image continuous_id).bddAbove
  · exact (isCompact_Icc.image continuous_id).bddBelow
  · have hempty : ({x | x ∈ Set.Icc a b ∧ ¬ ContinuousAt (fun y : ℝ => y) x} : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hx.2 continuousAt_id
    rw [hempty]; exact Set.finite_empty
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    exact absurd continuousAt_id hx.2

/-! ### Interior RS value: `rsIntegral id α₂ (-3/2) (3/2) = 0`. -/

/-- `β` is monotone, so `id` is RS-integrable against `β` on `[-3/2,3/2]`. -/
theorem rsIntegrable_id_beta : RSIntegrable (fun y => y) beta (-3 / 2 : ℝ) (3 / 2 : ℝ) :=
  rsIntegrable_id_of_monotone beta_monotone (by norm_num)

/-- Via Theorem 1.4: `rsIntegral id β (-3/2) (3/2) = ∫ y·φ = 0`. -/
theorem rsIntegral_id_beta_eq_zero :
    rsIntegral (fun y => y) beta (-3 / 2 : ℝ) (3 / 2 : ℝ) rsIntegrable_id_beta = 0 := by
  have hthm := thm_1_4 (f := fun y => y) (α := beta) (α' := standardNormalKernel)
    (a := (-3 / 2 : ℝ)) (b := (3 / 2 : ℝ))
    (by norm_num)
    (continuous_id.continuousOn)
    beta_monotone
    (fun x _ => beta_hasDerivAt x)
    (continuous_standardNormalKernel.continuousOn)
    rsIntegrable_id_beta
  obtain ⟨_, hval⟩ := hthm
  rw [hval]
  -- `∫ y·φ` over `[-3/2, 3/2]`; note the interval bounds `(-3/2)` vs `-(3/2)`.
  have hbounds : (-3 / 2 : ℝ) = -(3 / 2 : ℝ) := by norm_num
  rw [hbounds]
  exact interior_integral_zero

/-! ### Basic sign/magnitude facts about `pTail`. -/

theorem pTail_nonneg : 0 ≤ pTail := by
  rw [pTail_eq_integral_Ici]
  exact setIntegral_nonneg measurableSet_Ici (fun x _ => standardNormalKernel_nonneg x)

/-- `1 - 2·pTail ≥ 0`, i.e. `2·pTail ≤ 1` (the interior mass is nonneg). -/
theorem two_pTail_le_one : 2 * pTail ≤ 1 := by
  -- `1 = ∫ φ = ∫_{Iic -3/2} + ∫_{Ioc -3/2 3/2} + ∫_{Ioi 3/2} = pTail + beta(3/2) + pTail`.
  have h := beta_at_right
  have hbeta_nonneg : 0 ≤ beta (3 / 2 : ℝ) := by
    have : beta (-3 / 2 : ℝ) = 0 := by
      simp [beta, intervalIntegral.integral_same]
    have hmono := beta_monotone (show (-3 / 2 : ℝ) ≤ 3 / 2 by norm_num)
    rw [this] at hmono
    exact hmono
  linarith [h, hbeta_nonneg]

/-! ### Global monotonicity of `α₂`. -/

/-- `α₂` (with `p = pTail`) is monotone on all of `ℝ`. -/
theorem alpha2_monotone : Monotone (alpha2 pTail) := by
  intro x y hxy
  -- Prove by relating `alpha2` to `beta` on the middle, `0` on left, plateau on right.
  -- Values: left `0`, middle `beta`, right `beta(3/2)`.  All ordered by `beta` monotone + signs.
  have hbeta0 : beta (-3 / 2 : ℝ) = 0 := by
    simp [beta, intervalIntegral.integral_same]
  -- Handy: on `[-3/2, 3/2]` closed, value equals `beta`; and `alpha2 x` is between `0` and `beta(3/2)`.
  have hval : ∀ z : ℝ, alpha2 pTail z =
      if z < (-3 / 2 : ℝ) then 0
      else if z < (3 / 2 : ℝ) then beta z else beta (3 / 2 : ℝ) := by
    intro z
    by_cases h1 : z < (-3 / 2 : ℝ)
    · simp only [alpha2, h1, if_true]
    · by_cases h2 : z < (3 / 2 : ℝ)
      · simp only [alpha2, beta, h1, h2, if_false, if_true]
      · simp only [alpha2, h1, h2, if_false]
        exact beta_at_right.symm
  rw [hval x, hval y]
  -- Establish bounds needed for each case.
  have hb0le : ∀ z : ℝ, (-3 / 2 : ℝ) ≤ z → 0 ≤ beta z := by
    intro z hz; rw [← hbeta0]; exact beta_monotone hz
  have hble32 : ∀ z : ℝ, z ≤ (3 / 2 : ℝ) → beta z ≤ beta (3 / 2 : ℝ) := by
    intro z hz; exact beta_monotone hz
  by_cases hx1 : x < (-3 / 2 : ℝ)
  · -- x in left branch: alpha2 x = 0
    simp only [hx1, if_true]
    by_cases hy1 : y < (-3 / 2 : ℝ)
    · simp [hy1]
    · by_cases hy2 : y < (3 / 2 : ℝ)
      · simp only [hy1, hy2, if_false, if_true]
        exact hb0le y (not_lt.mp hy1)
      · simp only [hy1, hy2, if_false]
        exact hb0le _ (by norm_num)
  · by_cases hx2 : x < (3 / 2 : ℝ)
    · -- x in middle: alpha2 x = beta x
      have hxge : (-3 / 2 : ℝ) ≤ x := not_lt.mp hx1
      have hynl : ¬ y < (-3 / 2 : ℝ) := not_lt.mpr (le_trans hxge hxy)
      simp only [hx1, hx2, if_false, if_true]
      by_cases hy2 : y < (3 / 2 : ℝ)
      · simp only [hynl, hy2, if_false, if_true]
        exact beta_monotone hxy
      · simp only [hynl, hy2, if_false]
        exact hble32 x (le_of_lt hx2)
    · -- x in right branch: alpha2 x = beta(3/2)
      have hxge : (3 / 2 : ℝ) ≤ x := not_lt.mp hx2
      have hynl : ¬ y < (-3 / 2 : ℝ) := not_lt.mpr (by linarith [le_trans hxge hxy])
      have hynr : ¬ y < (3 / 2 : ℝ) := not_lt.mpr (le_trans hxge hxy)
      simp only [hx1, hx2, hynl, hynr, if_false]
      exact le_rfl

/-! ### RS integral against a globally-constant integrator is `0`. -/

/-- `id` is RS-integrable against any constant integrator `fun _ => k`. -/
theorem rsIntegrable_id_const (k : ℝ) {a b : ℝ} (hab : a < b) :
    RSIntegrable (fun y => y) (fun _ => k) a b :=
  rsIntegrable_id_of_monotone (monotone_const) hab

/-- `rsIntegral id (fun _ => k) a b = 0` (constant integrator has zero increments). -/
theorem rsIntegral_id_const_eq_zero (k : ℝ) {a b : ℝ} (hab : a < b) :
    rsIntegral (fun y => y) (fun _ => k) a b (rsIntegrable_id_const k hab) = 0 := by
  have hthm := thm_1_4 (f := fun y => y) (α := fun _ => k) (α' := fun _ => (0 : ℝ))
    (a := a) (b := b)
    (le_of_lt hab)
    (continuous_id.continuousOn)
    (monotone_const)
    (fun x _ => hasDerivAt_const x k)
    (continuous_const.continuousOn)
    (rsIntegrable_id_const k hab)
  obtain ⟨_, hval⟩ := hthm
  rw [hval]
  simp

/-! ### Transport interior value to `α₂` and truncation-to-`[-3/2,3/2]`. -/

/-- `id` is RS-integrable against `α₂` on `[-3/2,3/2]`. -/
theorem rsIntegrable_id_alpha2_mid :
    RSIntegrable (fun y => y) (alpha2 pTail) (-3 / 2 : ℝ) (3 / 2 : ℝ) :=
  rsIntegrable_id_of_monotone alpha2_monotone (by norm_num)

/-- Transport: `rsIntegral id α₂ (-3/2) (3/2) = rsIntegral id β (-3/2) (3/2) = 0`. -/
theorem rsIntegral_id_alpha2_mid_eq_zero :
    rsIntegral (fun y => y) (alpha2 pTail) (-3 / 2 : ℝ) (3 / 2 : ℝ) rsIntegrable_id_alpha2_mid = 0 := by
  -- `rsIntegral_congr_integrator_Icc` transports from `β` (via `h : RSIntegrable id β`) to `α₂`.
  have hmonoOn : MonotoneOn (alpha2 pTail) (Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ)) :=
    alpha2_monotone.monotoneOn _
  have hEq : ∀ x ∈ Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ), alpha2 pTail x = beta x :=
    fun x hx => (alpha2_eq_beta_on_Icc x hx).symm
  have hcongr :
      rsIntegral (fun y => y) (alpha2 pTail) (-3 / 2 : ℝ) (3 / 2 : ℝ)
          (rsIntegrable_congr_integrator_Icc rsIntegrable_id_beta hmonoOn hEq) =
        rsIntegral (fun y => y) beta (-3 / 2 : ℝ) (3 / 2 : ℝ) rsIntegrable_id_beta :=
    rsIntegral_congr_integrator_Icc rsIntegrable_id_beta hmonoOn hEq
  -- The RSIntegrable proof is irrelevant to the value.
  rw [show rsIntegrable_id_alpha2_mid =
        rsIntegrable_congr_integrator_Icc rsIntegrable_id_beta hmonoOn hEq from rfl]
  rw [hcongr]
  exact rsIntegral_id_beta_eq_zero

/-- On `Icc a (-3/2)`, `α₂ ≡ 0`. -/
theorem alpha2_eq_zero_on_left {a : ℝ} :
    ∀ x ∈ Set.Icc a (-3 / 2 : ℝ), alpha2 pTail x = (fun _ => (0 : ℝ)) x := by
  intro x hx
  obtain ⟨_, hhi⟩ := hx
  by_cases h1 : x < (-3 / 2 : ℝ)
  · simp only [alpha2, h1, if_true]
  · -- x = -3/2: middle branch `∫_{-3/2}^{-3/2} φ = 0`.
    have hx32 : x = (-3 / 2 : ℝ) := le_antisymm hhi (not_lt.mp h1)
    have h2 : x < (3 / 2 : ℝ) := by rw [hx32]; norm_num
    simp only [alpha2, h1, h2, if_false, if_true]
    rw [hx32]; simp [intervalIntegral.integral_same]

/-- On `Icc (3/2) b`, `α₂ ≡ 1 - 2·pTail`. -/
theorem alpha2_eq_const_on_right {b : ℝ} :
    ∀ x ∈ Set.Icc (3 / 2 : ℝ) b, alpha2 pTail x = (fun _ => (1 - 2 * pTail : ℝ)) x := by
  intro x hx
  obtain ⟨hlo, _⟩ := hx
  have h1 : ¬ x < (-3 / 2 : ℝ) := by rw [not_lt]; linarith
  have h2 : ¬ x < (3 / 2 : ℝ) := not_lt.mpr hlo
  simp only [alpha2, h1, h2, if_false]

/-- `id` is RS-integrable against `α₂` on `Icc a (-3/2)` (α₂ monotone). -/
theorem rsIntegrable_id_alpha2_left {a : ℝ} (ha : a < (-3 / 2 : ℝ)) :
    RSIntegrable (fun y => y) (alpha2 pTail) a (-3 / 2 : ℝ) :=
  rsIntegrable_id_of_monotone alpha2_monotone ha

theorem rsIntegrable_id_alpha2_right {b : ℝ} (hb : (3 / 2 : ℝ) < b) :
    RSIntegrable (fun y => y) (alpha2 pTail) (3 / 2 : ℝ) b :=
  rsIntegrable_id_of_monotone alpha2_monotone hb

/-- Outer-left RS value is `0` (constant integrator). -/
theorem rsIntegral_id_alpha2_left_eq_zero {a : ℝ} (ha : a < (-3 / 2 : ℝ)) :
    rsIntegral (fun y => y) (alpha2 pTail) a (-3 / 2 : ℝ) (rsIntegrable_id_alpha2_left ha) = 0 := by
  have hmonoOn : MonotoneOn (alpha2 pTail) (Set.Icc a (-3 / 2 : ℝ)) :=
    alpha2_monotone.monotoneOn _
  have hcongr :
      rsIntegral (fun y => y) (alpha2 pTail) a (-3 / 2 : ℝ)
          (rsIntegrable_congr_integrator_Icc (rsIntegrable_id_const 0 ha) hmonoOn
            alpha2_eq_zero_on_left) =
        rsIntegral (fun y => y) (fun _ => (0 : ℝ)) a (-3 / 2 : ℝ) (rsIntegrable_id_const 0 ha) :=
    rsIntegral_congr_integrator_Icc (rsIntegrable_id_const 0 ha) hmonoOn alpha2_eq_zero_on_left
  rw [show rsIntegrable_id_alpha2_left ha =
        rsIntegrable_congr_integrator_Icc (rsIntegrable_id_const 0 ha) hmonoOn
          alpha2_eq_zero_on_left from rfl]
  rw [hcongr]
  exact rsIntegral_id_const_eq_zero 0 ha

theorem rsIntegral_id_alpha2_right_eq_zero {b : ℝ} (hb : (3 / 2 : ℝ) < b) :
    rsIntegral (fun y => y) (alpha2 pTail) (3 / 2 : ℝ) b (rsIntegrable_id_alpha2_right hb) = 0 := by
  have hmonoOn : MonotoneOn (alpha2 pTail) (Set.Icc (3 / 2 : ℝ) b) :=
    alpha2_monotone.monotoneOn _
  have hcongr :
      rsIntegral (fun y => y) (alpha2 pTail) (3 / 2 : ℝ) b
          (rsIntegrable_congr_integrator_Icc (rsIntegrable_id_const (1 - 2 * pTail) hb) hmonoOn
            alpha2_eq_const_on_right) =
        rsIntegral (fun y => y) (fun _ => (1 - 2 * pTail : ℝ)) (3 / 2 : ℝ) b
          (rsIntegrable_id_const (1 - 2 * pTail) hb) :=
    rsIntegral_congr_integrator_Icc (rsIntegrable_id_const (1 - 2 * pTail) hb) hmonoOn
      alpha2_eq_const_on_right
  rw [show rsIntegrable_id_alpha2_right hb =
        rsIntegrable_congr_integrator_Icc (rsIntegrable_id_const (1 - 2 * pTail) hb) hmonoOn
          alpha2_eq_const_on_right from rfl]
  rw [hcongr]
  exact rsIntegral_id_const_eq_zero (1 - 2 * pTail) hb

/-! ### Continuity of `α₂` (needed for the glue). -/

/-- Closed-form: `α₂(x) = max 0 (min (β x) (β (3/2)))`, hence continuous. -/
theorem alpha2_eq_clamp (x : ℝ) :
    alpha2 pTail x = max 0 (min (beta x) (beta (3 / 2 : ℝ))) := by
  have hbeta0 : beta (-3 / 2 : ℝ) = 0 := by simp [beta, intervalIntegral.integral_same]
  by_cases h1 : x < (-3 / 2 : ℝ)
  · -- `beta x < 0` here (strict-mono? use monotone: beta x ≤ beta(-3/2)=0, and need beta x ≤ 0).
    have hle : beta x ≤ 0 := by rw [← hbeta0]; exact beta_monotone (le_of_lt h1)
    have hle32 : beta x ≤ beta (3 / 2 : ℝ) := beta_monotone (by linarith)
    simp only [alpha2, h1, if_true]
    rw [min_eq_left hle32, max_eq_left hle]
  · by_cases h2 : x < (3 / 2 : ℝ)
    · have hge : 0 ≤ beta x := by rw [← hbeta0]; exact beta_monotone (not_lt.mp h1)
      have hle32 : beta x ≤ beta (3 / 2 : ℝ) := beta_monotone (le_of_lt h2)
      simp only [alpha2, h1, h2, if_false, if_true]
      rw [min_eq_left hle32, max_eq_right hge]
      rfl
    · have hge32 : beta (3 / 2 : ℝ) ≤ beta x := beta_monotone (not_lt.mp h2)
      have hge0 : 0 ≤ beta (3 / 2 : ℝ) := by rw [← hbeta0]; exact beta_monotone (by norm_num)
      simp only [alpha2, h1, h2, if_false]
      rw [min_eq_right hge32, max_eq_right hge0]
      exact beta_at_right.symm

/-- `β` is continuous (differentiable everywhere). -/
theorem continuous_beta : Continuous beta :=
  continuous_iff_continuousAt.mpr (fun x => (beta_hasDerivAt x).continuousAt)

theorem continuous_alpha2 : Continuous (alpha2 pTail) := by
  have heq : alpha2 pTail = fun x => max 0 (min (beta x) (beta (3 / 2 : ℝ))) :=
    funext alpha2_eq_clamp
  rw [heq]
  exact continuous_const.max (continuous_beta.min continuous_const)

/-! ### Truncated RS value: `rsIntegral id α₂ a b = 0` for `a < -3/2 < 3/2 < b`. -/

/-- For `a < -3/2` and `3/2 < b`, `rsIntegral id α₂ a b = 0`. -/
theorem rsIntegral_id_alpha2_trunc_eq_zero {a b : ℝ}
    (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    ∃ h : RSIntegrable (fun y => y) (alpha2 pTail) a b,
      rsIntegral (fun y => y) (alpha2 pTail) a b h = 0 := by
  have hcont : ContinuousAt (alpha2 pTail) (-3 / 2 : ℝ) := continuous_alpha2.continuousAt
  have hcont2 : ContinuousAt (alpha2 pTail) (3 / 2 : ℝ) := continuous_alpha2.continuousAt
  -- Glue [-3/2,3/2] and [3/2,b] first, then [a,-3/2] with that.
  obtain ⟨hmr, hmr_val⟩ :=
    Thm12Item4.rsIntegral_glue (a := (-3 / 2 : ℝ)) (d := (3 / 2 : ℝ)) (b := b)
      (by norm_num) hb
      rsIntegrable_id_alpha2_mid (rsIntegrable_id_alpha2_right hb) (Or.inl hcont2)
  obtain ⟨hfull, hfull_val⟩ :=
    Thm12Item4.rsIntegral_glue (a := a) (d := (-3 / 2 : ℝ)) (b := b)
      ha (by linarith)
      (rsIntegrable_id_alpha2_left ha) hmr (Or.inl hcont)
  refine ⟨hfull, ?_⟩
  rw [hfull_val, hmr_val, rsIntegral_id_alpha2_mid_eq_zero,
    rsIntegral_id_alpha2_right_eq_zero hb, rsIntegral_id_alpha2_left_eq_zero ha]
  ring

/-- `pTail > 0` (the right-tail Gaussian mass is positive). -/
theorem pTail_pos : 0 < pTail := by
  unfold pTail
  rw [ENNReal.toReal_pos_iff]
  refine ⟨standardGaussianLaw_Ici_pos _, ?_⟩
  -- Gaussian measure of any set is ≤ 1 < ∞.
  calc standardGaussianLaw (Set.Ici (3 / 2 : ℝ)) ≤ standardGaussianLaw Set.univ :=
        measure_mono (Set.subset_univ _)
    _ = 1 := by
        rw [show standardGaussianLaw = ProbabilityTheory.gaussianReal 0 1 from rfl]
        exact measure_univ
    _ < ⊤ := ENNReal.one_lt_top

/-! ### α₁ truncation value: `rsIntegral id α₁ a b = 0` for `a < -3/2 < 3/2 < b`. -/

/-- Left atom jump value on `[a,b]`: `rsIntegral id (if x<-3/2 then 0 else p) = (-3/2)·p`. -/
theorem rsIntegral_leftAtom {a b : ℝ} (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    ∃ h : RSIntegrable (fun y => y) (fun x => if x < (-3 / 2 : ℝ) then (0 : ℝ) else pTail) a b,
      rsIntegral (fun y => y) (fun x => if x < (-3 / 2 : ℝ) then (0 : ℝ) else pTail) a b h
        = (-3 / 2 : ℝ) * pTail := by
  have hAbove : BddAbove ((fun y : ℝ => y) '' Set.Icc a b) :=
    (isCompact_Icc.image continuous_id).bddAbove
  have hBelow : BddBelow ((fun y : ℝ => y) '' Set.Icc a b) :=
    (isCompact_Icc.image continuous_id).bddBelow
  obtain ⟨h, hv⟩ := rsIntegral_singleJumpStep_exists
    (f := fun y : ℝ => y) (a := a) (b := b) (c := (-3 / 2 : ℝ)) (u₁ := 0) (u₂ := pTail)
    (le_of_lt (lt_trans ha (by linarith))) ha (by linarith) pTail_pos hAbove hBelow continuousAt_id
  refine ⟨h, ?_⟩
  rw [hv]; simp

theorem rsIntegral_rightAtom {a b : ℝ} (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    ∃ h : RSIntegrable (fun y => y) (fun x => if x < (3 / 2 : ℝ) then (0 : ℝ) else pTail) a b,
      rsIntegral (fun y => y) (fun x => if x < (3 / 2 : ℝ) then (0 : ℝ) else pTail) a b h
        = (3 / 2 : ℝ) * pTail := by
  have hAbove : BddAbove ((fun y : ℝ => y) '' Set.Icc a b) :=
    (isCompact_Icc.image continuous_id).bddAbove
  have hBelow : BddBelow ((fun y : ℝ => y) '' Set.Icc a b) :=
    (isCompact_Icc.image continuous_id).bddBelow
  obtain ⟨h, hv⟩ := rsIntegral_singleJumpStep_exists
    (f := fun y : ℝ => y) (a := a) (b := b) (c := (3 / 2 : ℝ)) (u₁ := 0) (u₂ := pTail)
    (le_of_lt (lt_trans ha (by linarith))) (by linarith) (le_of_lt hb) pTail_pos hAbove hBelow
    continuousAt_id
  refine ⟨h, ?_⟩
  rw [hv]; simp

/-- For `a < -3/2 < 3/2 < b`, `rsIntegral id α₁ a b = 0`. -/
theorem rsIntegral_id_alpha1_trunc_eq_zero {a b : ℝ}
    (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    ∃ h : RSIntegrable (fun y => y) (alpha1 pTail) a b,
      rsIntegral (fun y => y) (alpha1 pTail) a b h = 0 := by
  obtain ⟨hL, hLv⟩ := rsIntegral_leftAtom ha hb
  obtain ⟨hR, hRv⟩ := rsIntegral_rightAtom ha hb
  -- α₁ = leftAtom + rightAtom (definitionally).
  have hadd := rsIntegral_integrator_add hL hR
  have hint := rsIntegrable_integrator_add hL hR
  -- `alpha1 pTail = fun x => leftAtom x + rightAtom x` (defeq).
  refine ⟨hint, ?_⟩
  show rsIntegral (fun y => y)
      (fun x => (if x < (-3 / 2 : ℝ) then (0 : ℝ) else pTail)
        + (if x < (3 / 2 : ℝ) then (0 : ℝ) else pTail)) a b hint = 0
  rw [hadd, hLv, hRv]; ring

/-! ### Generic improper-convergence packaging from a truncation-zero hypothesis. -/

/-- If `α` is monotone and every truncated integral `rsTruncIntegral id α a b` with
`a < -3/2 < 3/2 < b` is `0`, then `ImproperRSConvergesTo id α 0`. -/
theorem improperRS_zero_of_trunc_zero {α : ℝ → ℝ} (hα : Monotone α)
    (htrunc : ∀ a b : ℝ, a < (-3 / 2 : ℝ) → (3 / 2 : ℝ) < b →
      rsTruncIntegral (fun y => y) α a b = 0) :
    ImproperRSConvergesTo (fun y => y) α 0 := by
  -- Finiteness on every strict interval.
  have hRS : ∀ ⦃a b : ℝ⦄, a < b → RSIntegrable (fun y => y) α a b :=
    fun a b hab => rsIntegrable_id_of_monotone hα hab
  have hFinite := thm_7_9_eventually_rsIntegrable_of_forall hRS
  -- Symmetric truncation `v n = rsTruncIntegral id α (-n) n` is eventually `0`.
  have hSymm : Tendsto (fun n : ℕ => rsTruncIntegral (fun y => y) α (-(n : ℝ)) (n : ℝ))
      atTop (nhds 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (htrunc (-(n : ℝ)) (n : ℝ) (by linarith) (by linarith)).symm
  -- Tail control: for `p` far out, both truncated values are `0`.
  have hctrl : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∀ᶠ p : ℝ × ℝ in improperRSFilter,
        ∃ n : ℕ, N ≤ n ∧
          dist (rsTruncIntegral (fun y => y) α p.1 p.2)
            (rsTruncIntegral (fun y => y) α (-(n : ℝ)) (n : ℝ)) < ε := by
    intro ε hε N
    -- Eventually `p.1 < -3/2` and `p.2 > 3/2` under the double filter.
    have hp1 : ∀ᶠ p : ℝ × ℝ in improperRSFilter, p.1 < (-3 / 2 : ℝ) ∧ (3 / 2 : ℝ) < p.2 := by
      unfold improperRSFilter
      rw [Filter.eventually_inf_principal, Filter.eventually_prod_iff]
      refine ⟨fun x : ℝ => x < (-3 / 2 : ℝ), ?_, fun y : ℝ => (3 / 2 : ℝ) < y, ?_, ?_⟩
      · exact Filter.eventually_atBot.2 ⟨(-2 : ℝ), fun x hx => by linarith⟩
      · exact Filter.eventually_atTop.2 ⟨(2 : ℝ), fun y hy => by linarith⟩
      · intro x hx y hy _; exact ⟨hx, hy⟩
    filter_upwards [hp1] with p hp
    refine ⟨N + 2, by omega, ?_⟩
    rw [htrunc p.1 p.2 hp.1 hp.2,
        htrunc (-(((N : ℕ) + 2 : ℕ) : ℝ)) (((N : ℕ) + 2 : ℕ) : ℝ)
          (by push_cast; linarith) (by push_cast; linarith)]
    simpa using hε
  exact thm_7_9_improperRSConvergesTo_of_symmetric_tail_control hFinite hSymm hctrl

/-- `rsTruncIntegral id α₁ a b = 0` for `a < -3/2 < 3/2 < b`. -/
theorem rsTrunc_id_alpha1_zero {a b : ℝ}
    (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    rsTruncIntegral (fun y => y) (alpha1 pTail) a b = 0 := by
  obtain ⟨h, hv⟩ := rsIntegral_id_alpha1_trunc_eq_zero ha hb
  rw [rsTruncIntegral, dif_pos h]; exact hv

theorem rsTrunc_id_alpha2_zero {a b : ℝ}
    (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    rsTruncIntegral (fun y => y) (alpha2 pTail) a b = 0 := by
  obtain ⟨h, hv⟩ := rsIntegral_id_alpha2_trunc_eq_zero ha hb
  rw [rsTruncIntegral, dif_pos h]; exact hv

/-! ### α₁ monotonicity and the two improper convergences. -/

/-- `α₁` (with `p = pTail ≥ 0`) is monotone. -/
theorem alpha1_monotone : Monotone (alpha1 pTail) := by
  have hp : (0 : ℝ) ≤ pTail := pTail_nonneg
  intro x y hxy
  simp only [alpha1]
  have h1 : (if x < (-3 / 2 : ℝ) then (0 : ℝ) else pTail)
      ≤ (if y < (-3 / 2 : ℝ) then (0 : ℝ) else pTail) := by
    split_ifs with hx hy hy <;> first | rfl | linarith
  have h2 : (if x < (3 / 2 : ℝ) then (0 : ℝ) else pTail)
      ≤ (if y < (3 / 2 : ℝ) then (0 : ℝ) else pTail) := by
    split_ifs with hx hy hy <;> first | rfl | linarith
  linarith

/-- Obligation (3c): `ImproperRSConvergesTo id α₁ 0`. -/
theorem alpha1_improperRS_zero :
    ImproperRSConvergesTo (fun y => y) (alpha1 pTail) 0 :=
  improperRS_zero_of_trunc_zero alpha1_monotone
    (fun _ _ ha hb => rsTrunc_id_alpha1_zero ha hb)

/-- Obligation (3d): `ImproperRSConvergesTo id α₂ 0`. -/
theorem alpha2_improperRS_zero :
    ImproperRSConvergesTo (fun y => y) (alpha2 pTail) 0 :=
  improperRS_zero_of_trunc_zero alpha2_monotone
    (fun _ _ ha hb => rsTrunc_id_alpha2_zero ha hb)

/-! ### Whole-line split `F_Y = α₁ + α₂` (obligation 3e): third convergence. -/

/-- `α₁ + α₂` is monotone. -/
theorem alpha_sum_monotone :
    Monotone (fun y => alpha1 pTail y + alpha2 pTail y) :=
  alpha1_monotone.add alpha2_monotone

/-- `rsIntegral id (α₁+α₂) a b = 0` for `a < -3/2 < 3/2 < b` (thm_1_3 additivity). -/
theorem rsIntegral_id_alpha_sum_trunc_eq_zero {a b : ℝ}
    (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    ∃ h : RSIntegrable (fun y => y) (fun y => alpha1 pTail y + alpha2 pTail y) a b,
      rsIntegral (fun y => y) (fun y => alpha1 pTail y + alpha2 pTail y) a b h = 0 := by
  obtain ⟨h1, hv1⟩ := rsIntegral_id_alpha1_trunc_eq_zero ha hb
  obtain ⟨h2, hv2⟩ := rsIntegral_id_alpha2_trunc_eq_zero ha hb
  refine ⟨rsIntegrable_integrator_add h1 h2, ?_⟩
  rw [rsIntegral_integrator_add h1 h2, hv1, hv2]; ring

theorem rsTrunc_id_alpha_sum_zero {a b : ℝ}
    (ha : a < (-3 / 2 : ℝ)) (hb : (3 / 2 : ℝ) < b) :
    rsTruncIntegral (fun y => y) (fun y => alpha1 pTail y + alpha2 pTail y) a b = 0 := by
  obtain ⟨h, hv⟩ := rsIntegral_id_alpha_sum_trunc_eq_zero ha hb
  rw [rsTruncIntegral, dif_pos h]; exact hv

/-- Obligation (3e): the whole-line `F_Y = α₁ + α₂` improper RS integral converges to `0`. -/
theorem alpha_sum_improperRS_zero :
    ImproperRSConvergesTo (fun y => y) (fun y => alpha1 pTail y + alpha2 pTail y) 0 :=
  improperRS_zero_of_trunc_zero alpha_sum_monotone
    (fun _ _ ha hb => rsTrunc_id_alpha_sum_zero ha hb)

/-! ### CDF decomposition `F_Y = α₁ + α₂` (obligation 3b). -/

/-- Left tail: for `y < -3/2`, `saturatedGaussianLaw (Iic y) = 0`. -/
theorem law_Iic_eq_zero_of_lt {y : ℝ} (hy : y < (-3 / 2 : ℝ)) :
    saturatedGaussianLaw (Set.Iic y) = 0 := by
  rw [saturatedGaussianLaw, Measure.map_apply measurable_saturationMap measurableSet_Iic]
  have hpre : saturationMap ⁻¹' Set.Iic y = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hmem : saturationMap x ∈ Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ) := saturationMap_mem_interval x
    have : saturationMap x ≤ y := hx
    linarith [hmem.1]
  rw [hpre]; simp

/-- Right tail: for `3/2 ≤ y`, `saturatedGaussianLaw (Iic y) = 1`. -/
theorem law_Iic_eq_one_of_ge {y : ℝ} (hy : (3 / 2 : ℝ) ≤ y) :
    saturatedGaussianLaw (Set.Iic y) = 1 := by
  rw [saturatedGaussianLaw, Measure.map_apply measurable_saturationMap measurableSet_Iic]
  have hpre : saturationMap ⁻¹' Set.Iic y = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hmem : saturationMap x ∈ Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ) := saturationMap_mem_interval x
    show saturationMap x ≤ y
    linarith [hmem.2]
  rw [hpre]
  rw [show standardGaussianLaw = ProbabilityTheory.gaussianReal 0 1 from rfl] at *
  exact measure_univ

/-- The left atom mass equals `pTail` (as ENNReal). -/
theorem law_left_atom_eq : saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ)
    = ENNReal.ofReal pTail := by
  rw [saturatedGaussianLaw_left_atom]
  have hnegeq : (Set.Iic (-3 / 2 : ℝ)) = (Set.Iic (-(3 / 2 : ℝ))) := by norm_num
  rw [hnegeq, standardGaussianLaw_Iic_neg_eq_Ici]
  rw [pTail_eq_integral_Ici, standardGaussianLaw_apply]

/-- The right atom mass equals `pTail` (as ENNReal). -/
theorem law_right_atom_eq : saturatedGaussianLaw ({(3 / 2 : ℝ)} : Set ℝ)
    = ENNReal.ofReal pTail := by
  rw [saturatedGaussianLaw_right_atom, pTail_eq_integral_Ici, standardGaussianLaw_apply]

/-- `law (Iio (-3/2)) = 0` (nothing maps strictly below `-3/2`). -/
theorem law_Iio_left_eq_zero : saturatedGaussianLaw (Set.Iio (-3 / 2 : ℝ)) = 0 := by
  rw [saturatedGaussianLaw, Measure.map_apply measurable_saturationMap measurableSet_Iio]
  have hpre : saturationMap ⁻¹' Set.Iio (-3 / 2 : ℝ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hmem : saturationMap x ∈ Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ) := saturationMap_mem_interval x
    have : saturationMap x < (-3 / 2 : ℝ) := hx
    linarith [hmem.1]
  rw [hpre]; simp

/-- `law (Iic (-3/2)) = law {-3/2}`. -/
theorem law_Iic_left_eq_atom :
    saturatedGaussianLaw (Set.Iic (-3 / 2 : ℝ)) = saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ) := by
  have hunion : Set.Iic (-3 / 2 : ℝ) = Set.Iio (-3 / 2 : ℝ) ∪ {(-3 / 2 : ℝ)} := by
    ext x; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · intro h; rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h | h)
      · exact le_of_lt h
      · exact le_of_eq h
  have hdisj : Disjoint (Set.Iio (-3 / 2 : ℝ)) ({(-3 / 2 : ℝ)} : Set ℝ) := by
    simp
  rw [hunion, measure_union hdisj (measurableSet_singleton _),
    law_Iio_left_eq_zero, zero_add]

/-- Interior measure agreement: for `s ⊆ Ioo (-3/2) (3/2)`,
`law s = standardGaussianLaw s`. -/
theorem law_eq_standard_on_interior {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Set.Ioo (-3 / 2 : ℝ) (3 / 2 : ℝ)) :
    saturatedGaussianLaw s = standardGaussianLaw s := by
  have hrestrict := saturatedGaussianLaw_restrict_interior_eq_standard
  have hsub' : s ⊆ saturationInterior := hsub
  calc saturatedGaussianLaw s
      = saturatedGaussianLaw.restrict saturationInterior s := by
        rw [Measure.restrict_apply hs, Set.inter_eq_left.mpr hsub']
    _ = standardGaussianLaw.restrict saturationInterior s := by rw [hrestrict]
    _ = standardGaussianLaw s := by
        rw [Measure.restrict_apply hs, Set.inter_eq_left.mpr hsub']

/-- Interior CDF piece: for `-3/2 ≤ y < 3/2`,
`law (Ioc (-3/2) y) = ENNReal.ofReal (∫_{-3/2}^y φ)`. -/
theorem law_Ioc_interior {y : ℝ} (hlo : (-3 / 2 : ℝ) ≤ y) (hhi : y < (3 / 2 : ℝ)) :
    saturatedGaussianLaw (Set.Ioc (-3 / 2 : ℝ) y)
      = ENNReal.ofReal (∫ t in (-3 / 2 : ℝ)..y, standardNormalKernel t) := by
  have hsub : Set.Ioc (-3 / 2 : ℝ) y ⊆ Set.Ioo (-3 / 2 : ℝ) (3 / 2 : ℝ) := by
    intro x hx
    exact ⟨hx.1, lt_of_le_of_lt hx.2 hhi⟩
  rw [law_eq_standard_on_interior measurableSet_Ioc hsub, standardGaussianLaw_apply]
  congr 1
  rw [intervalIntegral.integral_of_le hlo]

/-- Middle case: for `-3/2 ≤ y`, `law (Iic y) = law {-3/2} + law (Ioc (-3/2) y)`. -/
theorem law_Iic_mid_split {y : ℝ} (hlo : (-3 / 2 : ℝ) ≤ y) :
    saturatedGaussianLaw (Set.Iic y)
      = saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ)
        + saturatedGaussianLaw (Set.Ioc (-3 / 2 : ℝ) y) := by
  have hunion : Set.Iic y = Set.Iic (-3 / 2 : ℝ) ∪ Set.Ioc (-3 / 2 : ℝ) y := by
    rw [Set.Iic_union_Ioc_eq_Iic hlo]
  have hdisj : Disjoint (Set.Iic (-3 / 2 : ℝ)) (Set.Ioc (-3 / 2 : ℝ) y) :=
    Set.Iic_disjoint_Ioc (le_refl _)
  rw [hunion, measure_union hdisj measurableSet_Ioc, law_Iic_left_eq_atom]

/-- **CDF decomposition (obligation 3b):**
`(F_Y y).toReal = α₁(y) + α₂(y)` for all `y`, with `p = pTail`. -/
theorem saturatedGaussianCDF_decomposition (y : ℝ) :
    (saturatedGaussianCDF y).toReal = alpha1 pTail y + alpha2 pTail y := by
  rw [saturatedGaussianCDF]
  rcases lt_trichotomy y (-3 / 2 : ℝ) with hlt | heq | hgt
  · -- y < -3/2
    rw [law_Iic_eq_zero_of_lt hlt]
    have hα1 : alpha1 pTail y = 0 := by
      simp only [alpha1]
      rw [if_pos hlt, if_pos (by linarith : y < (3 / 2 : ℝ))]; ring
    have hα2 : alpha2 pTail y = 0 := by simp only [alpha2]; rw [if_pos hlt]
    rw [hα1, hα2]; simp
  · -- y = -3/2
    subst heq
    rw [law_Iic_mid_split (le_refl _)]
    have hIoc : saturatedGaussianLaw (Set.Ioc (-3 / 2 : ℝ) (-3 / 2 : ℝ)) = 0 := by
      rw [Set.Ioc_self]; simp
    rw [hIoc, add_zero, law_left_atom_eq, ENNReal.toReal_ofReal pTail_nonneg]
    have hα1 : alpha1 pTail (-3 / 2 : ℝ) = pTail := by
      simp only [alpha1]
      rw [if_neg (lt_irrefl _), if_pos (by norm_num : (-3 / 2 : ℝ) < (3 / 2 : ℝ))]; ring
    have hα2 : alpha2 pTail (-3 / 2 : ℝ) = 0 := by
      simp only [alpha2]
      rw [if_neg (lt_irrefl _), if_pos (by norm_num : (-3 / 2 : ℝ) < (3 / 2 : ℝ))]
      simp [intervalIntegral.integral_same]
    rw [hα1, hα2]; ring
  · -- y > -3/2: sub-split on y < 3/2 vs y ≥ 3/2
    rcases lt_or_ge y (3 / 2 : ℝ) with hmid | hright
    · -- -3/2 < y < 3/2
      have hInt : (0:ℝ) ≤ ∫ t in (-3 / 2 : ℝ)..y, standardNormalKernel t := by
        rw [intervalIntegral.integral_of_le (le_of_lt hgt)]
        exact setIntegral_nonneg measurableSet_Ioc (fun x _ => standardNormalKernel_nonneg x)
      rw [law_Iic_mid_split (le_of_lt hgt), law_left_atom_eq,
        law_Ioc_interior (le_of_lt hgt) hmid,
        ← ENNReal.ofReal_add pTail_nonneg hInt,
        ENNReal.toReal_ofReal (by linarith [pTail_nonneg])]
      have hα1 : alpha1 pTail y = pTail := by
        simp only [alpha1]
        rw [if_neg (by linarith), if_pos hmid]; ring
      have hα2 : alpha2 pTail y = ∫ t in (-3 / 2 : ℝ)..y, standardNormalKernel t := by
        simp only [alpha2]
        rw [if_neg (by linarith), if_pos hmid]
      rw [hα1, hα2]
    · -- y ≥ 3/2
      rw [law_Iic_eq_one_of_ge hright]
      have hα1 : alpha1 pTail y = 2 * pTail := by
        simp only [alpha1]
        rw [if_neg (by linarith), if_neg (by linarith)]; ring
      have hα2 : alpha2 pTail y = 1 - 2 * pTail := by
        simp only [alpha2]
        rw [if_neg (by linarith), if_neg (by linarith)]
      rw [hα1, hα2]; simp

/-! ### Final assembly: `E[Y] = 0` via the improper RS route. -/

/-- **Example 1.3.2 (exported).**  For the saturated Gaussian `Y` of Example 1.2.1,
with `p = pTail = P(Z > 3/2)`, the cdf decomposes as `F_Y = α₁ + α₂`
(`saturatedGaussianCDF_decomposition`), and the mean `E[Y]`, computed as the
improper Riemann–Stieltjes integral `∫_{-∞}^{∞} y d(α₁+α₂)`, equals `0`:

* both `∫ y dα₁` and `∫ y dα₂` converge (via Definition 1.4) to `0` by symmetry;
* their whole-line sum converges to `0`;
* the third value `0` is the source's `E[Y] = 0`, derived — not assumed. -/
theorem ex_1_3_2 :
    (∀ y : ℝ, (saturatedGaussianCDF y).toReal = alpha1 pTail y + alpha2 pTail y) ∧
    ImproperRSConvergesTo (fun y => y) (alpha1 pTail) 0 ∧
    ImproperRSConvergesTo (fun y => y) (alpha2 pTail) 0 ∧
    ImproperRSConvergesTo (fun y => y) (fun y => alpha1 pTail y + alpha2 pTail y) 0 :=
  ⟨saturatedGaussianCDF_decomposition,
    alpha1_improperRS_zero,
    alpha2_improperRS_zero,
    alpha_sum_improperRS_zero⟩

/-- The mean of `Y` is `0`, exhibited as the improper RS value of `id` against the
actual cdf decomposition `α₁ + α₂`. -/
theorem ex_1_3_2_mean_zero :
    ImproperRSIntegrable (fun y => y) (fun y => alpha1 pTail y + alpha2 pTail y) ∧
    ImproperRSConvergesTo (fun y => y) (fun y => alpha1 pTail y + alpha2 pTail y) 0 :=
  ⟨⟨0, alpha_sum_improperRS_zero⟩, alpha_sum_improperRS_zero⟩

end

end Ex132

/-- Top-level export for Example 1.3.2 (see `Ex132.ex_1_3_2`). -/
theorem ex_1_3_2 :
    (∀ y : ℝ, (saturatedGaussianCDF y).toReal
        = Ex132.alpha1 Ex132.pTail y + Ex132.alpha2 Ex132.pTail y) ∧
    ImproperRSConvergesTo (fun y => y) (Ex132.alpha1 Ex132.pTail) 0 ∧
    ImproperRSConvergesTo (fun y => y) (Ex132.alpha2 Ex132.pTail) 0 ∧
    ImproperRSConvergesTo (fun y => y)
      (fun y => Ex132.alpha1 Ex132.pTail y + Ex132.alpha2 Ex132.pTail y) 0 :=
  Ex132.ex_1_3_2
