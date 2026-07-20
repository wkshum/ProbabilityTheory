import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ProbabilityTheory.chapter_06.def_6_5
import ProbabilityTheory.chapter_06.def_6_6
import ProbabilityTheory.chapter_06.thm_6_6

/-! # Theorem 6.7: linearity of the Lebesgue integral -/

open MeasureTheory

namespace Thm67Support

theorem posPart_measurable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → EReal}
    (hXm : Measurable X) :
    Measurable (Def65Support.posPart X) := by
  change Measurable (fun ω => (X ω).toENNReal)
  exact hXm.ereal_toENNReal

theorem negPart_measurable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → EReal}
    (hXm : Measurable X) :
    Measurable (Def65Support.negPart X) := by
  change Measurable (fun ω => (-X ω).toENNReal)
  exact hXm.neg.ereal_toENNReal

theorem posPart_ae_lt_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∀ᵐ ω ∂μ, Def65Support.posPart X ω < ⊤ := by
  exact MeasureTheory.ae_lt_top (posPart_measurable hXm) (ne_of_lt hX.1)

theorem negPart_ae_lt_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∀ᵐ ω ∂μ, Def65Support.negPart X ω < ⊤ := by
  exact MeasureTheory.ae_lt_top (negPart_measurable hXm) (ne_of_lt hX.2)

theorem ae_ne_top {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
  filter_upwards [posPart_ae_lt_top hXm hX] with ω hω
  intro htop
  exact (ne_of_lt hω) ((EReal.toENNReal_eq_top_iff).2 htop)

theorem ae_ne_bot {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∀ᵐ ω ∂μ, X ω ≠ ⊥ := by
  filter_upwards [negPart_ae_lt_top hXm hX] with ω hω
  intro hbot
  have hnegTop : Def65Support.negPart X ω = ⊤ := by
    simp [Def65Support.negPart, hbot]
  exact (ne_of_lt hω) hnegTop

theorem toReal_eq_pos_sub_neg_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∀ᵐ ω ∂μ,
      (X ω).toReal =
        (Def65Support.posPart X ω).toReal - (Def65Support.negPart X ω).toReal := by
  filter_upwards [ae_ne_top hXm hX, ae_ne_bot hXm hX] with ω hxTop hxBot
  have hrepr :
      (((Def65Support.posPart X ω : ENNReal) : EReal) -
          ((Def65Support.negPart X ω : ENNReal) : EReal)) = X ω := by
    lift (X ω) to ℝ using ⟨hxTop, hxBot⟩ with x hx
    rw [Def65Support.posPart, Def65Support.negPart, ← hx]
    change
      (((x.toNNReal : ENNReal) : EReal) -
        (((-x).toNNReal : ENNReal) : EReal)) = (x : EReal)
    exact (EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal x).symm
  have hposTop : Def65Support.posPart X ω ≠ ⊤ := by
    rw [Def65Support.posPart, EReal.toENNReal_ne_top_iff]
    exact hxTop
  have hnegTop : Def65Support.negPart X ω ≠ ⊤ := by
    rw [Def65Support.negPart, EReal.toENNReal_ne_top_iff]
    simpa using hxBot
  have hposTop' : (((Def65Support.posPart X ω : ENNReal) : EReal)) ≠ ⊤ := by
    simpa using hposTop
  have hnegTop' : (((Def65Support.negPart X ω : ENNReal) : EReal)) ≠ ⊤ := by
    simpa using hnegTop
  calc
    (X ω).toReal =
        ((((Def65Support.posPart X ω : ENNReal) : EReal) -
            ((Def65Support.negPart X ω : ENNReal) : EReal))).toReal := by
          rw [hrepr]
    _ = (Def65Support.posPart X ω).toReal - (Def65Support.negPart X ω).toReal := by
      simpa using
        (EReal.toReal_sub
          (x := ((Def65Support.posPart X ω : ENNReal) : EReal))
          (y := ((Def65Support.negPart X ω : ENNReal) : EReal))
          hposTop' (by simp) hnegTop' (by simp))

theorem ennreal_ofReal_abs_toReal_eq_pos_add_neg {x : EReal} (hxTop : x ≠ ⊤) (hxBot : x ≠ ⊥) :
    ENNReal.ofReal |x.toReal| = x.toENNReal + (-x).toENNReal := by
  lift x to ℝ using ⟨hxTop, hxBot⟩
  simpa using
    (show ENNReal.ofReal |x| = (x : EReal).toENNReal + (-(x : EReal)).toENNReal by
      rw [← max_zero_add_max_neg_zero_eq_abs_self x, ENNReal.ofReal_add]
      · simp
      · exact le_max_right x (0 : ℝ)
      · exact le_max_right (-x) (0 : ℝ))

theorem abs_toReal_eq_pos_add_neg_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∀ᵐ ω ∂μ,
      ENNReal.ofReal |(X ω).toReal| = Def65Support.posPart X ω + Def65Support.negPart X ω := by
  filter_upwards [ae_ne_top hXm hX, ae_ne_bot hXm hX] with ω hxTop hxBot
  simpa [Def65Support.posPart, Def65Support.negPart] using
    ennreal_ofReal_abs_toReal_eq_pos_add_neg hxTop hxBot

theorem integrable_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    Integrable (fun ω => (X ω).toReal) μ := by
  have hPosInt :
      Integrable (fun ω => (Def65Support.posPart X ω).toReal) μ :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top
      (posPart_measurable hXm).aemeasurable (ne_of_lt hX.1)
  have hNegInt :
      Integrable (fun ω => (Def65Support.negPart X ω).toReal) μ :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top
      (negPart_measurable hXm).aemeasurable (ne_of_lt hX.2)
  have hSub :
      Integrable (fun ω =>
        (Def65Support.posPart X ω).toReal - (Def65Support.negPart X ω).toReal) μ :=
    hPosInt.sub hNegInt
  refine hSub.congr ?_
  filter_upwards [toReal_eq_pos_sub_neg_ae hXm hX] with ω hω
  exact hω.symm

theorem integral_posPart_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∫ ω, (Def65Support.posPart X ω).toReal ∂μ = (Def65Support.posLIntegral μ X).toReal := by
  exact MeasureTheory.integral_toReal
    (posPart_measurable hXm).aemeasurable
    (MeasureTheory.ae_lt_top (posPart_measurable hXm) (ne_of_lt hX.1))

theorem integral_negPart_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    ∫ ω, (Def65Support.negPart X ω).toReal ∂μ = (Def65Support.negLIntegral μ X).toReal := by
  exact MeasureTheory.integral_toReal
    (negPart_measurable hXm).aemeasurable
    (MeasureTheory.ae_lt_top (negPart_measurable hXm) (ne_of_lt hX.2))

theorem textbookValue_eq_integral_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    (((Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal)).toReal) =
      ∫ ω, (X ω).toReal ∂μ := by
  have hPosInt := integral_posPart_toReal hXm hX
  have hNegInt := integral_negPart_toReal hXm hX
  have hInt :
      ∫ ω, (X ω).toReal ∂μ =
        (Def65Support.posLIntegral μ X).toReal - (Def65Support.negLIntegral μ X).toReal := by
    calc
      ∫ ω, (X ω).toReal ∂μ =
          ∫ ω,
            ((Def65Support.posPart X ω).toReal - (Def65Support.negPart X ω).toReal) ∂μ := by
            apply integral_congr_ae
            exact toReal_eq_pos_sub_neg_ae hXm hX
      _ = (∫ ω, (Def65Support.posPart X ω).toReal ∂μ) -
            ∫ ω, (Def65Support.negPart X ω).toReal ∂μ := by
            have hPosIntegrable :
                Integrable (fun ω => (Def65Support.posPart X ω).toReal) μ :=
              MeasureTheory.integrable_toReal_of_lintegral_ne_top
                (posPart_measurable hXm).aemeasurable (ne_of_lt hX.1)
            have hNegIntegrable :
                Integrable (fun ω => (Def65Support.negPart X ω).toReal) μ :=
              MeasureTheory.integrable_toReal_of_lintegral_ne_top
                (negPart_measurable hXm).aemeasurable (ne_of_lt hX.2)
            simpa using integral_sub hPosIntegrable hNegIntegrable
      _ = (Def65Support.posLIntegral μ X).toReal - (Def65Support.negLIntegral μ X).toReal := by
            rw [hPosInt, hNegInt]
  have hDiff :
      (((Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal)).toReal) =
        (Def65Support.posLIntegral μ X).toReal - (Def65Support.negLIntegral μ X).toReal := by
    simpa using
      (EReal.toReal_sub
        (x := ((Def65Support.posLIntegral μ X : ENNReal) : EReal))
        (y := ((Def65Support.negLIntegral μ X : ENNReal) : EReal))
        (by simpa using (ne_of_lt hX.1 : Def65Support.posLIntegral μ X ≠ ⊤)) (by simp)
        (by simpa using (ne_of_lt hX.2 : Def65Support.negLIntegral μ X ≠ ⊤)) (by simp))
  rw [hDiff, hInt]

theorem textbookIntegral_eq_some_toRealIntegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    textbookIntegral μ X = some (((∫ ω, (X ω).toReal ∂μ : ℝ)) : EReal) := by
  have hUndefined :
      ¬ (Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤) := by
    intro hBoth
    exact (ne_of_lt hX.1) hBoth.1
  unfold textbookIntegral
  simp [hUndefined]
  have hVal :
      (((Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal)).toReal) =
        ∫ ω, (X ω).toReal ∂μ :=
    textbookValue_eq_integral_toReal hXm hX
  have hPosNeTop : (Def65Support.posLIntegral μ X : EReal) ≠ ⊤ := by
    simpa using (ne_of_lt hX.1 : Def65Support.posLIntegral μ X ≠ ⊤)
  have hNegNeTop : (Def65Support.negLIntegral μ X : EReal) ≠ ⊤ := by
    simpa using (ne_of_lt hX.2 : Def65Support.negLIntegral μ X ≠ ⊤)
  have hFinite :
      (((Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal)).toReal : EReal) =
        ((Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal)) := by
    lift (Def65Support.posLIntegral μ X) to NNReal using (ne_of_lt hX.1) with p hp
    lift (Def65Support.negLIntegral μ X) to NNReal using (ne_of_lt hX.2) with n hn
    rcases le_total n p with hnp | hpn
    · have hEq :
          (((p : ENNReal) : EReal) - ((n : ENNReal) : EReal)) =
            (((p - n : NNReal) : ℝ) : EReal) := by
        rw [show (((p : ENNReal) : EReal)) = ((p : ℝ) : EReal) by rfl]
        rw [show (((n : ENNReal) : EReal)) = ((n : ℝ) : EReal) by rfl]
        rw [← EReal.coe_sub, NNReal.coe_sub hnp]
      rw [hEq]
      simp
    · have hEqReal : (p : ℝ) - (n : ℝ) = -((n - p : NNReal) : ℝ) := by
        rw [NNReal.coe_sub hpn]
        linarith
      have hEq :
          (((p : ENNReal) : EReal) - ((n : ENNReal) : EReal)) =
            -((((n - p : NNReal) : ℝ) : EReal)) := by
        rw [show (((p : ENNReal) : EReal)) = ((p : ℝ) : EReal) by rfl]
        rw [show (((n : ENNReal) : EReal)) = ((n : ℝ) : EReal) by rfl]
        rw [← EReal.coe_sub]
        exact_mod_cast hEqReal
      rw [hEq]
      simp
  rw [← hVal, hFinite]

theorem textbookIntegrable_neg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hX : textbookIntegrable μ X) :
    textbookIntegrable μ (fun ω => -X ω) := by
  constructor
  · simpa [textbookIntegrable, Def65Support.posLIntegral, Def65Support.negLIntegral,
      Def65Support.posPart, Def65Support.negPart]
      using hX.2
  · simpa [textbookIntegrable, Def65Support.posLIntegral, Def65Support.negLIntegral,
      Def65Support.posPart, Def65Support.negPart]
      using hX.1

theorem textbookIntegrable_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → EReal} (hXm : Measurable X) (_hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) :
    textbookIntegrable μ (fun ω => X ω + Y ω) := by
  constructor
  · have hPosLe :
        (fun ω => Def65Support.posPart (fun ω => X ω + Y ω) ω) ≤
          fun ω => Def65Support.posPart X ω + Def65Support.posPart Y ω := by
      intro ω
      simpa [Def65Support.posPart] using (EReal.toENNReal_add_le (x := X ω) (y := Y ω))
    have hPosRhs :
        ∫⁻ a, Def65Support.posPart X a + Def65Support.posPart Y a ∂μ < ⊤ := by
      rw [MeasureTheory.lintegral_add_left (posPart_measurable hXm)]
      simpa [Def65Support.posLIntegral] using ENNReal.add_lt_top.mpr ⟨hX.1, hY.1⟩
    exact lt_of_le_of_lt (lintegral_mono hPosLe) hPosRhs
  · have hNegLe :
        (fun ω => Def65Support.negPart (fun ω => X ω + Y ω) ω) ≤
          fun ω => Def65Support.negPart X ω + Def65Support.negPart Y ω := by
      intro ω
      by_cases hbotTop : X ω = ⊥ ∧ Y ω = ⊤
      · simp [Def65Support.negPart, hbotTop.1, hbotTop.2]
      · by_cases htopBot : X ω = ⊤ ∧ Y ω = ⊥
        · simp [Def65Support.negPart, htopBot.1, htopBot.2]
        · have h1 : X ω ≠ ⊥ ∨ Y ω ≠ ⊤ := by
            by_cases hxBot : X ω = ⊥
            · right
              intro hyTop
              exact hbotTop ⟨hxBot, hyTop⟩
            · exact Or.inl hxBot
          have h2 : X ω ≠ ⊤ ∨ Y ω ≠ ⊥ := by
            by_cases hxTop : X ω = ⊤
            · right
              intro hyBot
              exact htopBot ⟨hxTop, hyBot⟩
            · exact Or.inl hxTop
          have htmp : (-X ω + -Y ω).toENNReal ≤ (-X ω).toENNReal + (-Y ω).toENNReal :=
            EReal.toENNReal_add_le
          have hnegEq : -(X ω + Y ω) = -X ω - Y ω := EReal.neg_add h1 h2
          simpa [Def65Support.negPart, hnegEq, sub_eq_add_neg] using htmp
    have hNegRhs :
        ∫⁻ a, Def65Support.negPart X a + Def65Support.negPart Y a ∂μ < ⊤ := by
      rw [MeasureTheory.lintegral_add_left (negPart_measurable hXm)]
      simpa [Def65Support.negLIntegral] using ENNReal.add_lt_top.mpr ⟨hX.2, hY.2⟩
    exact lt_of_le_of_lt (lintegral_mono hNegLe) hNegRhs

theorem textbookIntegrable_smul_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (_hXm : Measurable X) (hX : textbookIntegrable μ X)
    {α : ℝ} (hα : 0 ≤ α) :
    textbookIntegrable μ (fun ω => ((α : EReal) * X ω)) := by
  have hαE : 0 ≤ (α : EReal) := by exact_mod_cast hα
  constructor
  · have hPoint :
        (fun ω => Def65Support.posPart (fun ω => ((α : EReal) * X ω)) ω) =
          fun ω => ENNReal.ofReal α * Def65Support.posPart X ω := by
      funext ω
      simpa [Def65Support.posPart, hα, mul_comm, mul_left_comm, mul_assoc] using
        (EReal.toENNReal_mul (x := (α : EReal)) (y := X ω) hαE)
    calc
      Def65Support.posLIntegral μ (fun ω => ((α : EReal) * X ω))
          = ∫⁻ ω, ENNReal.ofReal α * Def65Support.posPart X ω ∂μ := by
              unfold Def65Support.posLIntegral
              rw [hPoint]
      _ = ENNReal.ofReal α * Def65Support.posLIntegral μ X := by
              unfold Def65Support.posLIntegral
              exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal α)
                (Def65Support.posPart X) (by simp)
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hX.1
  · have hPoint :
        (fun ω => Def65Support.negPart (fun ω => ((α : EReal) * X ω)) ω) =
          fun ω => ENNReal.ofReal α * Def65Support.negPart X ω := by
      funext ω
      simpa [Def65Support.negPart, neg_mul, hα, mul_comm, mul_left_comm, mul_assoc] using
        (EReal.toENNReal_mul (x := (α : EReal)) (y := -X ω) hαE)
    calc
      Def65Support.negLIntegral μ (fun ω => ((α : EReal) * X ω))
          = ∫⁻ ω, ENNReal.ofReal α * Def65Support.negPart X ω ∂μ := by
              unfold Def65Support.negLIntegral
              rw [hPoint]
      _ = ENNReal.ofReal α * Def65Support.negLIntegral μ X := by
              unfold Def65Support.negLIntegral
              exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal α)
                (Def65Support.negPart X) (by simp)
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hX.2

theorem textbookIntegrable_smul_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) (α : ℝ) :
    textbookIntegrable μ (fun ω => ((α : EReal) * X ω)) := by
  by_cases hα : 0 ≤ α
  · exact textbookIntegrable_smul_nonneg hXm hX hα
  · have hNegX : textbookIntegrable μ (fun ω => -X ω) := textbookIntegrable_neg hX
    have hpos : 0 ≤ -α := by linarith
    have hScaled :
        textbookIntegrable μ (fun ω => (((-α : ℝ) : EReal) * (-X ω))) :=
      textbookIntegrable_smul_nonneg hXm.neg hNegX hpos
    have hEq : (fun ω => ((α : EReal) * X ω)) = fun ω => (((-α : ℝ) : EReal) * (-X ω)) := by
      funext ω
      have hα' : α = -(-α) := by linarith
      have hαE : (α : EReal) = -(((-α : ℝ) : EReal)) := by
        exact_mod_cast hα'
      have h1 : ((α : EReal) * X ω) = -((((-α : ℝ) : EReal) * X ω)) := by
        rw [hαE]
        exact EReal.neg_mul (((-α : ℝ) : EReal)) (X ω)
      have h2 : (((-α : ℝ) : EReal) * (-X ω)) = -((((-α : ℝ) : EReal) * X ω)) := by
        rw [mul_neg]
      calc
        ((α : EReal) * X ω) = -((((-α : ℝ) : EReal) * X ω)) := h1
        _ = (((-α : ℝ) : EReal) * (-X ω)) := h2.symm
    rw [hEq]
    exact hScaled

theorem toReal_add_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) :
    ∀ᵐ ω ∂μ, (X ω + Y ω).toReal = (X ω).toReal + (Y ω).toReal := by
  filter_upwards [ae_ne_top hXm hX, ae_ne_bot hXm hX, ae_ne_top hYm hY, ae_ne_bot hYm hY]
      with ω hxt hxb hyt hyb
  exact EReal.toReal_add hxt hxb hyt hyb

theorem textbookIntegrable_realCoe_of_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    textbookIntegrable μ (fun ω => (f ω : EReal)) := by
  have hMeasE : Measurable fun ω => ((f ω : ℝ) : EReal) := by
    fun_prop
  have hSum :
      (∫⁻ ω, (((f ω : ℝ) : EReal).toENNReal) ∂μ) +
        ∫⁻ ω, ((-((f ω : ℝ) : EReal)).toENNReal) ∂μ < ⊤ := by
    calc
      (∫⁻ ω, (((f ω : ℝ) : EReal).toENNReal) ∂μ) +
          ∫⁻ ω, ((-((f ω : ℝ) : EReal)).toENNReal) ∂μ
          = ∫⁻ ω,
              ((((f ω : ℝ) : EReal).toENNReal) +
                (-((f ω : ℝ) : EReal)).toENNReal) ∂μ := by
                  symm
                  exact MeasureTheory.lintegral_add_left (by
                    simpa using (Measurable.ereal_toENNReal hMeasE))
                    (fun ω => (-((f ω : ℝ) : EReal)).toENNReal)
      _ = ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ := by
          apply lintegral_congr_ae
          refine Filter.Eventually.of_forall ?_
          intro ω
          simpa using (ennreal_ofReal_abs_toReal_eq_pos_add_neg
            (x := ((f ω : ℝ) : EReal)) (by simp) (by simp)
            ).symm
      _ = ENNReal.ofReal (∫ ω, |f ω| ∂μ) := by
          symm
          exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf.norm
            (Filter.Eventually.of_forall (by intro ω; exact abs_nonneg (f ω)))
      _ < ⊤ := by simp
  have hAbs :
      Thm66Support.realAbsIntegral μ (fun ω => (f ω : EReal)) < ⊤ := by
    rw [Thm66Support.realAbsIntegral_eq_parts μ (fun ω => (f ω : EReal)) hMeasE]
    exact hSum
  have hIff := thm_6_6 μ (fun ω => (f ω : EReal)) hMeasE
  exact hIff.mpr (by simpa [Thm66Support.realAbsIntegral] using hAbs)

theorem complexTextbookIntegral_eq_some_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : Ω → ℂ} (_hZm : Measurable Z) (hZ : complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  exact _root_.complexTextbookIntegral_eq_some_integral μ Z hZ

end Thm67Support

/-- Compatibility wrapper retaining the existing Kenneth-facing signature.
The measurability hypothesis is unnecessary for the standard componentwise
integrability equivalence, but remains in the API for downstream callers. -/
theorem complexTextbookIntegrable_iff_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (_hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ Integrable Z μ :=
  complexTextbookIntegrable_iff_integrable_core μ Z

/--
Theorem 6.7, extended-real branch: integrability is preserved by addition and
real scalar multiplication, and the textbook optional integral is linear.
-/
theorem thm_6_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : Ω → EReal} (hXm : Measurable X) (hYm : Measurable Y)
    (hX : textbookIntegrable μ X) (hY : textbookIntegrable μ Y) (α : ℝ) :
    textbookIntegrable μ (fun ω => X ω + Y ω) ∧
      textbookIntegral μ (fun ω => X ω + Y ω) =
        Option.map₂ (fun x y => x + y) (textbookIntegral μ X) (textbookIntegral μ Y) ∧
      textbookIntegrable μ (fun ω => ((α : EReal) * X ω)) ∧
      textbookIntegral μ (fun ω => ((α : EReal) * X ω)) =
        Option.map (fun x => (α : EReal) * x) (textbookIntegral μ X) := by
  have hAddIntegrable := Thm67Support.textbookIntegrable_add hXm hYm hX hY
  have hAddMeas : Measurable fun ω => X ω + Y ω := by
    fun_prop
  have hAddVal :=
    Thm67Support.textbookIntegral_eq_some_toRealIntegral (μ := μ) (X := fun ω => X ω + Y ω)
      hAddMeas hAddIntegrable
  have hXVal := Thm67Support.textbookIntegral_eq_some_toRealIntegral (μ := μ) (X := X) hXm hX
  have hYVal := Thm67Support.textbookIntegral_eq_some_toRealIntegral (μ := μ) (X := Y) hYm hY
  have hAddInt :
      ∫ ω, (X ω + Y ω).toReal ∂μ = (∫ ω, (X ω).toReal ∂μ) + ∫ ω, (Y ω).toReal ∂μ := by
    calc
      ∫ ω, (X ω + Y ω).toReal ∂μ = ∫ ω, ((X ω).toReal + (Y ω).toReal) ∂μ := by
        apply integral_congr_ae
        exact Thm67Support.toReal_add_ae hXm hYm hX hY
      _ = (∫ ω, (X ω).toReal ∂μ) + ∫ ω, (Y ω).toReal ∂μ := by
        simpa using MeasureTheory.integral_add
          (Thm67Support.integrable_toReal hXm hX)
          (Thm67Support.integrable_toReal hYm hY)
  have hSmulIntegrable := Thm67Support.textbookIntegrable_smul_real hXm hX α
  have hSmulMeas : Measurable fun ω => ((α : EReal) * X ω) := by
    fun_prop
  have hSmulVal :=
    Thm67Support.textbookIntegral_eq_some_toRealIntegral (μ := μ)
      (X := fun ω => ((α : EReal) * X ω)) hSmulMeas hSmulIntegrable
  have hSmulInt :
      ∫ ω, (((α : EReal) * X ω)).toReal ∂μ = α * ∫ ω, (X ω).toReal ∂μ := by
    calc
      ∫ ω, (((α : EReal) * X ω)).toReal ∂μ = ∫ ω, α * (X ω).toReal ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          simpa using EReal.toReal_mul (x := (α : EReal)) (y := X ω))
      _ = α * ∫ ω, (X ω).toReal ∂μ := by
        simpa [smul_eq_mul] using MeasureTheory.integral_smul α (fun ω => (X ω).toReal)
  refine ⟨hAddIntegrable, ?_, hSmulIntegrable, ?_⟩
  · rw [hAddVal, hXVal, hYVal, Option.map₂_some_some]
    simp [hAddInt]
  · rw [hSmulVal, hXVal, Option.map_some]
    apply congrArg some
    simpa [mul_comm] using congrArg (fun r : ℝ => ((r : EReal))) hSmulInt

/--
Complex companion to Theorem 6.7: integrability is preserved by addition and
complex scalar multiplication, and the textbook optional complex integral is
linear.
-/
theorem thm_6_7_complex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z W : Ω → ℂ} (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : complexTextbookIntegrable μ Z) (hW : complexTextbookIntegrable μ W) (α : ℂ) :
    complexTextbookIntegrable μ (fun ω => Z ω + W ω) ∧
      complexTextbookIntegral μ (fun ω => Z ω + W ω) =
        Option.map₂ (fun z w => z + w) (complexTextbookIntegral μ Z) (complexTextbookIntegral μ W) ∧
      complexTextbookIntegrable μ (fun ω => α * Z ω) ∧
      complexTextbookIntegral μ (fun ω => α * Z ω) =
        Option.map (fun z => α * z) (complexTextbookIntegral μ Z) := by
  have hZStd : Integrable Z μ := by
    exact (complexTextbookIntegrable_iff_integrable_core μ Z).mp hZ
  have hWStd : Integrable W μ := by
    exact (complexTextbookIntegrable_iff_integrable_core μ W).mp hW
  have hAddStd : Integrable (fun ω => Z ω + W ω) μ := by
    change Integrable (Z + W) μ
    exact hZStd.add hWStd
  have hSmulStd : Integrable (fun ω => α * Z ω) μ := by
    change Integrable (α • Z) μ
    exact hZStd.smul α
  have hAddIntegrable : complexTextbookIntegrable μ (fun ω => Z ω + W ω) := by
    exact (complexTextbookIntegrable_iff_integrable_core μ (fun ω => Z ω + W ω)).mpr hAddStd
  have hSmulIntegrable : complexTextbookIntegrable μ (fun ω => α * Z ω) := by
    exact (complexTextbookIntegrable_iff_integrable_core μ (fun ω => α * Z ω)).mpr hSmulStd
  have hAddVal :=
    Thm67Support.complexTextbookIntegral_eq_some_integral (μ := μ)
      (Z := fun ω => Z ω + W ω) (by fun_prop) hAddIntegrable
  have hZVal := Thm67Support.complexTextbookIntegral_eq_some_integral (μ := μ) (Z := Z) hZm hZ
  have hWVal := Thm67Support.complexTextbookIntegral_eq_some_integral (μ := μ) (Z := W) hWm hW
  have hSmulVal :=
    Thm67Support.complexTextbookIntegral_eq_some_integral (μ := μ)
      (Z := fun ω => α * Z ω) (by fun_prop) hSmulIntegrable
  refine ⟨hAddIntegrable, ?_, hSmulIntegrable, ?_⟩
  · rw [hAddVal, hZVal, hWVal, Option.map₂_some_some]
    simp [MeasureTheory.integral_add, hZStd, hWStd]
  · rw [hSmulVal, hZVal, Option.map_some]
    apply congrArg some
    simpa [smul_eq_mul] using (MeasureTheory.integral_smul α Z)

/-- Compatibility alias for the earlier draft spelling. -/
theorem thm_6_7_complex' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z W : Ω → ℂ} (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : complexTextbookIntegrable μ Z) (hW : complexTextbookIntegrable μ W) (α : ℂ) :
    complexTextbookIntegrable μ (fun ω => Z ω + W ω) ∧
      complexTextbookIntegral μ (fun ω => Z ω + W ω) =
        Option.map₂ (fun z w => z + w) (complexTextbookIntegral μ Z) (complexTextbookIntegral μ W) ∧
      complexTextbookIntegrable μ (fun ω => α * Z ω) ∧
      complexTextbookIntegral μ (fun ω => α * Z ω) =
        Option.map (fun z => α * z) (complexTextbookIntegral μ Z) := by
  exact thm_6_7_complex μ hZm hWm hZ hW α
