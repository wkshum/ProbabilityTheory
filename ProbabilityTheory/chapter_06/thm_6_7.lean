import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ProbabilityTheory.chapter_06.def_6_5
import ProbabilityTheory.chapter_06.def_6_6


/-! # Theorem 6.7: linearity of the Lebesgue integral -/

open MeasureTheory

namespace Thm67Support

lemma realCoe_textbookIntegrable_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) :
    textbookIntegrable μ (fun ω => (f ω : EReal)) ↔ Integrable f μ := by
  unfold textbookIntegrable;
  constructor;
  · intro h_integrable
    have h_integrable_pos : MeasureTheory.Integrable (fun ω => max (f ω) 0) μ := by
      refine' ⟨ hfm.aemeasurable.max aemeasurable_const |> fun h => h.aestronglyMeasurable, _ ⟩;
      convert h_integrable.1 using 1;
      simp +decide [ hasFiniteIntegral_iff_norm, Def65Support.posLIntegral ];
      simp +decide [Def65Support.posPart, abs_of_nonneg]
    have h_integrable_neg : MeasureTheory.Integrable (fun ω => max (-f ω) 0) μ := by
      refine' ⟨ _, _ ⟩;
      · exact Measurable.aestronglyMeasurable ( by measurability );
      · convert h_integrable.2 using 1;
        simp +decide [ hasFiniteIntegral_iff_norm, Def65Support.negLIntegral ];
        simp +decide [Def65Support.negPart, abs_of_nonneg];
    convert h_integrable_pos.sub h_integrable_neg using 1 ; ext ω ; simp +decide [ max_def ] ; split_ifs <;> linarith;
  · intro hf;
    constructor;
    · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) _;
      exact fun ω => ENNReal.ofReal |f ω|;
      · unfold Def65Support.posPart;
        cases abs_cases ( f ω ) <;> simp +decide [ * ];
        rw [ ENNReal.ofReal_eq_zero.mpr ( by linarith ) ] ; norm_num;
      · convert hf.abs.lintegral_lt_top using 1;
    · refine' MeasureTheory.Integrable.lintegral_lt_top _;
      convert hf.neg using 1
      rfl



lemma def66Real_textbookIntegrable_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) :
    Def66RealSupport.textbookIntegrable μ (fun ω => (f ω : EReal)) ↔ Integrable f μ := by
  convert realCoe_textbookIntegrable_iff hfm using 1
  rfl

lemma textbookIntegral_realCoe_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    textbookIntegral μ (fun ω => (f ω : EReal)) = some ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  unfold textbookIntegral
  simp +decide [Def65Support.posLIntegral, Def65Support.negLIntegral]
  constructor;
  · intro h;
    convert hf.neg.lintegral_lt_top.ne using 1;
    rfl
  · have h_pos_neg : ∫⁻ ω, Def65Support.posPart (fun ω => (f ω : EReal)) ω ∂μ = ENNReal.ofReal (∫ ω, max (f ω) 0 ∂μ) ∧ ∫⁻ ω, Def65Support.negPart (fun ω => (f ω : EReal)) ω ∂μ = ENNReal.ofReal (∫ ω, max (-f ω) 0 ∂μ) := by
      constructor <;> rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      any_goals filter_upwards [ ] using fun _ => le_max_right _ _;
      · congr with ω ; simp +decide [ Def65Support.posPart ];
      · exact hf.pos_part;
      · congr with ω ; simp +decide [ Def65Support.negPart ];
      · exact hf.neg.pos_part;
    rw [ h_pos_neg.1, h_pos_neg.2, MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ] ; norm_cast;
    · rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
      · rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
        · simp +decide [ ENNReal.ofReal, Real.toNNReal ];
          rfl;
        · exact hf;
      · exact hf.neg_part;
    · exact hf.pos_part

lemma def66Real_textbookValue_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    Def66RealSupport.textbookValue μ (fun ω => (f ω : EReal)) = ∫ ω, f ω ∂μ := by
  have := @Thm67Support.textbookIntegral_realCoe_eq_some_integral Ω _ μ f hf;
  unfold textbookIntegral at this;
  split_ifs at this ; simp_all +decide [ Def66RealSupport.textbookValue ];
  convert congr_arg EReal.toReal this using 1
  · rfl
  · rfl

lemma complexTextbookIntegral_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) (hZ : Integrable Z μ) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  rw [ complexTextbookIntegral ];
  split_ifs with hZ';
  · rw [ def66Real_textbookValue_eq_integral, def66Real_textbookValue_eq_integral ];
    · rw [ ← integral_re_add_im hZ ] ;
      norm_num [ mul_comm ];
    · exact hZ.im;
    · exact hZ.re;
  · contrapose! hZ';
    exact ⟨ def66Real_textbookIntegrable_iff ( Complex.measurable_re.comp hZm ) |>.2 hZ.re, def66Real_textbookIntegrable_iff ( Complex.measurable_im.comp hZm ) |>.2 hZ.im ⟩

lemma ae_eq_realCoe_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    X =ᵐ[μ] fun ω => ((X ω).toReal : EReal) := by
  have h_pos : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
    convert MeasureTheory.ae_lt_top ( hXm.ereal_toENNReal ) _ using 1;
    · ext ω; cases h : X ω <;> simp +decide;
    · exact hX.1.ne
  have h_neg : ∀ᵐ ω ∂μ, X ω ≠ ⊥ := by
    convert MeasureTheory.ae_lt_top ( hXm.neg.ereal_toENNReal ) _;
    · cases h : X ‹_› <;> simp +decide;
    · exact hX.2.ne;
  filter_upwards [ h_pos, h_neg ] with ω hω₁ hω₂ using by cases h : X ω <;> aesop;

lemma integrable_toReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    Integrable (fun ω => (X ω).toReal) μ := by
  have h_realCoe : textbookIntegrable μ (fun ω => ((X ω).toReal : EReal)) := by
    obtain ⟨h_pos, h_neg⟩ := hX;
    constructor;
    · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) h_pos;
      cases h : X ω <;> simp +decide [ h, Def65Support.posPart ];
    · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) h_neg;
      cases h : X ω <;> simp +decide [ h, Def65Support.negPart ];
  convert realCoe_textbookIntegrable_iff _ |>.1 h_realCoe;
  fun_prop

lemma textbookIntegrable_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → EReal} (h : X =ᵐ[μ] Y) :
    textbookIntegrable μ X ↔ textbookIntegrable μ Y := by
  constructor <;> intro h' <;> constructor;
  · refine' lt_of_le_of_lt _ h'.1;
    refine' MeasureTheory.lintegral_mono_ae _;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.posPart ] ;
  · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono_ae _ ) ( h'.2 );
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.negPart ] ;
  · have h_pos : Def65Support.posLIntegral μ X = Def65Support.posLIntegral μ Y := by
      apply MeasureTheory.lintegral_congr_ae;
      filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.posPart ] ;
    exact h_pos.symm ▸ h'.1;
  · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono_ae _ ) h'.2;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.negPart ] ;

lemma textbookIntegral_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → EReal} (h : X =ᵐ[μ] Y) :
    textbookIntegral μ X = textbookIntegral μ Y := by
  unfold textbookIntegral;
  -- Since $X$ and $Y$ are equal almost everywhere, their positive and negative parts are also equal almost everywhere.
  have h_pos_eq : Def65Support.posLIntegral μ X = Def65Support.posLIntegral μ Y := by
    apply MeasureTheory.lintegral_congr_ae;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.posPart ] ;
  have h_neg_eq : Def65Support.negLIntegral μ X = Def65Support.negLIntegral μ Y := by
    apply MeasureTheory.lintegral_congr_ae;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.negPart ] ;
  aesop
end Thm67Support

/--
Theorem 6.7 for extended-real-valued functions: textbook integrability and
its optional integral are preserved by addition and real scalar multiplication.
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
  refine' ⟨ _, _, _, _ ⟩;
  · have h_add : textbookIntegrable μ (fun ω => (X ω).toReal + (Y ω).toReal) := by
      convert Thm67Support.realCoe_textbookIntegrable_iff _ |>.2 ( Thm67Support.integrable_toReal hXm hX |> fun h => h.add ( Thm67Support.integrable_toReal hYm hY ) ) using 1;
      · rfl
      · exact hXm.ereal_toReal.add hYm.ereal_toReal
    have h_eq : ∀ᵐ ω ∂μ, X ω + Y ω = (X ω).toReal + (Y ω).toReal := by
      have h_eq : ∀ᵐ ω ∂μ, X ω = (X ω).toReal ∧ Y ω = (Y ω).toReal := by
        have := Thm67Support.ae_eq_realCoe_toReal hXm hX; have := Thm67Support.ae_eq_realCoe_toReal hYm hY; aesop;
      filter_upwards [ h_eq ] with ω hω using congr_arg₂ ( · + · ) hω.1 hω.2;
    exact (Thm67Support.textbookIntegrable_congr_ae h_eq).mpr h_add;
  · convert Thm67Support.textbookIntegral_congr_ae _ |> Eq.trans <| Thm67Support.textbookIntegral_realCoe_eq_some_integral _ using 1;
    case convert_6 => exact fun ω => ( X ω |> EReal.toReal ) + ( Y ω |> EReal.toReal );
    · have := Thm67Support.textbookIntegral_realCoe_eq_some_integral ( Thm67Support.integrable_toReal hXm hX ) ; have := Thm67Support.textbookIntegral_realCoe_eq_some_integral ( Thm67Support.integrable_toReal hYm hY ) ; simp_all +decide [ Option.map₂ ] ;
      rw [ MeasureTheory.integral_add ];
      · rw [ Thm67Support.textbookIntegral_congr_ae ( Thm67Support.ae_eq_realCoe_toReal hXm hX ), Thm67Support.textbookIntegral_congr_ae ( Thm67Support.ae_eq_realCoe_toReal hYm hY ) ] ; aesop;
      · exact Thm67Support.integrable_toReal hXm hX;
      · exact Thm67Support.integrable_toReal hYm hY;
    · filter_upwards [ Thm67Support.ae_eq_realCoe_toReal hXm hX, Thm67Support.ae_eq_realCoe_toReal hYm hY ] with ω hωX hωY;
      rw [ hωX, hωY, EReal.coe_add ];
      norm_num;
    · exact MeasureTheory.Integrable.add ( Thm67Support.integrable_toReal hXm hX ) ( Thm67Support.integrable_toReal hYm hY );
  · convert Thm67Support.textbookIntegrable_congr_ae _ |>.2 ( Thm67Support.realCoe_textbookIntegrable_iff ( show Measurable fun ω => ( α * ( X ω |> EReal.toReal ) ) from ?_ ) |>.2 ( ?_ ) ) using 1;
    · filter_upwards [ Thm67Support.ae_eq_realCoe_toReal hXm hX ] with ω hω;
      rw [ hω ] ; norm_cast;
    · fun_prop;
    · exact MeasureTheory.Integrable.const_mul ( Thm67Support.integrable_toReal hXm hX ) α;
  · convert Thm67Support.textbookIntegral_congr_ae _ |> Eq.trans <| Thm67Support.textbookIntegral_realCoe_eq_some_integral _ using 1;
    convert congr_arg ( fun x : Option EReal => Option.map ( fun y : EReal => ( α : EReal ) * y ) x ) ( Thm67Support.textbookIntegral_realCoe_eq_some_integral <| Thm67Support.integrable_toReal hXm hX ) using 1;
    convert congr_arg ( fun x : Option EReal => Option.map ( fun y : EReal => ( α : EReal ) * y ) x ) ( Thm67Support.textbookIntegral_congr_ae _ ) using 1;
    exact Thm67Support.ae_eq_realCoe_toReal hXm hX;
    rotate_left;
    rotate_left;
    exact fun ω => α * ( X ω |> EReal.toReal );
    · exact MeasureTheory.Integrable.const_mul ( Thm67Support.integrable_toReal hXm hX ) α;
    · simp [ MeasureTheory.integral_const_mul ];
    · filter_upwards [ Thm67Support.ae_eq_realCoe_toReal hXm hX ] with ω hω;
      rw [ hω ] ; norm_cast
/-
For a measurable complex-valued function, textbook integrability of its
real and imaginary parts is equivalent to Bochner integrability.
-/
theorem complexTextbookIntegrable_iff_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ Integrable Z μ := by
  refine' ⟨ _, fun h => _ ⟩;
  · intro hZ_integrable
    obtain ⟨hZ_re, hZ_im⟩ := hZ_integrable
    have hZ_re_integrable : Integrable (fun ω => (Z ω).re) μ := by
      convert Thm67Support.def66Real_textbookIntegrable_iff _ |>.1 hZ_re using 1;
      exact Complex.measurable_re.comp hZm
    have hZ_im_integrable : Integrable (fun ω => (Z ω).im) μ := by
      exact Thm67Support.def66Real_textbookIntegrable_iff ( Complex.measurable_im.comp hZm ) |>.1 hZ_im;
    convert hZ_re_integrable.ofReal.add ( hZ_im_integrable.ofReal.smul_const Complex.I ) using 1 ;
    rfl
    ext; simp  [Complex.ext_iff]
    any_goals exact ℝ
    all_goals first | infer_instance | simp +decide
  · constructor;
    · convert Thm67Support.def66Real_textbookIntegrable_iff ( Complex.measurable_re.comp hZm ) |>.2 ( h.re ) using 1;
      rfl
    · convert Thm67Support.def66Real_textbookIntegrable_iff ( show Measurable fun ω => ( Z ω |> Complex.im ) from Complex.measurable_im.comp hZm ) |>.2 ( h.im ) using 1

/--
## Theorem 6.7 for the complex-valued textbook integral.

If `Z` and `W` are measurable and textbook-integrable complex-valued functions, then:

* their pointwise sum `fun ω => Z ω + W ω` is textbook-integrable;
* the textbook integral of the sum is the sum of the textbook integrals;
* for every scalar `α : ℂ`, the scalar multiple `fun ω => α * Z ω` is textbook-integrable;
* the textbook integral of the scalar multiple is `α` times the textbook integral of `Z`.

The equalities are stated using `Option.map₂` and `Option.map`, since
`complexTextbookIntegral` returns an optional value.
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
  refine' ⟨ _, _, _, _ ⟩;
  · convert complexTextbookIntegrable_iff_integrable ( show Measurable fun ω => Z ω + W ω from hZm.add hWm ) |>.2 ( Integrable.add ( complexTextbookIntegrable_iff_integrable hZm |>.1 hZ ) ( complexTextbookIntegrable_iff_integrable hWm |>.1 hW ) ) using 1;
  · convert Thm67Support.complexTextbookIntegral_eq_some_integral ( hZm.add hWm ) ( show Integrable ( fun ω => Z ω + W ω ) μ from _ ) using 1;
    · rw [ Thm67Support.complexTextbookIntegral_eq_some_integral hZm ( complexTextbookIntegrable_iff_integrable hZm |>.1 hZ ), Thm67Support.complexTextbookIntegral_eq_some_integral hWm ( complexTextbookIntegrable_iff_integrable hWm |>.1 hW ), MeasureTheory.integral_add ];
      · rfl;
      · exact complexTextbookIntegrable_iff_integrable hZm |>.1 hZ;
      · exact complexTextbookIntegrable_iff_integrable hWm |>.1 hW;
    · exact ( complexTextbookIntegrable_iff_integrable hZm ).1 hZ |> fun h => h.add ( ( complexTextbookIntegrable_iff_integrable hWm ).1 hW );
  · convert ( complexTextbookIntegrable_iff_integrable ( show Measurable fun ω => α * Z ω from measurable_const.mul hZm ) ) |>.2 ( MeasureTheory.Integrable.const_mul ( show MeasureTheory.Integrable Z μ from ?_ ) α ) using 1;
    exact complexTextbookIntegrable_iff_integrable hZm |>.1 hZ;
  · -- By definition of complexTextbookIntegral, we know that
    have h_integrable : Integrable (fun ω => α * Z ω) μ := by
      exact MeasureTheory.Integrable.const_mul ( by simpa using ( complexTextbookIntegrable_iff_integrable hZm ).mp hZ ) α;
    rw [ Thm67Support.complexTextbookIntegral_eq_some_integral, Thm67Support.complexTextbookIntegral_eq_some_integral ];
    · simp [ MeasureTheory.integral_const_mul ];
    · exact hZm;
    · exact (complexTextbookIntegrable_iff_integrable hZm).mp hZ;
    · exact measurable_const.mul hZm;
    · exact h_integrable

/--
Compatibility alias for `thm_6_7_complex`.

This is an alternative spelling of Theorem 6.7 for the complex-valued textbook
integral, retained for compatibility with the draft. It states the same
linearity properties: closure under addition and scalar multiplication,
together with the corresponding formulas for `complexTextbookIntegral`.
-/
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
