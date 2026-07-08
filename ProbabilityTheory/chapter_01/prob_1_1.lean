import Mathlib

open MeasureTheory ProbabilityTheory Complex Real MeasureTheory.Measure
open scoped ENNReal NNReal

/-! ## Helper lemmas (independent of ProbSpace) -/

/-
The characteristic function of `expMeasure r` at `t` equals `r / (r - t * I)`.
-/
lemma charFun_expMeasure (r : ℝ) (hr : 0 < r) (t : ℝ) :
    charFun (expMeasure r) t = ↑r / (↑r - ↑t * I) := by
  -- Use the provided lemma to rewrite the characteristic function.
  have h_char_fun : charFun (expMeasure r) t = r * ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(r - t * Complex.I) * x) := by
    convert integral_withDensity_eq_integral_smul _ _ using 1;
    · have hmul :
          (↑r : ℂ) * ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(r - t * Complex.I) * x) =
            ∫ x in Set.Ioi (0 : ℝ), (↑r : ℂ) * Complex.exp (-(r - t * Complex.I) * x) := by
        simpa using
          (MeasureTheory.integral_const_mul
            (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (r := (↑r : ℂ))
            (f := fun x : ℝ => Complex.exp (-(r - t * Complex.I) * x))).symm
      rw [hmul]
      rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, gammaPDFReal ];
      rw [ ← MeasureTheory.integral_congr_ae ]
      filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.1 ( MeasureTheory.measure_singleton 0 ) ] with x hx
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · have hxnot_le : ¬ 0 ≤ x := not_le_of_gt hneg
        have hxnot_lt : ¬ 0 < x := not_lt_of_ge hneg.le
        simp [hxnot_le, hxnot_lt]
        exact zero_smul ℝ (Complex.exp (↑(inner ℝ x t) * I))
      · simp [Set.indicator, gammaPDFReal, hpos, hpos.le, Real.Gamma_one]
        have hnonneg : 0 ≤ r * Real.exp (-(r * x)) := by positivity
        rw [NNReal.smul_def]
        norm_num [Real.toNNReal_of_nonneg hnonneg] at *
        change ((r * Real.exp (-(r * x)) : ℝ) : ℂ) * Complex.exp (↑(inner ℝ x t) * I) =
          ↑r * Complex.exp ((↑t * I - ↑r) * ↑x)
        rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
        have hone : inner ℝ (1 : ℝ) t = t := by
          calc
            inner ℝ (1 : ℝ) t = t * inner ℝ (1 : ℝ) 1 := by
              simpa using (real_inner_smul_right (1 : ℝ) (1 : ℝ) t)
            _ = t * 1 := by
              have h11 : inner ℝ (1 : ℝ) 1 = 1 := by norm_num
              rw [h11]
            _ = t := by ring
        have hinner : inner ℝ x t = x * t := by
          calc
            inner ℝ x t = x * inner ℝ (1 : ℝ) t := by
              simpa using (real_inner_smul_left (1 : ℝ) t x)
            _ = x * t := by rw [hone]
        have hexp :
            (↑(-(r * x)) : ℂ) + ↑(inner ℝ x t) * I = (↑t * I - ↑r) * ↑x := by
          rw [hinner]
          have hrx : (↑(-(r * x)) : ℂ) = -↑r * ↑x := by
            push_cast
            ring_nf
          have htx : ↑(x * t) * I = I * ↑t * ↑x := by
            push_cast
            ring_nf
          rw [hrx, htx]
          ring_nf
        rw [hexp]
    · refine' Measurable.subtype_mk _;
      exact Measurable.max ( Measurable.ite ( measurableSet_Ici ) ( by exact Continuous.measurable ( by continuity ) ) measurable_const ) measurable_const;
  rw [ h_char_fun, mul_comm ];
  have h_integral : ∀ a : ℂ, a.re > 0 → ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-a * x) = 1 / a := by
    intro a ha
    have : Filter.Tendsto (fun b : ℝ => ∫ x in (0 : ℝ)..b, Complex.exp (-a * x)) Filter.atTop (nhds (1 / a)) := by
      have h_integral : ∀ b : ℝ, ∫ x in (0 : ℝ)..b, Complex.exp (-a * x) = (1 - Complex.exp (-a * b)) / a := by
        intro b; have := @integral_exp_mul_complex 0 b; simp_all +decide [ div_eq_inv_mul ] ;
        convert @this ( -a ) ( neg_ne_zero.mpr <| by aesop ) using 1 <;> norm_num ; ring;
      -- Use the fact that $e^{-a b} \to 0$ as $b \to \infty$ for $a > 0$.
      have h_exp_zero : Filter.Tendsto (fun b : ℝ => Complex.exp (-a * b)) Filter.atTop (nhds 0) := by
        rw [ tendsto_zero_iff_norm_tendsto_zero ];
        norm_num [ Complex.norm_exp ];
        exact Filter.tendsto_id.const_mul_atTop ha;
      simpa only [ h_integral, sub_zero ] using Filter.Tendsto.div_const ( h_exp_zero.const_sub 1 ) a
    refine' tendsto_nhds_unique _ this;
    apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
    · have h_integrable : MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp (-a.re * x)) (Set.Ioi 0) := by
        have := ( exp_neg_integrableOn_Ioi 0 ha );
        exact this;
      refine' h_integrable.norm.mono' _ _;
      · exact Continuous.aestronglyMeasurable ( by continuity );
      · simp [Complex.norm_exp];
    · exact Filter.tendsto_id;
  rw [ h_integral ] <;> norm_num [ hr ] ; ring

/-
When squared, the integral of `cexp(i t x²)` against `gaussianReal 0 v`
    equals `1 / (1 - 2 v I t)`.
-/
lemma integral_cexp_sq_gaussianReal_sq (v : NNReal) (hv : (v : ℝ) > 0) (t : ℝ) :
    (∫ x : ℝ, cexp (↑(x ^ 2 * t) * I) ∂gaussianReal 0 v) ^ 2 =
    1 / (1 - 2 * ↑(v : ℝ) * ↑t * I) := by
  -- Set $b = \frac{1}{2v} - t \cdot i$.
  set b : ℂ := (1 / (2 * v : ℂ)) - t * Complex.I
  have h1 :
      ∫ x : ℝ, Complex.exp (↑(x ^ 2 * t) * Complex.I) ∂gaussianReal 0 v =
        (↑(√(2 * Real.pi * v))⁻¹ : ℂ) * ∫ x : ℝ, Complex.exp (-(b * x ^ 2)) := by
    rw [ integral_gaussianReal_eq_integral_smul ];
    · have hmul :
          (↑(√(2 * Real.pi * v))⁻¹ : ℂ) * ∫ x : ℝ, Complex.exp (-(b * x ^ 2)) =
            ∫ x : ℝ, (↑(√(2 * Real.pi * v))⁻¹ : ℂ) * Complex.exp (-(b * x ^ 2)) := by
        simpa using
          (MeasureTheory.integral_const_mul
            (μ := volume)
            (r := (↑(√(2 * Real.pi * v))⁻¹ : ℂ))
            (f := fun x : ℝ => Complex.exp (-(b * x ^ 2)))).symm
      rw [hmul]
      congr
      congr 1
      ext x
      unfold gaussianPDFReal
      push_cast
      simp [sub_zero]
      change (((√↑v)⁻¹ * ((√π)⁻¹ * (√2)⁻¹) * Real.exp (-x ^ 2 / (2 * ↑v))) : ℝ) •
            Complex.exp (↑x ^ 2 * ↑t * I) =
          (↑√↑v)⁻¹ * ((↑√π)⁻¹ * (↑√2)⁻¹) * Complex.exp (-(b * ↑x ^ 2))
      rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc,
        ← Complex.exp_add]
      have hvc : ((v : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt hv
      have hexp_direct :
          (((-x ^ 2 / (2 * (v : ℝ))) : ℝ) : ℂ) + ↑x ^ 2 * ↑t * I = -(b * ↑x ^ 2) := by
        have hsq_div :
            (((-x ^ 2 / (2 * (v : ℝ))) : ℝ) : ℂ) =
              (((x ^ 2 * (↑v)⁻¹ * (-1 / 2 : ℝ)) : ℝ) : ℂ) := by
          norm_num [div_eq_mul_inv]
          ring_nf
        rw [hsq_div]
        simp [b, div_eq_mul_inv]
        ring_nf
      have hcexp := congrArg Complex.exp hexp_direct
      have hmul_exp :
          (↑(√↑v)⁻¹ : ℂ) * ↑((√π)⁻¹ * (√2)⁻¹) *
              Complex.exp (((( -x ^ 2 / (2 * (v : ℝ))) : ℝ) : ℂ) + ↑x ^ 2 * ↑t * I) =
            (↑(√↑v)⁻¹ : ℂ) * ↑((√π)⁻¹ * (√2)⁻¹) * Complex.exp (-(b * ↑x ^ 2)) := by
        exact congrArg (fun z => (↑(√↑v)⁻¹ : ℂ) * ↑((√π)⁻¹ * (√2)⁻¹) * z) hcexp
      simpa [mul_assoc] using hmul_exp
    · aesop;
  -- By integral_gaussian_complex, ∫ x, cexp (-b * x^2) = (π / b)^(1/2).
  have h2 : ∫ x : ℝ, Complex.exp (-(b * x ^ 2)) = (Real.pi / b) ^ (1 / 2 : ℂ) := by
    have hb_re : 0 < b.re := by
      simp [b, hv]
    simpa using (integral_gaussian_complex (b := b) hb_re)
  simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, Real.pi_pos.le, ne_of_gt Real.pi_pos ];
  norm_cast ; norm_num [ mul_pow, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.le, hv.ne' ] ; ring;
  simp +zetaDelta at *;
  field_simp;
  ring ; norm_num [ hv.ne' ]

/-
The charFun of the pushforward of a product measure by the sum-of-squares function
    factors as the square of an integral.
-/
lemma charFun_sq_sum_prod (v : NNReal) (hv : (v : ℝ) > 0) (t : ℝ) :
    charFun (Measure.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
      ((gaussianReal 0 v).prod (gaussianReal 0 v))) t =
    (∫ x : ℝ, cexp (↑(x ^ 2 * t) * I) ∂gaussianReal 0 v) ^ 2 := by
  rw [charFun_apply_real]
  rw [MeasureTheory.integral_map_of_stronglyMeasurable
    (μ := (gaussianReal 0 v).prod (gaussianReal 0 v))
    (φ := fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
    (f := fun x : ℝ => Complex.exp (t * x * I))
    (by fun_prop)
    (by fun_prop)]
  calc
    ∫ z : ℝ × ℝ, cexp (↑t * ↑(z.1 ^ 2 + z.2 ^ 2) * I) ∂(gaussianReal 0 v).prod (gaussianReal 0 v)
        = ∫ z : ℝ × ℝ, cexp (↑z.1 ^ 2 * ↑t * I) * cexp (↑z.2 ^ 2 * ↑t * I) ∂
            (gaussianReal 0 v).prod (gaussianReal 0 v) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            have hzexp :
                ↑t * ↑(z.1 ^ 2 + z.2 ^ 2) * I = ↑z.1 ^ 2 * ↑t * I + ↑z.2 ^ 2 * ↑t * I := by
              push_cast
              ring_nf
            rw [show Complex.exp (↑t * ↑(z.1 ^ 2 + z.2 ^ 2) * I) =
                Complex.exp (↑z.1 ^ 2 * ↑t * I + ↑z.2 ^ 2 * ↑t * I) by rw [hzexp]]
            rw [Complex.exp_add]
    _ = (∫ x : ℝ, cexp (↑x ^ 2 * ↑t * I) ∂gaussianReal 0 v) *
          ∫ y : ℝ, cexp (↑y ^ 2 * ↑t * I) ∂gaussianReal 0 v := by
            simpa using (MeasureTheory.integral_prod_mul
              (μ := gaussianReal 0 v)
              (ν := gaussianReal 0 v)
              (f := fun x : ℝ => cexp (↑x ^ 2 * ↑t * I))
              (g := fun y : ℝ => cexp (↑y ^ 2 * ↑t * I)))
    _ = (∫ x : ℝ, cexp (↑(x ^ 2 * t) * I) ∂gaussianReal 0 v) *
          ∫ y : ℝ, cexp (↑(y ^ 2 * t) * I) ∂gaussianReal 0 v := by
            congr 1
            · refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with x
              have hxexp : ↑x ^ 2 * ↑t * I = ↑(x ^ 2 * t) * I := by
                simpa [mul_assoc, mul_left_comm, mul_comm]
              rw [hxexp]
            · refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with y
              have hyexp : ↑y ^ 2 * ↑t * I = ↑(y ^ 2 * t) * I := by
                simpa [mul_assoc, mul_left_comm, mul_comm]
              rw [hyexp]
    _ = (∫ x : ℝ, cexp (↑(x ^ 2 * t) * I) ∂gaussianReal 0 v) ^ 2 := by
          rw [sq]

/-- Core: the pushforward of the product of two centered Gaussians under sum-of-squares
    equals the exponential distribution. -/
lemma gaussianReal_sq_sum_eq_expMeasure (v : NNReal) (hv : (v : ℝ) > 0) :
    Measure.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) =
    expMeasure ((2 * (v : ℝ))⁻¹) := by
  have hr : 0 < (2 * (v : ℝ))⁻¹ := by positivity
  haveI := isProbabilityMeasure_expMeasure hr
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_sq_sum_prod v hv t, integral_cexp_sq_gaussianReal_sq v hv t]
  rw [charFun_expMeasure _ hr t]
  -- Algebraic identity: 1/(1-2vIt) = (2v)⁻¹/((2v)⁻¹ - tI)
  have hd1 : (1 : ℂ) - 2 * ↑(v : ℝ) * ↑t * I ≠ 0 := by
    intro h; have := congr_arg re h; simp at this
  have hd2 : (↑(2 * (v : ℝ))⁻¹ : ℂ) - ↑t * I ≠ 0 := by
    intro h; have h1 := congr_arg re h; simp at h1; simp [h1] at hv
  rw [div_eq_div_iff hd1 hd2]
  push_cast
  ring_nf
  rw [mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hv : (↑(v : ℝ) : ℂ) ≠ 0)]
  ring

/-! ## Probability space infrastructure -/

class ProbSpace where
  Ω : Type*
  msΩ : MeasurableSpace Ω
  P : @Measure Ω msΩ
  isProb : @IsProbabilityMeasure Ω msΩ P

attribute [instance] ProbSpace.msΩ ProbSpace.isProb

variable [ps : ProbSpace]

structure RandomVariable (α : Type*) where
  toFun : ps.Ω → α

instance {α : Type*} : CoeFun (RandomVariable α) (fun _ => ps.Ω → α) where
  coe := RandomVariable.toFun

instance {α : Type*} : Coe (ps.Ω → α) (RandomVariable α) where
  coe f := ⟨f⟩

noncomputable def RandomVariable.distribution {α : Type*} [MeasurableSpace α]
    (X : RandomVariable α) : Measure α :=
  Measure.map X.toFun ps.P

namespace Function

noncomputable def distribution {α : Type*} [MeasurableSpace α] (X : ps.Ω → α) : Measure α :=
  RandomVariable.distribution (X : RandomVariable α)

end Function

noncomputable def NormalDist (μ σ : ℝ) : Measure ℝ :=
  gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩

noncomputable def Exponential (r : ℝ) : Measure ℝ :=
  expMeasure r

def Independent (X Y : RandomVariable ℝ) : Prop :=
  ProbabilityTheory.IndepFun X.toFun Y.toFun ps.P

local notation "Normal" => NormalDist

/-! ## Main theorem -/

theorem prob_1_1 (σ : ℝ) (hσ : σ > 0) (X Y : RandomVariable ℝ)
    (h_indep : Independent X Y)
    (hX_dist : X.distribution = Normal (0 : ℝ) σ)
    (hY_dist : Y.distribution = Normal (0 : ℝ) σ) :
    (fun ω => X ω ^ 2 + Y ω ^ 2).distribution =
      Exponential ((2 * σ ^ 2)⁻¹) := by
  simp only [RandomVariable.distribution, Exponential]
  set v : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩
  have hv : (v : ℝ) > 0 := sq_pos_of_pos hσ
  have hX : Measure.map X.toFun ps.P = gaussianReal 0 v := by
    change X.distribution = NormalDist 0 σ at hX_dist
    simp only [RandomVariable.distribution, NormalDist] at hX_dist; exact hX_dist
  have hY : Measure.map Y.toFun ps.P = gaussianReal 0 v := by
    change Y.distribution = NormalDist 0 σ at hY_dist
    simp only [RandomVariable.distribution, NormalDist] at hY_dist; exact hY_dist
  have hX_ae : AEMeasurable X.toFun ps.P := by
    by_contra hc; rw [Measure.map_of_not_aemeasurable hc] at hX
    exact (IsProbabilityMeasure.ne_zero (gaussianReal 0 v)) hX.symm
  have hY_ae : AEMeasurable Y.toFun ps.P := by
    by_contra hc; rw [Measure.map_of_not_aemeasurable hc] at hY
    exact (IsProbabilityMeasure.ne_zero (gaussianReal 0 v)) hY.symm
  have hi : IndepFun X.toFun Y.toFun ps.P := h_indep
  have h_prod : Measure.map (fun ω => (X.toFun ω, Y.toFun ω)) ps.P =
      (gaussianReal 0 v).prod (gaussianReal 0 v) := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map hX_ae hY_ae).mp hi
    rw [hX, hY] at h; exact h
  have h_sq_meas : Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by measurability
  have h_pair_ae : AEMeasurable (fun ω => (X.toFun ω, Y.toFun ω)) ps.P :=
    hX_ae.prodMk hY_ae
  show Measure.map (fun ω => X.toFun ω ^ 2 + Y.toFun ω ^ 2) ps.P = _
  calc Measure.map (fun ω => X.toFun ω ^ 2 + Y.toFun ω ^ 2) ps.P
      = Measure.map ((fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ∘
          (fun ω => (X.toFun ω, Y.toFun ω))) ps.P := by rfl
    _ = Measure.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
          (Measure.map (fun ω => (X.toFun ω, Y.toFun ω)) ps.P) := by
        conv_lhs => rw [Measure.map_congr (h_pair_ae.ae_eq_mk.fun_comp
          (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2))]
        rw [← Measure.map_map h_sq_meas h_pair_ae.measurable_mk,
            Measure.map_congr h_pair_ae.ae_eq_mk]
    _ = Measure.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
          ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by rw [h_prod]
    _ = expMeasure ((2 * (v : ℝ))⁻¹) := gaussianReal_sq_sum_eq_expMeasure v hv
    _ = expMeasure ((2 * σ ^ 2)⁻¹) := by norm_cast
