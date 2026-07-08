import Mathlib

/-
TASK ID: prob_1_6
TYPE: Problem
SOURCE PLAN: 39_chap1_problems
TASK CONTENT:
\textbf{1.6.} We roll a fair die and denote the value minus $1$ as $X$, so that $X$ is a discrete uniform random variable taking values in $\{0,1,2,3,4,5\}$. Independently, we generate a continuous uniform random variable $U$ between $0$ and $1$. Let $Y$ be the product $XU$. The random variable $Y$ can be described as follows. When $X=0$, $Y$ is equal to a constant $0$. When $X=1$, $Y$ takes on a uniform distribution between $0$ and $1$. When $X=2$, $Y$ takes on a uniform distribution between $0$ and $2$, and so on:
\begin{enumerate}[label=(\alph*)]
    \item Draw the cumulative distribution function of $Y$.
    \item Compute the expectation of $Y$.
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory intervalIntegral Finset

noncomputable section

/-- The fair die value after subtracting one, encoded as a uniform PMF on `Fin 6`. -/
noncomputable def prob_1_6_diePMF : PMF (Fin 6) :=
  PMF.uniformOfFintype (Fin 6)

/-- The fair-die probability measure on values `{0,1,2,3,4,5}`. -/
noncomputable def prob_1_6_dieMeasure : Measure (Fin 6) :=
  prob_1_6_diePMF.toMeasure

/-- The continuous uniform probability measure on `[0,1]`. -/
noncomputable def prob_1_6_unitUniformMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The product model encoding an independent fair die and a uniform `[0,1]` variable. -/
noncomputable def prob_1_6_sampleMeasure : Measure (Fin 6 × ℝ) :=
  prob_1_6_dieMeasure.prod prob_1_6_unitUniformMeasure

/-- The die variable `X`, taking values `0,1,2,3,4,5`. -/
def prob_1_6_X (ω : Fin 6 × ℝ) : ℝ :=
  (ω.1 : ℕ)

/-- The uniform variable `U` on `[0,1]`. -/
def prob_1_6_U (ω : Fin 6 × ℝ) : ℝ :=
  ω.2

/-- The source random variable `Y = XU`. -/
def prob_1_6_Y (ω : Fin 6 × ℝ) : ℝ :=
  prob_1_6_X ω * prob_1_6_U ω

/-- Each die atom has probability `1/6`. -/
theorem prob_1_6_die_singleton (k : Fin 6) :
    prob_1_6_dieMeasure ({k} : Set (Fin 6)) = (1 / 6 : ENNReal) := by
  rw [prob_1_6_dieMeasure]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]
  norm_num [prob_1_6_diePMF, PMF.uniformOfFintype_apply]

/-- The `[0,1]` uniform measure has total mass one. -/
theorem prob_1_6_unitUniformMeasure_univ :
    prob_1_6_unitUniformMeasure Set.univ = 1 := by
  rw [prob_1_6_unitUniformMeasure, Measure.restrict_apply MeasurableSet.univ]
  simp [Real.volume_Icc]

/-- On the die fiber `X=k`, the source variable is the scaled uniform variable `kU`. -/
theorem prob_1_6_Y_on_die_fiber (k : Fin 6) (u : ℝ) :
    prob_1_6_Y (k, u) = (k : ℕ) * u := by
  rfl

/-- Conditional CDF of `k * U` when `U` is uniform on `[0,1]`.
For `k = 0`, this is the degenerate variable equal to zero. -/
noncomputable def prob_1_6_conditionalCdf (k : ℕ) (y : ℝ) : ℝ :=
  if y < 0 then 0
  else if k = 0 then 1
  else min (y / (k : ℝ)) 1

/-- The CDF obtained from conditioning on the fair die value `X = k`. -/
noncomputable def cdf_Y (y : ℝ) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ k ∈ Finset.range 6, prob_1_6_conditionalCdf k y

/-- For the degenerate scale `0`, the sublevel probability is the step CDF at zero. -/
theorem prob_1_6_unitUniform_sublevel_zero (y : ℝ) :
    (prob_1_6_unitUniformMeasure {u : ℝ | (0 : ℝ) * u ≤ y}).toReal =
      if y < 0 then 0 else 1 := by
  by_cases hy : y < 0
  · have hnot : ¬ (0 : ℝ) ≤ y := by linarith
    simp [prob_1_6_unitUniformMeasure, hy, hnot]
  · have hy0 : (0 : ℝ) ≤ y := le_of_not_gt hy
    simp [prob_1_6_unitUniformMeasure, hy, hy0, Real.volume_Icc]

/-- For a positive scale `a`, the restricted-uniform sublevel measure is `min (y/a) 1`. -/
theorem prob_1_6_unitUniform_sublevel_pos {a y : ℝ} (ha : 0 < a) :
    (prob_1_6_unitUniformMeasure {u : ℝ | a * u ≤ y}).toReal =
      if y < 0 then 0 else min (y / a) 1 := by
  have hmeas : MeasurableSet {u : ℝ | a * u ≤ y} := by
    exact measurableSet_le (by fun_prop : Measurable fun u : ℝ => a * u) measurable_const
  rw [prob_1_6_unitUniformMeasure, Measure.restrict_apply hmeas]
  by_cases hy : y < 0
  · have hset : {u : ℝ | a * u ≤ y} ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
      ext u
      constructor
      · intro hu
        have hnonneg : (0 : ℝ) ≤ a * u := mul_nonneg ha.le hu.2.1
        have : (0 : ℝ) < 0 := lt_of_le_of_lt (le_trans hnonneg hu.1) hy
        exact (lt_irrefl (0 : ℝ) this).elim
      · intro hu
        simp at hu
    rw [hset]
    simp [hy]
  · have hy0 : (0 : ℝ) ≤ y := le_of_not_gt hy
    by_cases hcap : y / a ≤ 1
    · have hya0 : (0 : ℝ) ≤ y / a := div_nonneg hy0 ha.le
      have hset :
          {u : ℝ | a * u ≤ y} ∩ Set.Icc (0 : ℝ) 1 =
            Set.Icc (0 : ℝ) (y / a) := by
        ext u
        constructor
        · intro hu
          refine ⟨hu.2.1, ?_⟩
          have hmul : u * a ≤ y := by simpa [mul_comm] using hu.1
          exact (le_div_iff₀ ha).2 hmul
        · intro hu
          refine ⟨?_, ⟨hu.1, ?_⟩⟩
          · have hmul : u * a ≤ y := (le_div_iff₀ ha).1 hu.2
            simpa [mul_comm] using hmul
          · exact hu.2.trans hcap
      rw [hset, Real.volume_Icc]
      simp [hy, ENNReal.toReal_ofReal hya0, min_eq_left hcap]
    · have hcap' : (1 : ℝ) < y / a := lt_of_not_ge hcap
      have hset :
          {u : ℝ | a * u ≤ y} ∩ Set.Icc (0 : ℝ) 1 =
            Set.Icc (0 : ℝ) 1 := by
        ext u
        constructor
        · intro hu
          exact hu.2
        · intro hu
          refine ⟨?_, hu⟩
          have hule : u ≤ y / a := hu.2.trans hcap'.le
          have hmul : u * a ≤ y := (le_div_iff₀ ha).1 hule
          simpa [mul_comm] using hmul
      rw [hset, Real.volume_Icc]
      simp [hy, min_eq_right hcap'.le]

/-- The conditional CDF formula is derived from the restricted uniform measure. -/
theorem prob_1_6_conditionalCdf_measure (k : Fin 6) (y : ℝ) :
    (prob_1_6_unitUniformMeasure {u : ℝ | ((k : ℕ) : ℝ) * u ≤ y}).toReal =
      prob_1_6_conditionalCdf (k : ℕ) y := by
  by_cases hk : (k : ℕ) = 0
  · have hkreal : ((k : ℕ) : ℝ) = 0 := by exact_mod_cast hk
    rw [hkreal]
    simpa [prob_1_6_conditionalCdf, hk] using prob_1_6_unitUniform_sublevel_zero y
  · have hkpos_nat : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk
    have hkpos : 0 < ((k : ℕ) : ℝ) := by exact_mod_cast hkpos_nat
    rw [prob_1_6_unitUniform_sublevel_pos hkpos]
    simp [prob_1_6_conditionalCdf, hk]

/-- The finite-mixture CDF rewrites to the displayed closed form. -/
theorem prob_1_6_cdf_formula (y : ℝ) :
    cdf_Y y =
      if y < 0 then 0
      else (1 / 6 : ℝ) * (1 + ∑ k ∈ Finset.range 5, min (y / (↑k + 1)) 1) := by
  by_cases hy : y < 0
  · simp [cdf_Y, prob_1_6_conditionalCdf, hy]
  · rw [cdf_Y]
    rw [Finset.sum_range_succ' (fun k => prob_1_6_conditionalCdf k y) 5]
    simp [prob_1_6_conditionalCdf, hy]
    ring

/-- The displayed `cdf_Y` is the actual CDF of `Y = XU` under the product model. -/
theorem prob_1_6_cdf_actual (y : ℝ) :
    (prob_1_6_sampleMeasure {ω : Fin 6 × ℝ | prob_1_6_Y ω ≤ y}).toReal = cdf_Y y := by
  haveI : SFinite prob_1_6_unitUniformMeasure := by
    rw [prob_1_6_unitUniformMeasure]
    infer_instance
  haveI : IsFiniteMeasure prob_1_6_unitUniformMeasure := by
    rw [prob_1_6_unitUniformMeasure]
    infer_instance
  have hmeas : MeasurableSet {ω : Fin 6 × ℝ | prob_1_6_Y ω ≤ y} := by
    change MeasurableSet {ω : Fin 6 × ℝ | (((ω.1 : ℕ) : ℝ) * ω.2) ≤ y}
    have hfst : Measurable fun ω : Fin 6 × ℝ => ((ω.1 : ℕ) : ℝ) :=
      (measurable_of_finite fun k : Fin 6 => ((k : ℕ) : ℝ)).comp measurable_fst
    exact measurableSet_le (hfst.mul measurable_snd) measurable_const
  have hsumENN :
      prob_1_6_sampleMeasure {ω : Fin 6 × ℝ | prob_1_6_Y ω ≤ y} =
        ∑ k : Fin 6,
          prob_1_6_unitUniformMeasure {u : ℝ | ((k : ℕ) : ℝ) * u ≤ y} *
            (1 / 6 : ENNReal) := by
    rw [prob_1_6_sampleMeasure, Measure.prod_apply hmeas, MeasureTheory.lintegral_fintype]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [prob_1_6_die_singleton k]
    rfl
  rw [hsumENN]
  rw [ENNReal.toReal_sum (s := Finset.univ)
    (f := fun k : Fin 6 =>
      prob_1_6_unitUniformMeasure {u : ℝ | ((k : ℕ) : ℝ) * u ≤ y} * (1 / 6 : ENNReal))]
  · simp_rw [ENNReal.toReal_mul]
    have hSix : (1 / 6 : ENNReal).toReal = (1 / 6 : ℝ) := by norm_num
    simp_rw [hSix]
    simp_rw [prob_1_6_conditionalCdf_measure]
    rw [Fin.sum_univ_eq_sum_range (fun k => prob_1_6_conditionalCdf k y * (1 / 6 : ℝ)) 6]
    rw [cdf_Y]
    simp [Finset.mul_sum, mul_comm]
  · intro k hk
    exact ENNReal.mul_ne_top (measure_ne_top prob_1_6_unitUniformMeasure _)
      (by norm_num)

/--
Problem 1.6, parts (a) and (b), packaged together:

1. the cumulative distribution function of the actual variable `Y = XU` is the displayed formula;
2. the expectation of `Y` is `5/4`.
-/
theorem prob_1_6 :
    (∀ y : ℝ,
      (prob_1_6_sampleMeasure {ω : Fin 6 × ℝ | prob_1_6_Y ω ≤ y}).toReal =
        if y < 0 then 0
        else (1 / 6 : ℝ) * (1 + ∑ k ∈ Finset.range 5, min (y / (↑k + 1)) 1)) ∧
    (∫ ω : Fin 6 × ℝ, prob_1_6_Y ω ∂prob_1_6_sampleMeasure = 5 / 4) := by
  refine ⟨?_, ?_⟩
  · intro y
    rw [prob_1_6_cdf_actual, prob_1_6_cdf_formula]
  · haveI : SFinite prob_1_6_unitUniformMeasure := by
      rw [prob_1_6_unitUniformMeasure]
      infer_instance
    change ∫ ω : Fin 6 × ℝ, (((ω.1 : ℕ) : ℝ) * ω.2) ∂prob_1_6_sampleMeasure =
      (5 / 4 : ℝ)
    rw [prob_1_6_sampleMeasure]
    have hprod :
        (∫ ω : Fin 6 × ℝ, (((ω.1 : ℕ) : ℝ) * ω.2)
            ∂prob_1_6_dieMeasure.prod prob_1_6_unitUniformMeasure) =
          (∫ k : Fin 6, ((k : ℕ) : ℝ) ∂prob_1_6_dieMeasure) *
            ∫ u : ℝ, u ∂prob_1_6_unitUniformMeasure := by
      simpa using
        (MeasureTheory.integral_prod_mul
          (μ := prob_1_6_dieMeasure) (ν := prob_1_6_unitUniformMeasure)
          (f := fun k : Fin 6 => ((k : ℕ) : ℝ)) (g := fun u : ℝ => u))
    rw [hprod]
    have hdie :
        ∫ k : Fin 6, ((k : ℕ) : ℝ) ∂prob_1_6_dieMeasure = (5 / 2 : ℝ) := by
      rw [prob_1_6_dieMeasure]
      rw [PMF.integral_eq_sum]
      simp [Fin.sum_univ_succ, prob_1_6_diePMF, PMF.uniformOfFintype_apply]
      norm_num
    have hunit :
        ∫ u : ℝ, u ∂prob_1_6_unitUniformMeasure = (1 / 2 : ℝ) := by
      rw [prob_1_6_unitUniformMeasure]
      rw [integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      simp [integral_id]
    rw [hdie, hunit]
    norm_num

 /-- Part (a): the explicit cumulative distribution function formula for the actual `Y = XU`. -/
theorem prob_1_6a (y : ℝ) :
    (prob_1_6_sampleMeasure {ω : Fin 6 × ℝ | prob_1_6_Y ω ≤ y}).toReal =
      if y < 0 then 0
      else (1 / 6 : ℝ) * (1 + ∑ k ∈ Finset.range 5, min (y / (↑k + 1)) 1) :=
  prob_1_6.1 y

/-- The mean of the continuous uniform measure on `[0,1]`. -/
theorem prob_1_6_unitUniform_mean :
    ∫ u : ℝ, u ∂prob_1_6_unitUniformMeasure = (1 / 2 : ℝ) := by
  rw [prob_1_6_unitUniformMeasure]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp [integral_id]

/-- The mean of the fair die value after subtracting one. -/
theorem prob_1_6_die_mean :
    ∫ k : Fin 6, ((k : ℕ) : ℝ) ∂prob_1_6_dieMeasure = (5 / 2 : ℝ) := by
  rw [prob_1_6_dieMeasure]
  rw [PMF.integral_eq_sum]
  simp [Fin.sum_univ_succ, prob_1_6_diePMF, PMF.uniformOfFintype_apply]
  norm_num

/-- The expectation of the actual random variable `Y = XU` in the product model is `5/4`. -/
theorem prob_1_6_expectation_actual :
    ∫ ω : Fin 6 × ℝ, prob_1_6_Y ω ∂prob_1_6_sampleMeasure = (5 / 4 : ℝ) := by
  haveI : SFinite prob_1_6_unitUniformMeasure := by
    rw [prob_1_6_unitUniformMeasure]
    infer_instance
  change ∫ ω : Fin 6 × ℝ, (((ω.1 : ℕ) : ℝ) * ω.2) ∂prob_1_6_sampleMeasure =
    (5 / 4 : ℝ)
  rw [prob_1_6_sampleMeasure]
  have hprod :
      (∫ ω : Fin 6 × ℝ, (((ω.1 : ℕ) : ℝ) * ω.2)
          ∂prob_1_6_dieMeasure.prod prob_1_6_unitUniformMeasure) =
        (∫ k : Fin 6, ((k : ℕ) : ℝ) ∂prob_1_6_dieMeasure) *
          ∫ u : ℝ, u ∂prob_1_6_unitUniformMeasure := by
    simpa using
      (MeasureTheory.integral_prod_mul
        (μ := prob_1_6_dieMeasure) (ν := prob_1_6_unitUniformMeasure)
        (f := fun k : Fin 6 => ((k : ℕ) : ℝ)) (g := fun u : ℝ => u))
  rw [hprod, prob_1_6_die_mean, prob_1_6_unitUniform_mean]
  norm_num

/-- Part (b): the expectation of `Y = XU` is `5/4`. -/
theorem prob_1_6b :
    ∫ ω : Fin 6 × ℝ, prob_1_6_Y ω ∂prob_1_6_sampleMeasure = (5 / 4 : ℝ) :=
  prob_1_6.2
