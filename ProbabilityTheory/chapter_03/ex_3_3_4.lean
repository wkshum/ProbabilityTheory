import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Dirac


/-

  # Example 3.3.4 Dirac measure

-/

open MeasureTheory Set Function Filter


/-- The jump function used to realize a point mass at `x₀`. -/
noncomputable def dirac_step_fun (x₀ x : ℝ) : ℝ :=
  if x < x₀ then 0 else 1

/-- The jump function is monotone. -/
theorem monotone_dirac_step_fun (x₀ : ℝ) : Monotone (dirac_step_fun x₀) := by
  intro x y hxy
  by_cases hy : y < x₀
  · have hx : x < x₀ := lt_of_le_of_lt hxy hy
    simp [dirac_step_fun, hx, hy]
  · by_cases hx : x < x₀
    · simp [dirac_step_fun, hx, hy]
    · simp [dirac_step_fun, hx, hy]

/-- The Stieltjes function attached to the jump at `x₀`. -/
noncomputable def dirac_step_function (x₀ : ℝ) : StieltjesFunction ℝ :=
  (monotone_dirac_step_fun x₀).stieltjesFunction

/-- The Stieltjes function has the expected step-function values. -/
theorem dirac_step_function_apply (x₀ x : ℝ) :
    dirac_step_function x₀ x = if x < x₀ then 0 else 1 := by
  rw [dirac_step_function, Monotone.stieltjesFunction_eq]
  by_cases hx : x < x₀
  · apply rightLim_eq_of_tendsto (nhdsGT_neBot x).ne
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show x < (x + x₀) / 2 by linarith)] with y hy
    have hmid : (x + x₀) / 2 < x₀ := by linarith
    have hyx₀ : y < x₀ := lt_trans hy.2 hmid
    have hval : dirac_step_fun x₀ y = 0 := by
      simp [dirac_step_fun, hyx₀]
    simpa [hval]
  · apply rightLim_eq_of_tendsto (nhdsGT_neBot x).ne
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show x < x + 1 by linarith)] with y hy
    have hx₀ : x₀ ≤ x := le_of_not_gt hx
    have hyx₀ : ¬ y < x₀ := by linarith [le_of_not_gt hx, hy.1]
    have hval : dirac_step_fun x₀ y = 1 := by
      simp [dirac_step_fun, hyx₀]
    simpa [hval]

/-- The jump-function Stieltjes function tends to `0` at `-∞`. -/
theorem dirac_step_function_tendsto_atBot (x₀ : ℝ) :
    Tendsto (dirac_step_function x₀) atBot (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  refine Filter.eventually_atBot.2 ?_
  refine ⟨x₀ - 1, ?_⟩
  intro x hx
  have hxx₀ : x < x₀ := by linarith
  simp [dirac_step_function_apply, hxx₀]

/-- The jump-function Stieltjes function tends to `1` at `+∞`. -/
theorem dirac_step_function_tendsto_atTop (x₀ : ℝ) :
    Tendsto (dirac_step_function x₀) atTop (nhds 1) := by
  refine tendsto_const_nhds.congr' ?_
  refine Filter.eventually_atTop.2 ?_
  refine ⟨x₀, ?_⟩
  intro x hx
  have hxx₀ : ¬ x < x₀ := not_lt.mpr hx
  simp [dirac_step_function_apply, hxx₀]

/-- The measure induced by the jump Stieltjes function is the Dirac measure at `x₀`. -/
theorem dirac_step_measure_eq_dirac (x₀ : ℝ) :
    (dirac_step_function x₀).measure = Measure.dirac x₀ := by
  have h_univ : (dirac_step_function x₀).measure univ = 1 := by
    simpa using
      (StieltjesFunction.measure_univ (dirac_step_function x₀)
        (dirac_step_function_tendsto_atBot x₀)
        (dirac_step_function_tendsto_atTop x₀))
  letI : IsFiniteMeasure ((dirac_step_function x₀).measure) := ⟨by simp [h_univ]⟩
  refine Measure.ext_of_Iic (dirac_step_function x₀).measure (Measure.dirac x₀) fun x => ?_
  rw [StieltjesFunction.measure_Iic (dirac_step_function x₀)
    (dirac_step_function_tendsto_atBot x₀)]
  by_cases hx : x < x₀
  · simp [dirac_step_function_apply, hx, not_le_of_gt hx]
  · simp [dirac_step_function_apply, hx, le_of_not_gt hx]

/-- The point mass puts probability `1` on the singleton `{x₀}`. -/
theorem dirac_step_measure_singleton (x₀ : ℝ) :
    (dirac_step_function x₀).measure {x₀} = 1 := by
  rw [dirac_step_measure_eq_dirac]
  simp

/--
Example 3.3.4: the jump Stieltjes function produces the Dirac point mass at `x₀`, so every set
gets probability `1` iff it contains `x₀`.
-/
theorem ex_3_3_4 (x₀ : ℝ) (A : Set ℝ) :
    (dirac_step_function x₀).measure A = A.indicator 1 x₀ := by
  rw [dirac_step_measure_eq_dirac]
  simp

/-- Any set containing `x₀` has probability `1` under the induced measure. -/
theorem dirac_step_measure_of_mem (x₀ : ℝ) (A : Set ℝ) (hx : x₀ ∈ A) :
    (dirac_step_function x₀).measure A = 1 := by
  rw [ex_3_3_4]
  simp [hx]

/-- Any set not containing `x₀` has probability `0` under the induced measure. -/
theorem dirac_step_measure_of_notMem (x₀ : ℝ) (A : Set ℝ) (hx : x₀ ∉ A) :
    (dirac_step_function x₀).measure A = 0 := by
  rw [ex_3_3_4]
  simp [hx]
