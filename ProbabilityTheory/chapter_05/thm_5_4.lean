import Mathlib.Tactic
import ProbabilityTheory.chapter_05.thm_5_5

/-
  # Theorem 5.4
  Independence of continuous distributions
-/

open MeasureTheory Set

noncomputable def jointCDF {Ω : Type _} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (x y : ℝ) : ENNReal :=
  μ (X ⁻¹' Set.Iic x ∩ Y ⁻¹' Set.Iic y)

noncomputable def marginalCDF {Ω : Type _} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (x : ℝ) : ENNReal :=
  μ (X ⁻¹' Set.Iic x)


/--
  ## Independence of two continuous distributions
-/
theorem thm_5_4 {Ω : Type _} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    ProbabilityTheory.IndepFun X Y μ ↔
      ∀ x y : ℝ,
        jointCDF μ X Y x y = marginalCDF μ X x * marginalCDF μ Y y := by
  constructor
  · intro hXY x y
    rw [jointCDF, marginalCDF]
    have hpre := (ProbabilityTheory.indepFun_iff_indepSet_preimage (μ := μ) hX hY).1 hXY
    exact
      (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
        (hX measurableSet_Iic)
        (hY measurableSet_Iic)
        (μ := μ)).1 (hpre (Set.Iic x) (Set.Iic y) measurableSet_Iic measurableSet_Iic)
  · intro hCDF
    let C : Set (Set ℝ) := ⋃ a : ℚ, ({Set.Iic (a : ℝ)} : Set (Set ℝ))
    have hRat :
        ∀ A B, A ∈ C → B ∈ C → ProbabilityTheory.IndepSet (X ⁻¹' A) (Y ⁻¹' B) μ := by
      intro A B hA hB
      rcases Set.mem_iUnion.1 hA with ⟨a, ha⟩
      rcases Set.mem_singleton_iff.1 ha with rfl
      rcases Set.mem_iUnion.1 hB with ⟨b, hb⟩
      rcases Set.mem_singleton_iff.1 hb with rfl
      rw [ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
        (hX measurableSet_Iic) (hY measurableSet_Iic) (μ := μ)]
      simpa [jointCDF, marginalCDF] using hCDF (a : ℝ) (b : ℝ)
    exact thm_5_5 μ X Y hX hY C Real.isPiSystem_Iic_rat Real.borel_eq_generateFrom_Iic_rat hRat
