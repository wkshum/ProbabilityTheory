import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Stieltjes
import ProbabilityTheory.chapter_01.def_1_2

open MeasureTheory intervalIntegral Set
open scoped Pointwise

noncomputable section

/-!
Stieltjes measure wrappers for the local RS bridge family.
This is a mechanical split from the old mixed `rs_stieltjes_bridge` body.
-/
instance (μ : Measure ℝ) : Preorder (NullMeasurableSpace ℝ μ) := inferInstanceAs (Preorder ℝ)
instance (μ : Measure ℝ) : PartialOrder (NullMeasurableSpace ℝ μ) :=
  inferInstanceAs (PartialOrder ℝ)
instance (μ : Measure ℝ) : LinearOrder (NullMeasurableSpace ℝ μ) :=
  inferInstanceAs (LinearOrder ℝ)

/-- The Stieltjes measure determined by a monotone integrator. -/
def rsMeasureLocal (α : ℝ → ℝ) (hα : Monotone α) : Measure ℝ :=
  hα.stieltjesFunction.measure

/-- RS integrability on a finite interval, modeled by integrability on `[a,b]` against the
associated Stieltjes measure. -/
def RSStieltjesIntegrableOn (f α : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ hα : Monotone α, IntegrableOn f (Ioc a b) (rsMeasureLocal α hα)

/-- The RS integral on a finite interval. Non-monotone integrators are assigned value `0`. -/
noncomputable def rsStieltjesIntegralOn (f α : ℝ → ℝ) (a b : ℝ) : ℝ := by
  classical
  exact if hα : Monotone α then ∫ x in Ioc a b, f x ∂(rsMeasureLocal α hα) else 0

/-- When the integrator is already a `StieltjesFunction`, the local RS measure is the same measure. -/
lemma rsMeasureLocal_eq_measure (F : StieltjesFunction ℝ) :
    rsMeasureLocal F F.mono = F.measure := by
  unfold rsMeasureLocal
  have hsf : (F.mono).stieltjesFunction = F := by
    ext x
    rw [Monotone.stieltjesFunction_eq, F.rightLim_eq]
  simpa [hsf]

/-- The local Stieltjes measure is finite on every compact interval. -/
lemma rsMeasureLocal_Icc_lt_top (α : ℝ → ℝ) (hα : Monotone α) (a b : ℝ) :
    rsMeasureLocal α hα (Icc a b) < ⊤ := by
  simpa [rsMeasureLocal] using
    (measure_Icc_lt_top (μ := hα.stieltjesFunction.measure) (a := a) (b := b))

/-- The local Stieltjes measure is finite on every half-open compact interval. -/
lemma rsMeasureLocal_Ioc_lt_top (α : ℝ → ℝ) (hα : Monotone α) (a b : ℝ) :
    rsMeasureLocal α hα (Ioc a b) < ⊤ := by
  simpa [rsMeasureLocal] using
    (measure_Ioc_lt_top (μ := hα.stieltjesFunction.measure) (a := a) (b := b))

/-- A continuous integrand on a compact interval is integrable against the local Stieltjes measure. -/
theorem rsStieltjesIntegrableOn_of_continuousOn
    {f α : ℝ → ℝ} {a b : ℝ} (hα : Monotone α)
    (hf : ContinuousOn f (Icc a b)) :
    RSStieltjesIntegrableOn f α a b := by
  refine ⟨hα, ?_⟩
  have hIcc : IntegrableOn f (Icc a b) (rsMeasureLocal α hα) := by
    simpa [rsMeasureLocal] using
      (hf.integrableOn_Icc (μ := hα.stieltjesFunction.measure))
  exact hIcc.mono_set Ioc_subset_Icc_self

/-- A bounded measurable integrand on `[a,b]` is integrable against the local Stieltjes measure. -/
theorem rsStieltjesIntegrableOn_of_bounded_measurableOn_Icc
    {f α : ℝ → ℝ} {a b : ℝ} (hα : Monotone α)
    (hf_meas : Measurable ((Icc a b).restrict f))
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    RSStieltjesIntegrableOn f α a b := by
  refine ⟨hα, ?_⟩
  obtain ⟨U, hU⟩ := hAbove
  obtain ⟨L, hL⟩ := hBelow
  let C : ℝ := max |L| |U|
  have hC : ∀ x ∈ Icc a b, ‖f x‖ ≤ C := by
    intro x hx
    have hLfx : L ≤ f x := hL ⟨x, hx, rfl⟩
    have hfxU : f x ≤ U := hU ⟨x, hx, rfl⟩
    have hLower : -C ≤ f x := by
      calc
        -C ≤ -|L| := by
          dsimp [C]
          gcongr
          exact le_max_left |L| |U|
        _ ≤ L := by simpa using neg_abs_le L
        _ ≤ f x := hLfx
    have hUpper : f x ≤ C := by
      calc
        f x ≤ U := hfxU
        _ ≤ |U| := le_abs_self U
        _ ≤ C := by
          dsimp [C]
          exact le_max_right |L| |U|
    simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hLower, hUpper⟩)
  have hf_aesm :
      AEStronglyMeasurable f ((rsMeasureLocal α hα).restrict (Icc a b)) := by
    let g : ℝ → ℝ := Set.piecewise (Icc a b) f (fun _ => 0)
    have hg_meas : Measurable g := by
      refine measurable_of_restrict_of_restrict_compl (s := Icc a b) measurableSet_Icc ?_ ?_
      · simpa [g] using hf_meas
      · have hg_zero : ((Icc a b)ᶜ).restrict g = fun _ => (0 : ℝ) := by
          funext x
          simpa [g] using
            (Set.piecewise_eq_of_notMem (s := Icc a b) (f := f) (g := fun _ : ℝ => 0) x.property)
        rw [hg_zero]
        exact measurable_const
    have hg_eq : g =ᵐ[(rsMeasureLocal α hα).restrict (Icc a b)] f := by
      simpa [g] using (piecewise_ae_eq_restrict (μ := rsMeasureLocal α hα) measurableSet_Icc)
    exact hg_meas.aemeasurable.aestronglyMeasurable.congr hg_eq
  exact
    (IntegrableOn.of_bound (rsMeasureLocal_Icc_lt_top α hα a b) hf_aesm C <| by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall hC).mono_set Ioc_subset_Icc_self

