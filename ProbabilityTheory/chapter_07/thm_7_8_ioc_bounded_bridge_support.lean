import ToyApollo.Output.thm_7_8_ioc_bridge_support

open Finset BigOperators
open MeasureTheory Set
open Topology

noncomputable section

/-!
Bounded-measurable half-open bridge support for Chapter 7.

The already reviewed continuous `Ioc` bridge uses two ingredients: finite
Lebesgue-Stieltjes integrability on `Ioc a b`, and the Darboux squeeze between
lower/upper Riemann-Stieltjes sums. This file exposes the same bridge when
integrability comes from measurability plus boundedness on `Icc a b`, while RS
integrability is supplied separately.
-/

/-- A bounded function that is measurable on `[a,b]` is integrable on `(a,b]`
against the Stieltjes measure of `F`. -/
theorem thm_7_8_integrableOn_Ioc_of_bounded_measurableOn_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hgMeas : Measurable ((Icc a b).restrict g))
    (hAbove : BddAbove (g '' Icc a b))
    (hBelow : BddBelow (g '' Icc a b)) :
    IntegrableOn g (Ioc a b) F.measure := by
  obtain ⟨U, hU⟩ := hAbove
  obtain ⟨L, hL⟩ := hBelow
  let C : ℝ := max |L| |U|
  have hC : ∀ x ∈ Icc a b, ‖g x‖ ≤ C := by
    intro x hx
    have hLgx : L ≤ g x := hL ⟨x, hx, rfl⟩
    have hgxU : g x ≤ U := hU ⟨x, hx, rfl⟩
    have hLower : -C ≤ g x := by
      calc
        -C ≤ -|L| := by
          dsimp [C]
          gcongr
          exact le_max_left |L| |U|
        _ ≤ L := by simpa using neg_abs_le L
        _ ≤ g x := hLgx
    have hUpper : g x ≤ C := by
      calc
        g x ≤ U := hgxU
        _ ≤ |U| := le_abs_self U
        _ ≤ C := by
          dsimp [C]
          exact le_max_right |L| |U|
    simpa [Real.norm_eq_abs] using (abs_le.mpr ⟨hLower, hUpper⟩)
  have hgAes :
      AEStronglyMeasurable g (F.measure.restrict (Icc a b)) := by
    let g0 : ℝ → ℝ := Set.piecewise (Icc a b) g (fun _ => 0)
    have hg0Meas : Measurable g0 := by
      refine measurable_of_restrict_of_restrict_compl (s := Icc a b)
        measurableSet_Icc ?_ ?_
      · simpa [g0] using hgMeas
      · have hg0Zero : ((Icc a b)ᶜ).restrict g0 = fun _ => (0 : ℝ) := by
          funext x
          simpa [g0] using
            (Set.piecewise_eq_of_notMem
              (s := Icc a b) (f := g) (g := fun _ : ℝ => 0) x.property)
        rw [hg0Zero]
        exact measurable_const
    have hg0Eq : g0 =ᵐ[F.measure.restrict (Icc a b)] g := by
      simpa [g0] using
        (piecewise_ae_eq_restrict (μ := F.measure) measurableSet_Icc)
    exact hg0Meas.aemeasurable.aestronglyMeasurable.congr hg0Eq
  exact
    (IntegrableOn.of_bound
      (measure_Icc_lt_top (μ := F.measure) (a := a) (b := b))
      hgAes C <| by
        rw [ae_restrict_iff' measurableSet_Icc]
        exact Filter.Eventually.of_forall hC).mono_set Ioc_subset_Icc_self

/-- Half-open LS/RS equality from bounded measurable LS integrability plus an
independent finite RS-integrability witness. -/
theorem thm_7_8_ioc_bridge_of_rs_integrable_bounded_measurableOn
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hgMeas : Measurable ((Icc a b).restrict g))
    (hAbove : BddAbove (g '' Icc a b))
    (hBelow : BddBelow (g '' Icc a b))
    (hRS : RSIntegrable g F a b) :
    IntegrableOn g (Ioc a b) F.measure ∧
      ∃ hRS' : RSIntegrable g F a b,
        ∫ x in Ioc a b, g x ∂F.measure = rsIntegral g F a b hRS' := by
  have hgIntIoc : IntegrableOn g (Ioc a b) F.measure :=
    thm_7_8_integrableOn_Ioc_of_bounded_measurableOn_Icc
      F hgMeas hAbove hBelow
  have hSqueeze : ∀ P : DarbouxRS.Partition a b,
      DarbouxRS.lowerSum P g F ≤ ∫ x in Ioc a b, g x ∂F.measure ∧
        ∫ x in Ioc a b, g x ∂F.measure ≤ DarbouxRS.upperSum P g F := by
    intro P
    exact thm_7_8_cellStep_integral_sandwich_Ioc F P g
      (thm_7_8_lowerCellStep_le_on_Ioc P g hBelow)
      (thm_7_8_le_upperCellStep_on_Ioc P g hAbove)
      hgIntIoc
  exact ⟨hgIntIoc,
    ⟨hRS, thm_7_8_common_limit_squeeze_rsIntegral F hRS hSqueeze⟩⟩
