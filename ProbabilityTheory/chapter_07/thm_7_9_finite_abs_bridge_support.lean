import ToyApollo.Output.thm_7_9_bounded_finite_bridge_support
import ToyApollo.Output.thm_7_9_piecewise_regular_support

open MeasureTheory Set

noncomputable section

/-!
Finite absolute truncation bridge support for Theorem 7.9.

This file keeps the finite bridge as ordinary Chapter 7 family support rather
than as public `obl_*` modules. It deliberately does not prove the reverse
bound, DCT value equality, improper-filter bookkeeping, or final Theorem 7.9.
-/

/-- Endpoint-route packaging for a continuous finite-interval integrand. -/
theorem thm_7_9_finite_abs_endpoint_route
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Icc a b)) :
    IntegrableOn g (Icc a b) F.measure ∧
      IntegrableOn g (Ioc a b) F.measure ∧
      (∫ x in Icc a b, g x ∂F.measure =
        (F.measure {a}).toReal * g a + ∫ x in Ioc a b, g x ∂F.measure) ∧
      ∃ hRS : RSIntegrable g F a b,
        ∫ x in Ioc a b, g x ∂F.measure = rsIntegral g F a b hRS := by
  have hgIntIcc : IntegrableOn g (Icc a b) F.measure :=
    thm_7_8_integrability F hg
  have hEndpoint :
      ∫ x in Icc a b, g x ∂F.measure =
        (F.measure {a}).toReal * g a + ∫ x in Ioc a b, g x ∂F.measure :=
    thm_7_9_integral_Icc_eq_singleton_add_Ioc F (le_of_lt hab) hgIntIcc
  have hIoc := thm_7_8_ioc_bridge F hab hg
  exact ⟨hgIntIcc, hIoc.1, hEndpoint, hIoc.2⟩

/-- The finite-discontinuity surface supplies the finite absolute source
regularity used by the finite bridge route. -/
theorem thm_7_9_finite_abs_source_regular
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) :
    Thm79SourceRegular F g ∧
      Measurable (fun x => |g x|) ∧
      (∀ ⦃a b : ℝ⦄, a < b → RSIntegrable (fun x => |g x|) F a b) ∧
      (∀ ⦃n : ℕ⦄, 0 < n →
        RSIntegrable (thm_7_9_trunc (fun x => |g x|) n) F (-(n : ℝ)) (n : ℝ)) := by
  let hreg : Thm79SourceRegular F g := h.to_source_regular
  refine ⟨hreg, hreg.abs_measurable, ?_, ?_⟩
  · intro a b hab
    exact hreg.finite_abs_rs hab
  · intro n hn
    exact hreg.abs_trunc_rs hn

/-- Finite-interval bridge for absolute-value truncations in Theorem 7.9. -/
theorem thm_7_9_finite_abs_bridge
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (thm_7_9_trunc (fun x => |g x|) n)
        (Icc (-(n : ℝ)) (n : ℝ)) F.measure ∧
      ∃ hRS : RSIntegrable (thm_7_9_trunc (fun x => |g x|) n)
          F (-(n : ℝ)) (n : ℝ),
        ∫ x in Icc (-(n : ℝ)) (n : ℝ),
            thm_7_9_trunc (fun y => |g y|) n x ∂F.measure =
          (F.measure {-(n : ℝ)}).toReal *
              thm_7_9_trunc (fun y => |g y|) n (-(n : ℝ)) +
            rsIntegral (thm_7_9_trunc (fun y => |g y|) n)
              F (-(n : ℝ)) (n : ℝ) hRS := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlt : -(n : ℝ) < (n : ℝ) := by
    linarith
  let f : ℝ → ℝ := thm_7_9_trunc (fun x => |g x|) n
  have hfMeas : Measurable f := by
    dsimp [f]
    exact thm_7_9_trunc_measurable h.measurable.abs n
  have hfMeasRestrict :
      Measurable ((Icc (-(n : ℝ)) (n : ℝ)).restrict f) := by
    exact hfMeas.comp measurable_subtype_coe
  have hAbsBounds := h.finite_abs_bounds hlt
  have hAbove : BddAbove (f '' Icc (-(n : ℝ)) (n : ℝ)) := by
    rcases hAbsBounds.1 with ⟨U, hU⟩
    refine ⟨U, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hfx : f x = |g x| := by
      dsimp [f]
      exact Set.indicator_of_mem hx (fun y => |g y|)
    rw [hfx]
    exact hU ⟨x, hx, rfl⟩
  have hBelow : BddBelow (f '' Icc (-(n : ℝ)) (n : ℝ)) := by
    rcases hAbsBounds.2 with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hfx : f x = |g x| := by
      dsimp [f]
      exact Set.indicator_of_mem hx (fun y => |g y|)
    rw [hfx]
    exact hL ⟨x, hx, rfl⟩
  have hfAes : AEStronglyMeasurable f F.measure :=
    hfMeas.aestronglyMeasurable
  have hAboveBridge := hAbove
  have hBelowBridge := hBelow
  obtain ⟨U, hU⟩ := hAbove
  obtain ⟨L, hL⟩ := hBelow
  let C : ℝ := max |L| |U|
  have hC : ∀ x ∈ Icc (-(n : ℝ)) (n : ℝ), ‖f x‖ ≤ C := by
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
  have hIcc : IntegrableOn f (Icc (-(n : ℝ)) (n : ℝ)) F.measure :=
    Measure.integrableOn_of_bounded
      (μ := F.measure) (s := Icc (-(n : ℝ)) (n : ℝ))
      (measure_Icc_lt_top (μ := F.measure)
        (a := (-(n : ℝ))) (b := (n : ℝ))).ne
      hfAes <| by
        rw [ae_restrict_iff' measurableSet_Icc]
        exact Filter.Eventually.of_forall hC
  have hRS : RSIntegrable f F (-(n : ℝ)) (n : ℝ) := by
    dsimp [f]
    exact h.to_source_regular.abs_trunc_rs hn
  have hpack :=
    thm_7_9_Icc_eq_endpoint_add_rs_of_bounded_measurableOn
      F (le_of_lt hlt) hIcc hfMeasRestrict hAboveBridge hBelowBridge hRS
  rcases hpack with ⟨hIcc', _hIoc, _hEndpoint, hEq⟩
  constructor
  · simpa [f] using hIcc'
  · rcases hEq with ⟨hRS', hEq'⟩
    refine ⟨hRS', ?_⟩
    simpa [f] using hEq'

/-- Endpoint-corrected closed-interval LS/RS bridge for a continuous absolute
truncation. -/
theorem thm_7_9_abs_trunc_Icc_eq_endpoint_add_rs
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ} {n : ℕ}
    (hn : 0 < n)
    (hcont : ContinuousOn (thm_7_9_trunc (fun x => |g x|) n)
      (Icc (-(n : ℝ)) (n : ℝ))) :
    IntegrableOn (thm_7_9_trunc (fun x => |g x|) n)
        (Icc (-(n : ℝ)) (n : ℝ)) F.measure ∧
      ∃ hRS : RSIntegrable (thm_7_9_trunc (fun x => |g x|) n)
          F (-(n : ℝ)) (n : ℝ),
        ∫ x in Icc (-(n : ℝ)) (n : ℝ),
            thm_7_9_trunc (fun y => |g y|) n x ∂F.measure =
          (F.measure {-(n : ℝ)}).toReal *
              thm_7_9_trunc (fun y => |g y|) n (-(n : ℝ)) +
            rsIntegral (thm_7_9_trunc (fun x => |g x|) n)
              F (-(n : ℝ)) (n : ℝ) hRS := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlt : -(n : ℝ) < (n : ℝ) := by
    linarith
  let f : ℝ → ℝ := thm_7_9_trunc (fun x => |g x|) n
  have hpack :=
    thm_7_9_finite_abs_endpoint_route
      (F := F) (a := (-(n : ℝ))) (b := (n : ℝ)) (g := f) hlt hcont
  rcases hpack with ⟨hIcc, _hIoc, hEndpoint, hRSex⟩
  constructor
  · exact hIcc
  · rcases hRSex with ⟨hRS, hIocEq⟩
    refine ⟨hRS, ?_⟩
    dsimp [f] at hEndpoint hIocEq ⊢
    rw [hEndpoint, hIocEq]
