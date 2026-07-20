import ToyApollo.Output.thm_7_9_finite_abs_bridge_support
import ToyApollo.Output.thm_7_9_mct_support

open MeasureTheory Set

noncomputable section

/-!
Reverse-bound support for Theorem 7.9.

This file proves the finite absolute RS truncation bound used in the reverse
direction. It does not prove the remaining Definition 1.4 tail-control step or
the final improper absolute convergence theorem.
-/

lemma thm_7_9_setIntegral_abs_trunc_eq_integral
    (μ : Measure ℝ) (g : ℝ → ℝ) (n : ℕ) :
    (∫ x in Icc (-(n : ℝ)) (n : ℝ),
        thm_7_9_trunc (fun y => |g y|) n x ∂μ) =
      ∫ x, thm_7_9_trunc (fun y => |g y|) n x ∂μ := by
  rw [← integral_indicator (μ := μ)
    (f := thm_7_9_trunc (fun y => |g y|) n) measurableSet_Icc]
  refine integral_congr_ae ?_
  filter_upwards with x
  by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · simp [thm_7_9_trunc, hx]
  · simp [thm_7_9_trunc, hx]

lemma thm_7_9_rsTruncIntegral_zero_zero
    (f α : ℝ → ℝ) :
    rsTruncIntegral f α 0 0 = 0 := by
  unfold rsTruncIntegral
  by_cases h : RSIntegrable f α 0 0
  · have hsrc := rsIntegral_source_spec h
    have hlt : (0 : ℝ) < 0 := hsrc.1.1
    exact False.elim ((lt_irrefl (0 : ℝ)) hlt)
  · simp [h]

lemma thm_7_9_nat_Ioc_subset {n m : ℕ} (hnm : n ≤ m) :
    Ioc (-(n : ℝ)) (n : ℝ) ⊆ Ioc (-(m : ℝ)) (m : ℝ) := by
  intro x hx
  have hnmR : (n : ℝ) ≤ m := by
    exact_mod_cast hnm
  constructor
  · linarith [hx.1]
  · exact le_trans hx.2 hnmR

/-- The guarded finite RS truncation of `|g|` over `[-n,n]` is exactly the
Lebesgue-Stieltjes integral over the half-open interval `(−n,n]`. This is the
endpoint-safe form needed for monotonicity. -/
theorem thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g) {n : ℕ} (hn : 0 < n) :
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) =
      ∫ x in Ioc (-(n : ℝ)) (n : ℝ), |g x| ∂F.measure := by
  have hlt : -(n : ℝ) < (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  let f : ℝ → ℝ := thm_7_9_trunc (fun x => |g x|) n
  have hOrig : RSIntegrable (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) :=
    h.to_source_regular.finite_abs_rs hlt
  have hEqOn : ∀ x ∈ Icc (-(n : ℝ)) (n : ℝ), f x = |g x| := by
    intro x hx
    dsimp [f]
    exact Set.indicator_of_mem hx (fun y => |g y|)
  let hTrunc : RSIntegrable f F (-(n : ℝ)) (n : ℝ) :=
    rsIntegrable_congr_integrand_Icc hOrig hEqOn
  have hTruncOrig :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc =
        rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig := by
    dsimp [hTrunc]
    exact rsIntegral_congr_integrand_Icc hOrig hEqOn
  have hRsTruncOrig :
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) =
        rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig := by
    unfold rsTruncIntegral
    by_cases hIf : RSIntegrable (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
    · simp [hIf]
    · exact False.elim (hIf hOrig)
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
    have hfx : f x = |g x| := hEqOn x hx
    rw [hfx]
    exact hU ⟨x, hx, rfl⟩
  have hBelow : BddBelow (f '' Icc (-(n : ℝ)) (n : ℝ)) := by
    rcases hAbsBounds.2 with ⟨L, hL⟩
    refine ⟨L, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hfx : f x = |g x| := hEqOn x hx
    rw [hfx]
    exact hL ⟨x, hx, rfl⟩
  have hIoc :=
    thm_7_8_ioc_bridge_of_rs_integrable_bounded_measurableOn
      F hfMeasRestrict hAbove hBelow hTrunc
  rcases hIoc with ⟨_hIntIoc, hEqIoc⟩
  rcases hEqIoc with ⟨hRSIoc, hIocEq⟩
  have hIocEqAbs :
      (∫ x in Ioc (-(n : ℝ)) (n : ℝ), f x ∂F.measure) =
        ∫ x in Ioc (-(n : ℝ)) (n : ℝ), |g x| ∂F.measure := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro x hx
    exact hEqOn x (Ioc_subset_Icc_self hx)
  have hRSIocTrunc :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSIoc =
        rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := by
    exact DarbouxRS.taggedCommonLimit_unique
      (rsIntegral_spec hRSIoc) (rsIntegral_spec hTrunc)
  calc
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
        = rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig :=
          hRsTruncOrig
    _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := hTruncOrig.symm
    _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSIoc := hRSIocTrunc.symm
    _ = ∫ x in Ioc (-(n : ℝ)) (n : ℝ), f x ∂F.measure := hIocEq.symm
    _ = ∫ x in Ioc (-(n : ℝ)) (n : ℝ), |g x| ∂F.measure := hIocEqAbs

/-- Each finite absolute RS truncation is bounded by the whole-line
Lebesgue-Stieltjes integral of `|g|`. The proof uses the reviewed
endpoint-corrected finite bridge, not the old Chapter 7 debt shortcut. -/
theorem thm_7_9_symmetric_abs_rs_bound_by_total_ls
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) {n : ℕ} (hn : 0 < n) :
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) ≤
      ∫ x, |g x| ∂F.measure := by
  have hlt : -(n : ℝ) < (n : ℝ) := by
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  let f : ℝ → ℝ := thm_7_9_trunc (fun x => |g x|) n
  have hOrig : RSIntegrable (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) :=
    h.to_source_regular.finite_abs_rs hlt
  have hEqOn : ∀ x ∈ Icc (-(n : ℝ)) (n : ℝ), f x = |g x| := by
    intro x hx
    dsimp [f]
    exact Set.indicator_of_mem hx (fun y => |g y|)
  let hTrunc : RSIntegrable f F (-(n : ℝ)) (n : ℝ) :=
    rsIntegrable_congr_integrand_Icc hOrig hEqOn
  have hTruncOrig :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc =
        rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig := by
    dsimp [hTrunc]
    exact rsIntegral_congr_integrand_Icc hOrig hEqOn
  have hRsTruncOrig :
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) =
        rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig := by
    unfold rsTruncIntegral
    by_cases hIf : RSIntegrable (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
    · simp [hIf]
    · exact False.elim (hIf hOrig)
  rcases
      thm_7_9_finite_abs_bridge
        F h hn with
    ⟨_hIcc, hBridge⟩
  rcases hBridge with ⟨hRSBridge, hBridgeEq⟩
  have hBridgeTrunc :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge =
        rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := by
    exact DarbouxRS.taggedCommonLimit_unique
      (rsIntegral_spec hRSBridge) (rsIntegral_spec hTrunc)
  have hRsTruncBridge :
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) =
        rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge := by
    calc
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
          = rsIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) hOrig :=
            hRsTruncOrig
      _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hTrunc := hTruncOrig.symm
      _ = rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge :=
            hBridgeTrunc.symm
  have hEndpointNonneg :
      0 ≤ (F.measure {-(n : ℝ)}).toReal * f (-(n : ℝ)) := by
    exact mul_nonneg ENNReal.toReal_nonneg (by
      dsimp [f]
      exact thm_7_9_abs_trunc_nonneg g n (-(n : ℝ)))
  have hBridgeValueLeSet :
      rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge ≤
        ∫ x in Icc (-(n : ℝ)) (n : ℝ), f x ∂F.measure := by
    rw [hBridgeEq]
    linarith
  have hSetEqGlobal :
      (∫ x in Icc (-(n : ℝ)) (n : ℝ), f x ∂F.measure) =
        ∫ x, f x ∂F.measure := by
    dsimp [f]
    exact thm_7_9_setIntegral_abs_trunc_eq_integral F.measure g n
  have hGlobalLe :
      (∫ x, f x ∂F.measure) ≤ ∫ x, |g x| ∂F.measure := by
    dsimp [f]
    exact thm_7_9_integral_abs_trunc_le_integral_abs
      F.measure h.measurable hAbs n
  calc
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)
        = rsIntegral f F (-(n : ℝ)) (n : ℝ) hRSBridge := hRsTruncBridge
    _ ≤ ∫ x in Icc (-(n : ℝ)) (n : ℝ), f x ∂F.measure := hBridgeValueLeSet
    _ = ∫ x, f x ∂F.measure := hSetEqGlobal
    _ ≤ ∫ x, |g x| ∂F.measure := hGlobalLe

/-- The symmetric absolute RS truncation values are bounded above. This is the
sequence-level boundedness needed before applying the monotone convergence
bookkeeping for the reverse direction. -/
theorem thm_7_9_symmetric_abs_rs_bddAbove_by_total_ls
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) :
    ∃ C : ℝ, ∀ n : ℕ,
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) ≤ C := by
  let total : ℝ := ∫ x, |g x| ∂F.measure
  refine
    ⟨max (rsTruncIntegral (fun x => |g x|) F (-(0 : ℝ)) (0 : ℝ)) total,
      ?_⟩
  intro n
  cases n with
  | zero =>
      simpa using
        (le_max_left
          (rsTruncIntegral (fun x => |g x|) F (-(0 : ℝ)) (0 : ℝ)) total)
  | succ k =>
      have hk : 0 < k.succ := Nat.succ_pos k
      exact le_trans
        (thm_7_9_symmetric_abs_rs_bound_by_total_ls F h hAbs hk)
        (le_max_right
          (rsTruncIntegral (fun x => |g x|) F (-(0 : ℝ)) (0 : ℝ)) total)

/-- The symmetric absolute finite RS truncation values form an increasing
sequence. The proof uses the half-open `(−n,n]` LS identification above, so no
closed-interval endpoint atom is silently dropped. -/
theorem thm_7_9_symmetric_abs_rs_monotone
    (F : StieltjesFunction ℝ) {g : ℝ → ℝ}
    (h : Thm79FiniteDiscontinuityInputs F g)
    (hAbs : Integrable (fun x => |g x|) F.measure) :
    Monotone (fun n : ℕ =>
      rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ)) := by
  intro n m hnm
  change
    rsTruncIntegral (fun x => |g x|) F (-(n : ℝ)) (n : ℝ) ≤
      rsTruncIntegral (fun x => |g x|) F (-(m : ℝ)) (m : ℝ)
  by_cases hnzero : n = 0
  · subst n
    by_cases hmzero : m = 0
    · subst m
      rfl
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
      have hzero :
          rsTruncIntegral (fun x => |g x|) F (-((0 : ℕ) : ℝ)) ((0 : ℕ) : ℝ) =
            0 := by
        simpa using thm_7_9_rsTruncIntegral_zero_zero (fun x => |g x|) F
      rw [hzero]
      rw [thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc F h hmpos]
      exact integral_nonneg fun x => abs_nonneg (g x)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
    have hmpos : 0 < m := lt_of_lt_of_le hnpos hnm
    rw [thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc F h hnpos]
    rw [thm_7_9_rsTruncIntegral_abs_eq_integral_Ioc F h hmpos]
    have hsubset : Ioc (-(n : ℝ)) (n : ℝ) ⊆ Ioc (-(m : ℝ)) (m : ℝ) :=
      thm_7_9_nat_Ioc_subset hnm
    exact setIntegral_mono_set (hAbs.integrableOn)
      (Filter.Eventually.of_forall fun x => abs_nonneg (g x))
      (Filter.Eventually.of_forall fun x hx => hsubset hx)
