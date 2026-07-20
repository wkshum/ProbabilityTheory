import ToyApollo.Output.def_1_4

open Filter

noncomputable section

/-!
Definition 1.4 bookkeeping support for Theorem 7.9.

The source proof reasons with large finite truncation intervals.  The local
Definition 1.4 interface packages this as a double-limit filter and guards each
finite value by an `RSIntegrable` check.  This file owns only that interface
bookkeeping.
-/

theorem thm_7_9_eventually_strict_improperRSFilter :
    ∀ᶠ p : ℝ × ℝ in improperRSFilter, p.1 < p.2 := by
  unfold improperRSFilter
  rw [Filter.eventually_inf_principal, Filter.eventually_prod_iff]
  refine ⟨fun x : ℝ => x ≤ 0, ?_, fun y : ℝ => 0 < y, ?_, ?_⟩
  · exact Filter.eventually_atBot.2 ⟨0, by intro x hx; exact hx⟩
  · exact Filter.eventually_atTop.2 ⟨1, by intro y hy; linarith⟩
  · intro x hx y hy _hle
    linarith

theorem thm_7_9_eventually_rsIntegrable_of_forall {g α : ℝ → ℝ}
    (hRS : ∀ ⦃a b : ℝ⦄, a < b → RSIntegrable g α a b) :
    ∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable g α p.1 p.2 := by
  exact thm_7_9_eventually_strict_improperRSFilter.mono fun p hp => hRS hp

theorem thm_7_9_eventually_rsTruncIntegral_eq_rsIntegral {g α : ℝ → ℝ}
    (hRS : ∀ ⦃a b : ℝ⦄, a < b → RSIntegrable g α a b) :
    ∀ᶠ p : ℝ × ℝ in improperRSFilter,
      ∃ h : RSIntegrable g α p.1 p.2,
        rsTruncIntegral g α p.1 p.2 = rsIntegral g α p.1 p.2 h := by
  filter_upwards [thm_7_9_eventually_strict_improperRSFilter] with p hp
  let h : RSIntegrable g α p.1 p.2 := hRS hp
  exact ⟨h, by simp [rsTruncIntegral, h]⟩

theorem thm_7_9_improperRSConvergesTo_intro {g α : ℝ → ℝ} {I : ℝ}
    (hFinite :
      ∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable g α p.1 p.2)
    (hTendsto :
      Tendsto
        (fun p : ℝ × ℝ => rsTruncIntegral g α p.1 p.2)
        improperRSFilter
        (nhds I)) :
    ImproperRSConvergesTo g α I := by
  exact ⟨hFinite, hTendsto⟩

theorem thm_7_9_improperRSIntegrable_of_convergesTo {g α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo g α I) :
    ImproperRSIntegrable g α := by
  exact ⟨I, h⟩
