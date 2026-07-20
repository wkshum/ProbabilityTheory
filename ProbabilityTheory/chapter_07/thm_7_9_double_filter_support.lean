import ToyApollo.Output.thm_7_9_filter_support

open Filter

noncomputable section

/-!
Double-filter transfer support for Theorem 7.9.

The source proof works with symmetric truncations `[-n,n]`, while the local
Definition 1.4 interface uses the double filter `a -> -infty`, `b -> infty`.
This file owns the abstract tail-control step that converts a reviewed
symmetric truncation limit into a double-filter limit once arbitrary large
interval truncations are controlled by sufficiently far symmetric truncations.
-/

theorem thm_7_9_tendsto_double_filter_of_symmetric_tail_control
    {u : ℝ × ℝ → ℝ} {v : ℕ → ℝ} {I : ℝ}
    (hv : Tendsto v atTop (nhds I))
    (hctrl : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∀ᶠ p : ℝ × ℝ in improperRSFilter,
        ∃ n : ℕ, N ≤ n ∧ dist (u p) (v n) < ε) :
    Tendsto u improperRSFilter (nhds I) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hv_event : ∀ᶠ n : ℕ in atTop, dist (v n) I < ε / 2 :=
    (Metric.tendsto_nhds.mp hv) (ε / 2) hε2
  rcases Filter.eventually_atTop.mp hv_event with ⟨N, hN⟩
  have hctrl_event := hctrl (ε / 2) hε2 N
  filter_upwards [hctrl_event] with p hp
  rcases hp with ⟨n, hn, hpn⟩
  have hnI : dist (v n) I < ε / 2 := hN n hn
  calc
    dist (u p) I ≤ dist (u p) (v n) + dist (v n) I := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hpn hnI
    _ = ε := by ring

theorem thm_7_9_improperRSConvergesTo_of_symmetric_tail_control
    {g α : ℝ → ℝ} {I : ℝ}
    (hFinite : ∀ᶠ p : ℝ × ℝ in improperRSFilter, RSIntegrable g α p.1 p.2)
    (hSymm :
      Tendsto (fun n : ℕ => rsTruncIntegral g α (-(n : ℝ)) (n : ℝ))
        atTop (nhds I))
    (hctrl : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∀ᶠ p : ℝ × ℝ in improperRSFilter,
        ∃ n : ℕ, N ≤ n ∧
          dist (rsTruncIntegral g α p.1 p.2)
            (rsTruncIntegral g α (-(n : ℝ)) (n : ℝ)) < ε) :
    ImproperRSConvergesTo g α I := by
  refine thm_7_9_improperRSConvergesTo_intro hFinite ?_
  exact thm_7_9_tendsto_double_filter_of_symmetric_tail_control hSymm hctrl
