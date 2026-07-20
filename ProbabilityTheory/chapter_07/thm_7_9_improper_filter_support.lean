import ToyApollo.Output.thm_7_9_filter_support
import ToyApollo.Output.thm_7_9_double_filter_support
import ToyApollo.Output.thm_7_9_value_support

open Filter

noncomputable section

/-!
Assembled Definition 1.4 bookkeeping support for Theorem 7.9.

This file packages the reviewed interface lemmas connecting the source
symmetric truncation route to the local double-filter definition of improper
Riemann-Stieltjes integration.  It remains at the Definition 1.4 interface
level: analytic tail-control and RS/LS bridge facts must still be supplied by
the other Theorem 7.9 support obligations.
-/

theorem thm_7_9_improper_filter_bookkeeping
    {g α : ℝ → ℝ} {I : ℝ}
    (hRS : ∀ ⦃a b : ℝ⦄, a < b → RSIntegrable g α a b)
    (hSymm :
      Tendsto (fun n : ℕ => rsTruncIntegral g α (-(n : ℝ)) (n : ℝ))
        atTop (nhds I))
    (hctrl : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∀ᶠ p : ℝ × ℝ in improperRSFilter,
        ∃ n : ℕ, N ≤ n ∧
          dist (rsTruncIntegral g α p.1 p.2)
            (rsTruncIntegral g α (-(n : ℝ)) (n : ℝ)) < ε) :
    ImproperRSConvergesTo g α I ∧
      ∃ hImp : ImproperRSIntegrable g α,
        improperRSIntegral g α hImp = I := by
  have hFinite := thm_7_9_eventually_rsIntegrable_of_forall hRS
  have hConv :=
    thm_7_9_improperRSConvergesTo_of_symmetric_tail_control
      hFinite hSymm hctrl
  let hImp : ImproperRSIntegrable g α :=
    thm_7_9_improperRSIntegrable_of_convergesTo hConv
  exact ⟨hConv, ⟨hImp, thm_7_9_improperRSIntegral_eq_of_convergesTo hConv⟩⟩
