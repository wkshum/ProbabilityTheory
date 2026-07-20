import ToyApollo.Output.thm_7_9_filter_support

open Filter

noncomputable section

/-!
Value-recovery support for Theorem 7.9.

After another support step proves convergence to a concrete value, the local
Definition 1.4 interface chooses an improper integral value by `Classical.choose`.
This file owns the uniqueness step that recovers the concrete limit value from
`improperRSIntegral_spec`.
-/

theorem thm_7_9_improperRSFilter_neBot : NeBot improperRSFilter := by
  unfold improperRSFilter
  rw [Filter.inf_neBot_iff]
  intro s hs t ht
  rw [Filter.mem_prod_iff] at hs
  rcases hs with ⟨A, hA, B, hB, hsub⟩
  rcases (Filter.eventually_atBot.mp hA) with ⟨a0, hA0⟩
  rcases (Filter.eventually_atTop.mp hB) with ⟨b0, hB0⟩
  let x : ℝ := min a0 b0
  let y : ℝ := max b0 x
  have hxA : x ∈ A := hA0 x (min_le_left a0 b0)
  have hyB : y ∈ B := hB0 y (le_max_left b0 x)
  have hxy : x ≤ y := le_max_right b0 x
  have ht_sub : {p : ℝ × ℝ | p.1 ≤ p.2} ⊆ t := by
    simpa using ht
  refine ⟨(x, y), ?_⟩
  constructor
  · exact hsub ⟨hxA, hyB⟩
  · exact ht_sub hxy

theorem thm_7_9_improperRSIntegral_eq_of_convergesTo {g α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo g α I) :
    improperRSIntegral g α (thm_7_9_improperRSIntegrable_of_convergesTo h) = I := by
  haveI : NeBot improperRSFilter := thm_7_9_improperRSFilter_neBot
  exact tendsto_nhds_unique
    (improperRSIntegral_spec
      (thm_7_9_improperRSIntegrable_of_convergesTo h)).2
    h.2

/-- Package a concrete improper RS convergence value into the existential
shape used by Theorem 7.9's value conclusion. -/
theorem thm_7_9_value_packaging_with_improperRSIntegral_spec {g α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo g α I) :
    ∃ hImp : ImproperRSIntegrable g α, I = improperRSIntegral g α hImp := by
  refine ⟨thm_7_9_improperRSIntegrable_of_convergesTo h, ?_⟩
  exact (thm_7_9_improperRSIntegral_eq_of_convergesTo h).symm
