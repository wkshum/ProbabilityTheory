import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Filter MeasureTheory
open scoped Topology

/-

  # Theorem 7.7 DCT for complex function in limit form

-/

/-
\begin{thmbox}{7.7 (Complex DCT, Limit Version)}
Let $X_h$ be complex-valued measurable functions defined on a measure space $(\Omega,\mathcal{F},\mu)$, indexed by a real variable $h$ in some interval. Suppose $\lim_{h\to h_0} X_h(\omega)$ converges almost everywhere for some $h_0$, and assume that there exists a real-valued integrable function $Y$ such that $|X_h|\le Y$ for all $h$ in the interval. Then the limit function
\[
X(\omega)\triangleq \lim_{h\to h_0} X_h(\omega)
\]
is integrable and
\[
\lim_{h\to h_0} \int X_h\, d\mu = \int \lim_{h\to h_0} X_h\, d\mu.
\]
\end{thmbox}
-/

/-- Filter-form complex dominated convergence. This is the analytic engine used by
the local interval statement below; the public theorem keeps the source's local
parameter domain instead of requiring global hypotheses on all real parameters. -/
theorem thm_7_DCT_filter {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xh : ι → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (l : Filter ι) [l.IsCountablyGenerated]
    (hXm : ∀ᶠ h in l, AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ᶠ h in l, ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) l (nhds (X ω))) :
    Tendsto (fun h => ∫ ω, Xh h ω ∂μ) l
      (nhds (∫ ω, X ω ∂μ)) :=
  tendsto_integral_filter_of_dominated_convergence
    Y hXm h_bound hYint h_lim

/-- Sequential complex DCT bridge. The source text says the limit-parameter
version is reduced to the sequential DCT by constructing a sequence converging
to the limit. This lemma records the sequential landing place explicitly. -/
theorem thm_7_7_sequential_complex_DCT {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hXm : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n : ℕ => ∫ ω, Xn n ω ∂μ) atTop
        (nhds (∫ ω, X ω ∂μ)) := by
  have hX_meas : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim
  have hX_finite : HasFiniteIntegral X μ :=
    hasFiniteIntegral_of_dominated_convergence hYint.hasFiniteIntegral h_bound h_lim
  have hXint : Integrable X μ := ⟨hX_meas, hX_finite⟩
  have h_tendsto :
      Tendsto (fun n : ℕ => ∫ ω, Xn n ω ∂μ) atTop
        (nhds (∫ ω, X ω ∂μ)) :=
    thm_7_DCT_filter μ Xn X Y atTop
      (Eventually.of_forall hXm) hYint
      (Eventually.of_forall h_bound) h_lim
  exact ⟨hXint, h_tendsto⟩

/-- Theorem 7.7, stated on a local real parameter interval. The assumptions are
only required for `h ∈ I`, and the limit is taken along `nhdsWithin h0 I`. -/
theorem thm_7_7_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : Set ℝ) (h0 : ℝ)
    (Xh : ℝ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hh0 : h0 ∈ I)
    (hXm : ∀ h : ℝ, h ∈ I → AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ h : ℝ, h ∈ I → ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h : ℝ => Xh h ω) (nhdsWithin h0 I) (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun h : ℝ => ∫ ω, Xh h ω ∂μ) (nhdsWithin h0 I)
      (nhds (∫ ω, X ω ∂μ)) := by
  have hconst : Tendsto (fun _ : ℕ => h0) atTop (nhdsWithin h0 I) :=
    tendsto_const_nhdsWithin hh0
  have hseq_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun _ : ℕ => Xh h0 ω) atTop (nhds (X ω)) := by
    filter_upwards [h_lim] with ω hω
    exact hω.comp hconst
  have hseq :
      Integrable X μ ∧
        Tendsto (fun _ : ℕ => ∫ ω, Xh h0 ω ∂μ) atTop
          (nhds (∫ ω, X ω ∂μ)) :=
    thm_7_7_sequential_complex_DCT μ (fun _ : ℕ => Xh h0) X Y
      (fun _ => hXm h0 hh0) hYint (fun _ => h_bound h0 hh0) hseq_lim
  have hXm_eventually :
      ∀ᶠ h in nhdsWithin h0 I, AEStronglyMeasurable (Xh h) μ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hXm h hh
  have hbound_eventually :
      ∀ᶠ h in nhdsWithin h0 I, ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact h_bound h hh
  have h_tendsto :
      Tendsto (fun h : ℝ => ∫ ω, Xh h ω ∂μ) (nhdsWithin h0 I)
        (nhds (∫ ω, X ω ∂μ)) :=
    thm_7_DCT_filter μ Xh X Y (nhdsWithin h0 I)
      hXm_eventually hYint hbound_eventually h_lim
  exact ⟨hseq.1, h_tendsto⟩

/-- Compatibility helper for the existing global real-parameter specialization. -/
theorem thm_7_7 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xh : ℝ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (h0 : ℝ)
    (hXm : ∀ h : ℝ, AEStronglyMeasurable (Xh h) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ h : ℝ, ∀ᵐ ω ∂μ, ‖Xh h ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) (nhds h0) (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun h => ∫ ω, Xh h ω ∂μ) (nhds h0) (nhds (∫ ω, X ω ∂μ)) := by
  have hlim_univ :
      ∀ᵐ ω ∂μ, Tendsto (fun h => Xh h ω) (nhdsWithin h0 Set.univ) (nhds (X ω)) := by
    simpa [nhdsWithin_univ] using h_lim
  simpa [nhdsWithin_univ] using
    (thm_7_7_interval μ Set.univ h0 Xh X Y (Set.mem_univ h0)
      (fun h _ => hXm h) hYint (fun h _ => h_bound h) hlim_univ)
