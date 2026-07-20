import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic


/-

  # Theorem 7.6  DCT for complex functions in sequential form

-/

/-
\begin{thmbox}{7.6 (Complex DCT, Sequential Version)}
Let $X_n$ be complex-valued random variables, for $n=1,2,3,\dots$, defined on a measure space $(\Omega,\mathcal{F},\mu)$. Suppose $(X_n)_{n\ge 1}$ converges to $X$ almost everywhere for all $n$, and there exists an integrable function $Y$ such that $|X_n|\le Y$ almost everywhere for all $n$. Then $X\in L^1(\mu)$ and
\[
\lim_{n\to\infty} \int X_n\, d\mu = \int \lim_{n\to\infty} X_n\, d\mu.
\]
\end{thmbox}
-/

open Filter MeasureTheory

/--
Exported statement for the sequential complex-valued dominated convergence
theorem.
-/
theorem thm_7_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℂ) (X : Ω → ℂ) (Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
    Integrable X μ ∧
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by
  have hX_meas : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim
  have h_bound_all : ∀ᵐ ω ∂μ, ∀ n, ‖Xn n ω‖ ≤ Y ω :=
    eventually_countable_forall.2 h_bound
  have hX_bound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ Y ω := by
    filter_upwards [h_bound_all, h_lim] with ω hω_bound hω_lim
    have hnorm_tendsto : Tendsto (fun n => ‖Xn n ω‖) atTop (nhds ‖X ω‖) :=
      (continuous_norm.tendsto (X ω)).comp hω_lim
    have hmem : ∀ᶠ n in atTop, ‖Xn n ω‖ ∈ Set.Iic (Y ω) :=
      Filter.Eventually.of_forall fun n => hω_bound n
    have hlimit_mem : ‖X ω‖ ∈ Set.Iic (Y ω) :=
      IsClosed.mem_of_tendsto isClosed_Iic hnorm_tendsto hmem
    simpa [Set.mem_Iic] using hlimit_mem
  have hX_int : Integrable X μ :=
    Integrable.mono' hYint hX_meas hX_bound
  have hXn_int : ∀ n, Integrable (Xn n) μ := fun n =>
    Integrable.mono' hYint (hXm n) (h_bound n)
  have h_re_meas : ∀ n, AEStronglyMeasurable (fun ω => (Xn n ω).re) μ := by
    intro n
    simpa [Function.comp_def] using
      (Complex.continuous_re.comp_aestronglyMeasurable (hXm n))

  have h_im_meas : ∀ n, AEStronglyMeasurable (fun ω => (Xn n ω).im) μ := by
    intro n
    simpa [Function.comp_def] using
      (Complex.continuous_im.comp_aestronglyMeasurable (hXm n))

  have h_re_bound : ∀ n, ∀ᵐ ω ∂μ, ‖(Xn n ω).re‖ ≤ Y ω := by
    intro n
    filter_upwards [h_bound n] with ω hω
    exact (RCLike.norm_re_le_norm (Xn n ω)).trans hω
  have h_im_bound : ∀ n, ∀ᵐ ω ∂μ, ‖(Xn n ω).im‖ ≤ Y ω := by
    intro n
    filter_upwards [h_bound n] with ω hω
    exact (RCLike.norm_im_le_norm (Xn n ω)).trans hω
  have h_re_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n => (Xn n ω).re) atTop (nhds ((X ω).re)) := by
    filter_upwards [h_lim] with ω hω
    exact (Complex.continuous_re.tendsto (X ω)).comp hω
  have h_im_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n => (Xn n ω).im) atTop (nhds ((X ω).im)) := by
    filter_upwards [h_lim] with ω hω
    exact (Complex.continuous_im.tendsto (X ω)).comp hω
  have h_re_tendsto :
      Tendsto (fun n => ∫ ω, (Xn n ω).re ∂μ) atTop
        (nhds (∫ ω, (X ω).re ∂μ)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      Y h_re_meas hYint h_re_bound h_re_lim
  have h_im_tendsto :
      Tendsto (fun n => ∫ ω, (Xn n ω).im ∂μ) atTop
        (nhds (∫ ω, (X ω).im ∂μ)) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      Y h_im_meas hYint h_im_bound h_im_lim
  have h_pair_tendsto :
      Tendsto (fun n => Complex.equivRealProdCLM (∫ ω, Xn n ω ∂μ)) atTop
        (nhds (Complex.equivRealProdCLM (∫ ω, X ω ∂μ))) := by
    rw [Prod.tendsto_iff]
    constructor
    · convert h_re_tendsto using 1
      · ext n
        simpa [Complex.equivRealProdCLM_apply] using (integral_re (hXn_int n)).symm
      · simpa [Complex.equivRealProdCLM_apply] using congrArg nhds (integral_re hX_int).symm
    · convert h_im_tendsto using 1
      · ext n
        simpa [Complex.equivRealProdCLM_apply] using (integral_im (hXn_int n)).symm
      · simpa [Complex.equivRealProdCLM_apply] using congrArg nhds (integral_im hX_int).symm

  have h_tendsto :
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by
    have h_back₀ :=
      (Complex.equivRealProdCLM.symm.continuous.tendsto
        (Complex.equivRealProdCLM (∫ ω, X ω ∂μ))).comp h_pair_tendsto

    have h_back :
        Tendsto
          (fun n =>
            Complex.equivRealProdCLM.symm
              ((∫ ω, Xn n ω ∂μ).re, (∫ ω, Xn n ω ∂μ).im))
          atTop
          (nhds
            (Complex.equivRealProdCLM.symm
              ((∫ ω, X ω ∂μ).re, (∫ ω, X ω ∂μ).im))) := by
      simpa [Function.comp_def, Complex.equivRealProdCLM_apply] using h_back₀

    have hfun :
        (fun n =>
          Complex.equivRealProdCLM.symm
            ((∫ ω, Xn n ω ∂μ).re, (∫ ω, Xn n ω ∂μ).im))
          =
        (fun n => ∫ ω, Xn n ω ∂μ) := by
      funext n
      rw [← Complex.equivRealProdCLM_apply (∫ ω, Xn n ω ∂μ)]
      simp
      rfl

    have hlim :
        Complex.equivRealProdCLM.symm
          ((∫ ω, X ω ∂μ).re, (∫ ω, X ω ∂μ).im)
          =
        ∫ ω, X ω ∂μ := by
      rw [← Complex.equivRealProdCLM_apply (∫ ω, X ω ∂μ)]
      simp
      rfl

    rw [hfun, hlim] at h_back
    exact h_back

  exact ⟨hX_int, h_tendsto⟩
