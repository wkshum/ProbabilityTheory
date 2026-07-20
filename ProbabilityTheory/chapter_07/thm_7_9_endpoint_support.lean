import ToyApollo.Output.thm_7_8

open MeasureTheory Set

noncomputable section

/-!
Endpoint support for the Theorem 7.9 finite-interval bridge.

Mathlib's Stieltjes measure satisfies `F.measure (Ioc a b) = F b - F a`.
The project Darboux Riemann-Stieltjes integral over `[a,b]` uses the same
increments and therefore matches the half-open interval route, while the
Lebesgue-Stieltjes integral over `Icc a b` also contains the left endpoint atom.
This file records that correction explicitly.
-/

/-- Decompose the closed-interval Lebesgue-Stieltjes integral into the left
endpoint atom plus the half-open interval integral. -/
theorem thm_7_9_integral_Icc_eq_singleton_add_Ioc
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) F.measure) :
    ∫ x in Icc a b, g x ∂F.measure =
      (F.measure {a}).toReal * g a + ∫ x in Ioc a b, g x ∂F.measure := by
  have hUnion : ({a} : Set ℝ) ∪ Ioc a b = Icc a b := by
    rw [← Icc_union_Ioc_eq_Icc (a := a) (b := a) (c := b) le_rfl hab]
    simp
  rw [← hUnion]
  have hDisj : Disjoint ({a} : Set ℝ) (Ioc a b) := by
    rw [disjoint_left]
    intro x hxA hxIoc
    have hxa : x = a := by simpa using hxA
    exact (lt_irrefl a) (by simpa [hxa] using hxIoc.1)
  rw [setIntegral_union hDisj measurableSet_Ioc]
  · rw [integral_singleton]
    simp [Measure.real_def, smul_eq_mul]
  · exact hg.mono_set (by
      intro x hx
      simp only [mem_singleton_iff] at hx
      rw [hx]
      exact ⟨le_rfl, hab⟩)
  · exact hg.mono_set Ioc_subset_Icc_self

