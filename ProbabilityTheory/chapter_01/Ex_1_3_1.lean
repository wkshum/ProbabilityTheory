import ProbabilityTheory.chapter_01.Thm_1_2_4


/-- Step integrator with one jump at `c`.

It is equal to `u₁` to the left of `c`, and equal to `u₂` at and to the
right of `c`.
-/
noncomputable def jumpStep (c u₁ u₂ : ℝ) : ℝ → ℝ :=
  fun x => if x < c then u₁ else u₂



theorem taggedCommonLimit_jumpStep_of_continuousAt
    {f : ℝ → ℝ} {c u₁ u₂ a b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hu : u₁ ≤ u₂)
    (hfcont : ContinuousAt f c) :
    TaggedCommonLimit a b f (jumpStep c u₁ u₂)
      (f c * (u₂ - u₁)) := by sorry


/--
The Riemann--Stieltjes integral with respect to a one-jump step integrator.

If

* `a < c < b`,
* `α x = u₁` for `x < c`,
* `α x = u₂` for `x ≥ c`,
* `u₁ ≤ u₂`,
* `f` is continuous at `c`,

then

`∫_[a,b] f dα = f(c) * (u₂ - u₁)`.

The proof uses tagged-sum uniqueness.  The hard analytic content is contained in
`taggedCommonLimit_jumpStep_of_continuousAt`, which proves directly that every
tagged Riemann--Stieltjes sum converges to `f c * (u₂ - u₁)`.
-/
theorem rsIntegral_jumpStep_eq {f : ℝ → ℝ} {c u₁ u₂ a b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hu : u₁ ≤ u₂)
    (hfcont : ContinuousAt f c)
    (h : RSIntegrable f (jumpStep c u₁ u₂) a b) :
    rsIntegral f (jumpStep c u₁ u₂) a b h =
      f c * (u₂ - u₁) := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec h)
    (taggedCommonLimit_jumpStep_of_continuousAt
      (f := f) (c := c) (u₁ := u₁) (u₂ := u₂)
      hac hcb hu hfcont)
