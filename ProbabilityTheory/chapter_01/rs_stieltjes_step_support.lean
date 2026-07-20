import ProbabilityTheory.chapter_01.rs_stieltjes_darboux_support
import ProbabilityTheory.chapter_01.thm_1_1_common_limit
import ProbabilityTheory.chapter_01.thm_1_3
import ProbabilityTheory.chapter_01.thm_1_4
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory intervalIntegral Set
open scoped Pointwise

noncomputable section

/-!
Single-jump and floor-step RS calculation support for Chapter 1 examples and problems.
This is a mechanical split from the old mixed `rs_stieltjes_bridge` body.
-/
noncomputable def rsIntegralWitness_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegralWitness (fun x => f x + g x) alpha a b where
  value := rsIntegral f alpha a b hf + rsIntegral g alpha a b hg
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_integrand_add
      (rsIntegral_source_spec hf) (rsIntegral_source_spec hg)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_integrand_add
      (rsIntegral_spec hf) (rsIntegral_spec hg)

noncomputable def rsIntegrable_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegrable (fun x => f x + g x) alpha a b :=
  ⟨rsIntegralWitness_add hf hg⟩

theorem rsIntegral_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    rsIntegral (fun x => f x + g x) alpha a b (rsIntegrable_add hf hg) =
      rsIntegral f alpha a b hf + rsIntegral g alpha a b hg := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_add hf hg))
    (DarbouxRS.taggedCommonLimit_integrand_add (rsIntegral_spec hf) (rsIntegral_spec hg))

noncomputable def rsIntegralWitness_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegralWitness (fun x => c * f x) alpha a b where
  value := c * rsIntegral f alpha a b hf
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_const_mul
      (c := c) (rsIntegral_source_spec hf)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_const_mul
      (c := c) (rsIntegral_spec hf)

noncomputable def rsIntegrable_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegrable (fun x => c * f x) alpha a b :=
  ⟨rsIntegralWitness_const_mul (c := c) hf⟩

theorem rsIntegral_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    rsIntegral (fun x => c * f x) alpha a b (rsIntegrable_const_mul (c := c) hf) =
      c * rsIntegral f alpha a b hf := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_const_mul (c := c) hf))
    (DarbouxRS.taggedCommonLimit_const_mul (c := c) (rsIntegral_spec hf))

theorem rsIntegral_mono {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    rsIntegral f alpha a b hf ≤ rsIntegral g alpha a b hg :=
  DarbouxRS.taggedCommonLimit_mono (rsIntegral_spec hf) (rsIntegral_spec hg) hfg

noncomputable def rsIntegralWitness_congr_integrator_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b)
    (hβmono : MonotoneOn β (Icc a b))
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    RSIntegralWitness f β a b where
  value := rsIntegral f α a b h
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_congr_integrator_Icc
      (rsIntegral_source_spec h) hβmono hEq
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_congr_integrator_Icc
      (rsIntegral_spec h) hβmono hEq

noncomputable def rsIntegrable_congr_integrator_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b)
    (hβmono : MonotoneOn β (Icc a b))
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    RSIntegrable f β a b :=
  ⟨rsIntegralWitness_congr_integrator_Icc h hβmono hEq⟩

theorem rsIntegral_congr_integrator_Icc
    {f α β : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b)
    (hβmono : MonotoneOn β (Icc a b))
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    rsIntegral f β a b (rsIntegrable_congr_integrator_Icc h hβmono hEq) =
      rsIntegral f α a b h := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_congr_integrator_Icc h hβmono hEq))
    (DarbouxRS.taggedCommonLimit_congr_integrator_Icc (rsIntegral_spec h) hβmono hEq)

noncomputable def rsIntegralWitness_congr_integrand_Icc
    {f g α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    RSIntegralWitness g α a b where
  value := rsIntegral f α a b h
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_congr_integrand_Icc
      (rsIntegral_source_spec h) hEq
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_congr_integrand_Icc
      (rsIntegral_spec h) hEq

noncomputable def rsIntegrable_congr_integrand_Icc
    {f g α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    RSIntegrable g α a b :=
  ⟨rsIntegralWitness_congr_integrand_Icc h hEq⟩

theorem rsIntegral_congr_integrand_Icc
    {f g α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    rsIntegral g α a b (rsIntegrable_congr_integrand_Icc h hEq) =
      rsIntegral f α a b h := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_congr_integrand_Icc h hEq))
    (DarbouxRS.taggedCommonLimit_congr_integrand_Icc (rsIntegral_spec h) hEq)

def floorStep0_10Integrator (x : ℝ) : ℝ :=
  ((((((((((if x < (1 : ℝ) then (0 : ℝ) else 1) +
    (if x < (2 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (3 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (4 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (5 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (6 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (7 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (8 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (9 : ℝ) then (0 : ℝ) else 1)) +
    (if x < (10 : ℝ) then (0 : ℝ) else 1))

lemma floorStep0_10Integrator_eq_floor {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 10) :
    floorStep0_10Integrator x = (⌊x⌋ : ℝ) := by
  rcases hx with ⟨h0, h10⟩
  by_cases h1 : x < (1 : ℝ)
  · have h2 : x < (2 : ℝ) := by linarith
    have h3 : x < (3 : ℝ) := by linarith
    have h4 : x < (4 : ℝ) := by linarith
    have h5 : x < (5 : ℝ) := by linarith
    have h6 : x < (6 : ℝ) := by linarith
    have h7 : x < (7 : ℝ) := by linarith
    have h8 : x < (8 : ℝ) := by linarith
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (0 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h2 : x < (2 : ℝ)
  · have hge1 : (1 : ℝ) ≤ x := le_of_not_gt h1
    have h3 : x < (3 : ℝ) := by linarith
    have h4 : x < (4 : ℝ) := by linarith
    have h5 : x < (5 : ℝ) := by linarith
    have h6 : x < (6 : ℝ) := by linarith
    have h7 : x < (7 : ℝ) := by linarith
    have h8 : x < (8 : ℝ) := by linarith
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (1 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h3 : x < (3 : ℝ)
  · have hge2 : (2 : ℝ) ≤ x := le_of_not_gt h2
    have h4 : x < (4 : ℝ) := by linarith
    have h5 : x < (5 : ℝ) := by linarith
    have h6 : x < (6 : ℝ) := by linarith
    have h7 : x < (7 : ℝ) := by linarith
    have h8 : x < (8 : ℝ) := by linarith
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (2 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h4 : x < (4 : ℝ)
  · have hge3 : (3 : ℝ) ≤ x := le_of_not_gt h3
    have h5 : x < (5 : ℝ) := by linarith
    have h6 : x < (6 : ℝ) := by linarith
    have h7 : x < (7 : ℝ) := by linarith
    have h8 : x < (8 : ℝ) := by linarith
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (3 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h5 : x < (5 : ℝ)
  · have hge4 : (4 : ℝ) ≤ x := le_of_not_gt h4
    have h6 : x < (6 : ℝ) := by linarith
    have h7 : x < (7 : ℝ) := by linarith
    have h8 : x < (8 : ℝ) := by linarith
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (4 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h6 : x < (6 : ℝ)
  · have hge5 : (5 : ℝ) ≤ x := le_of_not_gt h5
    have h7 : x < (7 : ℝ) := by linarith
    have h8 : x < (8 : ℝ) := by linarith
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (5 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h7 : x < (7 : ℝ)
  · have hge6 : (6 : ℝ) ≤ x := le_of_not_gt h6
    have h8 : x < (8 : ℝ) := by linarith
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (6 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h8 : x < (8 : ℝ)
  · have hge7 : (7 : ℝ) ≤ x := le_of_not_gt h7
    have h9 : x < (9 : ℝ) := by linarith
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (7 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h9 : x < (9 : ℝ)
  · have hge8 : (8 : ℝ) ≤ x := le_of_not_gt h8
    have h10lt : x < (10 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (8 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  by_cases h10lt : x < (10 : ℝ)
  · have hge9 : (9 : ℝ) ≤ x := le_of_not_gt h9
    have hfloor : ⌊x⌋ = (9 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]
  · have hge10 : (10 : ℝ) ≤ x := le_of_not_gt h10lt
    have hfloor : ⌊x⌋ = (10 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_10Integrator, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10lt, hfloor]

/-- Textbook finite-discontinuity criterion for the partition-based Riemann--Stieltjes integral.

This is the classical bridge needed after `def_1_2` was restored to the partition-limit
definition. It packages the standard theorem cited by Chapter 1: a bounded function with finitely
many discontinuities is RS-integrable when the integrator is continuous at each discontinuity. -/
theorem rsIntegrable_of_bounded_finite_discontinuities
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : ({x | x ∈ Icc a b ∧ ¬ ContinuousAt f x} : Set ℝ).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄,
      x ∈ ({x | x ∈ Icc a b ∧ ¬ ContinuousAt f x} : Set ℝ) → ContinuousAt α x) :
    RSIntegrable f α a b := by
  have hDiscFinite' : (discontinuitySetOn f a b).Finite := by
    apply hDiscFinite.subset
    intro x hx
    exact ⟨hx.1, fun hAt => hx.2 hAt.continuousWithinAt⟩
  have hαCont' : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x := by
    intro x hx
    exact hαCont ⟨hx.1, fun hAt => hx.2 hAt.continuousWithinAt⟩
  exact Thm11SourceRoute.strict_thm_1_1
    hab hα_mono hAbove hBelow hDiscFinite' hαCont'

/-- Classical single-jump Riemann--Stieltjes evaluation.

This is the source partition/tagged-sum proof used in Example 1.3.1: all
nonzero Stieltjes increments are carried by partition cells crossing the jump
point `c`; if the mesh is small, every such cell lies near `c`, and continuity
of `f` at `c` identifies the common limit. The boundedness hypotheses make
explicit the standing Chapter 1 context for Definition 1.2. -/
theorem rsIntegral_singleJumpStep_exists
    {f : ℝ → ℝ} {a b c u₁ u₂ : ℝ}
    (_hab : a ≤ b)
    (hac : a < c)
    (hcb : c ≤ b)
    (hu : u₁ < u₂)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcont : ContinuousAt f c) :
    ∃ hRS : RSIntegrable f (fun x => if x < c then u₁ else u₂) a b,
      rsIntegral f (fun x => if x < c then u₁ else u₂) a b hRS = f c * (u₂ - u₁) := by
  let hW : RSIntegralWitness f (fun x => if x < c then u₁ else u₂) a b := {
    value := f c * (u₂ - u₁)
    source_limit := DarbouxRS.singleJump_upperLowerCommonLimit
      (hac := hac) (hcb := hcb) (hu := hu) hAbove hBelow hcont
    tagged_limit := DarbouxRS.singleJump_taggedCommonLimit
      (hac := hac) (hcb := hcb) (hu := hu) hAbove hBelow hcont
  }
  let hRS : RSIntegrable f (fun x => if x < c then u₁ else u₂) a b :=
    ⟨hW⟩
  refine ⟨hRS, ?_⟩
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec hRS)
    (DarbouxRS.singleJump_taggedCommonLimit
      (hac := hac) (hcb := hcb) (hu := hu) hAbove hBelow hcont)

/-- The single-jump summand used in Problem 1.8(a). -/
theorem rsIntegral_square_unitJump_0_10
    {c : ℝ} (hc0 : 0 < c) (hc10 : c ≤ 10) :
    ∃ h : RSIntegrable (fun x : ℝ => x ^ 2)
        (fun x : ℝ => if x < c then (0 : ℝ) else 1) 0 10,
      rsIntegral (fun x : ℝ => x ^ 2)
          (fun x : ℝ => if x < c then (0 : ℝ) else 1) 0 10 h = c ^ 2 := by
  have hAbove : BddAbove ((fun x : ℝ => x ^ 2) '' Icc (0 : ℝ) 10) := by
    refine ⟨100, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    nlinarith [sq_nonneg x, hx.1, hx.2]
  have hBelow : BddBelow ((fun x : ℝ => x ^ 2) '' Icc (0 : ℝ) 10) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, _hx, rfl⟩
    exact sq_nonneg x
  have hcont : ContinuousAt (fun x : ℝ => x ^ 2) c :=
    (continuousAt_id.pow 2)
  obtain ⟨h, hv⟩ := rsIntegral_singleJumpStep_exists
    (f := fun x : ℝ => x ^ 2) (a := 0) (b := 10) (c := c)
    (u₁ := 0) (u₂ := 1) (by norm_num) hc0 hc10 (by norm_num)
    hAbove hBelow hcont
  refine ⟨h, ?_⟩
  simpa using hv

/-- Standard evaluated value for Problem 1.8(a), proved by decomposing `floor`
on `[0,10]` into its ten unit jumps and applying Theorem 1.3 additivity. -/
theorem rsIntegral_floor_square_0_10 :
    ∃ h : RSIntegrable (fun x : ℝ => x ^ 2) (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10,
      rsIntegral (fun x : ℝ => x ^ 2) (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10 h = 385 := by
  let f : ℝ → ℝ := fun x => x ^ 2
  let α1 : ℝ → ℝ := fun x => if x < (1 : ℝ) then (0 : ℝ) else 1
  let α2 : ℝ → ℝ := fun x => if x < (2 : ℝ) then (0 : ℝ) else 1
  let α3 : ℝ → ℝ := fun x => if x < (3 : ℝ) then (0 : ℝ) else 1
  let α4 : ℝ → ℝ := fun x => if x < (4 : ℝ) then (0 : ℝ) else 1
  let α5 : ℝ → ℝ := fun x => if x < (5 : ℝ) then (0 : ℝ) else 1
  let α6 : ℝ → ℝ := fun x => if x < (6 : ℝ) then (0 : ℝ) else 1
  let α7 : ℝ → ℝ := fun x => if x < (7 : ℝ) then (0 : ℝ) else 1
  let α8 : ℝ → ℝ := fun x => if x < (8 : ℝ) then (0 : ℝ) else 1
  let α9 : ℝ → ℝ := fun x => if x < (9 : ℝ) then (0 : ℝ) else 1
  let α10 : ℝ → ℝ := fun x => if x < (10 : ℝ) then (0 : ℝ) else 1
  obtain ⟨h1, hv1⟩ := rsIntegral_square_unitJump_0_10 (c := 1) (by norm_num) (by norm_num)
  obtain ⟨h2, hv2⟩ := rsIntegral_square_unitJump_0_10 (c := 2) (by norm_num) (by norm_num)
  obtain ⟨h3, hv3⟩ := rsIntegral_square_unitJump_0_10 (c := 3) (by norm_num) (by norm_num)
  obtain ⟨h4, hv4⟩ := rsIntegral_square_unitJump_0_10 (c := 4) (by norm_num) (by norm_num)
  obtain ⟨h5, hv5⟩ := rsIntegral_square_unitJump_0_10 (c := 5) (by norm_num) (by norm_num)
  obtain ⟨h6, hv6⟩ := rsIntegral_square_unitJump_0_10 (c := 6) (by norm_num) (by norm_num)
  obtain ⟨h7, hv7⟩ := rsIntegral_square_unitJump_0_10 (c := 7) (by norm_num) (by norm_num)
  obtain ⟨h8, hv8⟩ := rsIntegral_square_unitJump_0_10 (c := 8) (by norm_num) (by norm_num)
  obtain ⟨h9, hv9⟩ := rsIntegral_square_unitJump_0_10 (c := 9) (by norm_num) (by norm_num)
  obtain ⟨h10, hv10⟩ := rsIntegral_square_unitJump_0_10 (c := 10) (by norm_num) (by norm_num)
  have hv1' : rsIntegral f α1 0 10 h1 = 1 := by
    dsimp [f, α1]
    rw [hv1]
    norm_num
  have hv2' : rsIntegral f α2 0 10 h2 = 4 := by
    dsimp [f, α2]
    rw [hv2]
    norm_num
  have hv3' : rsIntegral f α3 0 10 h3 = 9 := by
    dsimp [f, α3]
    rw [hv3]
    norm_num
  have hv4' : rsIntegral f α4 0 10 h4 = 16 := by
    dsimp [f, α4]
    rw [hv4]
    norm_num
  have hv5' : rsIntegral f α5 0 10 h5 = 25 := by
    dsimp [f, α5]
    rw [hv5]
    norm_num
  have hv6' : rsIntegral f α6 0 10 h6 = 36 := by
    dsimp [f, α6]
    rw [hv6]
    norm_num
  have hv7' : rsIntegral f α7 0 10 h7 = 49 := by
    dsimp [f, α7]
    rw [hv7]
    norm_num
  have hv8' : rsIntegral f α8 0 10 h8 = 64 := by
    dsimp [f, α8]
    rw [hv8]
    norm_num
  have hv9' : rsIntegral f α9 0 10 h9 = 81 := by
    dsimp [f, α9]
    rw [hv9]
    norm_num
  have hv10' : rsIntegral f α10 0 10 h10 = 100 := by
    dsimp [f, α10]
    rw [hv10]
    norm_num
  let h12 : RSIntegrable f (fun x => α1 x + α2 x) 0 10 :=
    rsIntegrable_integrator_add h1 h2
  have hv12 : rsIntegral f (fun x => α1 x + α2 x) 0 10 h12 = 5 := by
    rw [rsIntegral_integrator_add h1 h2, hv1', hv2']
    norm_num
  let h123 : RSIntegrable f (fun x => (α1 x + α2 x) + α3 x) 0 10 :=
    rsIntegrable_integrator_add h12 h3
  have hv123 : rsIntegral f (fun x => (α1 x + α2 x) + α3 x) 0 10 h123 = 14 := by
    rw [rsIntegral_integrator_add h12 h3, hv12, hv3']
    norm_num
  let h1234 : RSIntegrable f (fun x => ((α1 x + α2 x) + α3 x) + α4 x) 0 10 :=
    rsIntegrable_integrator_add h123 h4
  have hv1234 :
      rsIntegral f (fun x => ((α1 x + α2 x) + α3 x) + α4 x) 0 10 h1234 = 30 := by
    rw [rsIntegral_integrator_add h123 h4, hv123, hv4']
    norm_num
  let h12345 :
      RSIntegrable f (fun x => (((α1 x + α2 x) + α3 x) + α4 x) + α5 x) 0 10 :=
    rsIntegrable_integrator_add h1234 h5
  have hv12345 :
      rsIntegral f (fun x => (((α1 x + α2 x) + α3 x) + α4 x) + α5 x)
          0 10 h12345 = 55 := by
    rw [rsIntegral_integrator_add h1234 h5, hv1234, hv5']
    norm_num
  let h123456 :
      RSIntegrable f (fun x => ((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x)
        0 10 :=
    rsIntegrable_integrator_add h12345 h6
  have hv123456 :
      rsIntegral f (fun x => ((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x)
          0 10 h123456 = 91 := by
    rw [rsIntegral_integrator_add h12345 h6, hv12345, hv6']
    norm_num
  let h1234567 :
      RSIntegrable f
        (fun x => (((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) + α7 x)
        0 10 :=
    rsIntegrable_integrator_add h123456 h7
  have hv1234567 :
      rsIntegral f
          (fun x => (((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) + α7 x)
          0 10 h1234567 = 140 := by
    rw [rsIntegral_integrator_add h123456 h7, hv123456, hv7']
    norm_num
  let h12345678 :
      RSIntegrable f
        (fun x => ((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) + α7 x) +
          α8 x)
        0 10 :=
    rsIntegrable_integrator_add h1234567 h8
  have hv12345678 :
      rsIntegral f
          (fun x => ((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) + α7 x) +
            α8 x)
          0 10 h12345678 = 204 := by
    rw [rsIntegral_integrator_add h1234567 h8, hv1234567, hv8']
    norm_num
  let h123456789 :
      RSIntegrable f
        (fun x => (((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) + α7 x) +
          α8 x) + α9 x)
        0 10 :=
    rsIntegrable_integrator_add h12345678 h9
  have hv123456789 :
      rsIntegral f
          (fun x => (((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) +
            α7 x) + α8 x) + α9 x)
          0 10 h123456789 = 285 := by
    rw [rsIntegral_integrator_add h12345678 h9, hv12345678, hv9']
    norm_num
  let hSteps :
      RSIntegrable f
        (fun x => ((((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) + α7 x) +
          α8 x) + α9 x) + α10 x)
        0 10 :=
    rsIntegrable_integrator_add h123456789 h10
  have hvSteps :
      rsIntegral f
          (fun x => ((((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) +
            α7 x) + α8 x) + α9 x) + α10 x)
          0 10 hSteps = 385 := by
    rw [rsIntegral_integrator_add h123456789 h10, hv123456789, hv10']
    norm_num
  have hFloorMono : MonotoneOn (fun x : ℝ => (⌊x⌋ : ℝ)) (Icc (0 : ℝ) 10) := by
    intro x _hx y _hy hxy
    change ((⌊x⌋ : ℤ) : ℝ) ≤ ((⌊y⌋ : ℤ) : ℝ)
    exact_mod_cast Int.floor_mono hxy
  have hEq :
      ∀ x ∈ Icc (0 : ℝ) 10,
        (⌊x⌋ : ℝ) =
          ((((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) + α7 x) +
            α8 x) + α9 x) + α10 x := by
    intro x hx
    simpa [floorStep0_10Integrator, α1, α2, α3, α4, α5, α6, α7, α8, α9, α10]
      using (floorStep0_10Integrator_eq_floor hx).symm
  let hFloor : RSIntegrable f (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10 :=
    rsIntegrable_congr_integrator_Icc hSteps hFloorMono hEq
  refine ⟨hFloor, ?_⟩
  change rsIntegral f (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10 hFloor = 385
  calc
    rsIntegral f (fun x : ℝ => (⌊x⌋ : ℝ)) 0 10 hFloor =
        rsIntegral f
          (fun x => ((((((((α1 x + α2 x) + α3 x) + α4 x) + α5 x) + α6 x) +
            α7 x) + α8 x) + α9 x) + α10 x)
          0 10 hSteps := rsIntegral_congr_integrator_Icc hSteps hFloorMono hEq
    _ = 385 := hvSteps

def floorStep0_2Integrator (x : ℝ) : ℝ :=
  (if x < (1 : ℝ) then (0 : ℝ) else 1) +
    (if x < (2 : ℝ) then (0 : ℝ) else 1)

lemma floorStep0_2Integrator_eq_floor {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    floorStep0_2Integrator x = (⌊x⌋ : ℝ) := by
  rcases hx with ⟨h0, h2bound⟩
  by_cases h1 : x < (1 : ℝ)
  · have h2 : x < (2 : ℝ) := by linarith
    have hfloor : ⌊x⌋ = (0 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_2Integrator, h1, h2, hfloor]
  by_cases h2 : x < (2 : ℝ)
  · have hge1 : (1 : ℝ) ≤ x := le_of_not_gt h1
    have hfloor : ⌊x⌋ = (1 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_2Integrator, h1, h2, hfloor]
  · have hge2 : (2 : ℝ) ≤ x := le_of_not_gt h2
    have hfloor : ⌊x⌋ = (2 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    norm_num [floorStep0_2Integrator, h1, h2, hfloor]

/-- The single-jump square-root summand used in Problem 1.8(b). -/
theorem rsIntegral_sqrt_unitJump_0_2
    {c : ℝ} (hc0 : 0 < c) (hc2 : c ≤ 2) :
    ∃ h : RSIntegrable Real.sqrt
        (fun x : ℝ => if x < c then (0 : ℝ) else 1) 0 2,
      rsIntegral Real.sqrt
          (fun x : ℝ => if x < c then (0 : ℝ) else 1) 0 2 h = Real.sqrt c := by
  have hAbove : BddAbove (Real.sqrt '' Icc (0 : ℝ) 2) := by
    refine ⟨Real.sqrt 2, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact Real.sqrt_le_sqrt hx.2
  have hBelow : BddBelow (Real.sqrt '' Icc (0 : ℝ) 2) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, _hx, rfl⟩
    exact Real.sqrt_nonneg x
  have hcont : ContinuousAt Real.sqrt c := Real.continuous_sqrt.continuousAt
  obtain ⟨h, hv⟩ := rsIntegral_singleJumpStep_exists
    (f := Real.sqrt) (a := 0) (b := 2) (c := c)
    (u₁ := 0) (u₂ := 1) (by norm_num) hc0 hc2 (by norm_num)
    hAbove hBelow hcont
  refine ⟨h, ?_⟩
  simpa using hv

/-- The floor part of Problem 1.8(b): only the jumps at `1` and `2`
contribute to the Riemann--Stieltjes integral. -/
theorem rsIntegral_sqrt_floor_0_2 :
    ∃ h : RSIntegrable Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ)) 0 2,
      rsIntegral Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ)) 0 2 h =
        1 + Real.sqrt 2 := by
  let α1 : ℝ → ℝ := fun x => if x < (1 : ℝ) then (0 : ℝ) else 1
  let α2 : ℝ → ℝ := fun x => if x < (2 : ℝ) then (0 : ℝ) else 1
  obtain ⟨h1, hv1⟩ := rsIntegral_sqrt_unitJump_0_2 (c := 1) (by norm_num) (by norm_num)
  obtain ⟨h2, hv2⟩ := rsIntegral_sqrt_unitJump_0_2 (c := 2) (by norm_num) (by norm_num)
  have hv1' : rsIntegral Real.sqrt α1 0 2 h1 = 1 := by
    dsimp [α1]
    rw [hv1]
    norm_num
  have hv2' : rsIntegral Real.sqrt α2 0 2 h2 = Real.sqrt 2 := by
    simpa [α2] using hv2
  let hSteps : RSIntegrable Real.sqrt (fun x => α1 x + α2 x) 0 2 :=
    rsIntegrable_integrator_add h1 h2
  have hvSteps :
      rsIntegral Real.sqrt (fun x => α1 x + α2 x) 0 2 hSteps =
        1 + Real.sqrt 2 := by
    rw [rsIntegral_integrator_add h1 h2, hv1', hv2']
  have hFloorMono : MonotoneOn (fun x : ℝ => (⌊x⌋ : ℝ)) (Icc (0 : ℝ) 2) := by
    intro x _hx y _hy hxy
    change ((⌊x⌋ : ℤ) : ℝ) ≤ ((⌊y⌋ : ℤ) : ℝ)
    exact_mod_cast Int.floor_mono hxy
  have hEq : ∀ x ∈ Icc (0 : ℝ) 2, (⌊x⌋ : ℝ) = α1 x + α2 x := by
    intro x hx
    simpa [floorStep0_2Integrator, α1, α2] using (floorStep0_2Integrator_eq_floor hx).symm
  let hFloor : RSIntegrable Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ)) 0 2 :=
    rsIntegrable_congr_integrator_Icc hSteps hFloorMono hEq
  refine ⟨hFloor, ?_⟩
  change rsIntegral Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ)) 0 2 hFloor = 1 + Real.sqrt 2
  calc
    rsIntegral Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ)) 0 2 hFloor =
        rsIntegral Real.sqrt (fun x => α1 x + α2 x) 0 2 hSteps :=
          rsIntegral_congr_integrator_Icc hSteps hFloorMono hEq
    _ = 1 + Real.sqrt 2 := hvSteps

/-- The identity-integrator contribution in Problem 1.8(b). -/
theorem rsIntegral_sqrt_id_0_2 :
    ∃ h : RSIntegrable Real.sqrt (fun x : ℝ => x) 0 2,
      rsIntegral Real.sqrt (fun x : ℝ => x) 0 2 h =
        (4 * Real.sqrt 2) / 3 := by
  have hCont : ContinuousOn Real.sqrt (Icc (0 : ℝ) 2) :=
    Real.continuous_sqrt.continuousOn
  have hValue :
      ∫ x in (0 : ℝ)..2, Real.sqrt x =
        (4 * Real.sqrt 2) / 3 := by
    rw [show (fun x : ℝ => Real.sqrt x) = fun x : ℝ => x ^ ((1 : ℝ) / 2) by
      funext x
      rw [Real.sqrt_eq_rpow]]
    rw [integral_rpow (a := (0 : ℝ)) (b := 2) (r := (1 : ℝ) / 2)
      (Or.inl (by norm_num))]
    norm_num
    have hpow : (2 : ℝ) ^ ((3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
      have hExp : ((3 : ℝ) / 2) = 1 + (1 / 2 : ℝ) := by norm_num
      rw [hExp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      rw [← Real.sqrt_eq_rpow]
    rw [hpow]
    ring
  let hW : RSIntegralWitness Real.sqrt (fun x : ℝ => x) 0 2 := {
    value := ∫ x in (0 : ℝ)..2, Real.sqrt x
    source_limit :=
      Thm_1_4.rsUpperLowerCommonLimit_intervalIntegral_id
        (g := Real.sqrt) (a := 0) (b := 2) (by norm_num) hCont
    tagged_limit :=
      Thm_1_4.rsTaggedCommonLimit_intervalIntegral_id
        (g := Real.sqrt) (a := 0) (b := 2) (by norm_num) hCont
  }
  let hRS : RSIntegrable Real.sqrt (fun x : ℝ => x) 0 2 := ⟨hW⟩
  refine ⟨hRS, ?_⟩
  calc
    rsIntegral Real.sqrt (fun x : ℝ => x) 0 2 hRS =
        ∫ x in (0 : ℝ)..2, Real.sqrt x := by
          exact DarbouxRS.taggedCommonLimit_unique (rsIntegral_spec hRS)
            (Thm_1_4.rsTaggedCommonLimit_intervalIntegral_id
              (g := Real.sqrt) (a := 0) (b := 2) (by norm_num) hCont)
    _ = (4 * Real.sqrt 2) / 3 := hValue

/-- Standard evaluated value for Problem 1.8(b). -/
theorem rsIntegral_sqrt_floor_add_id_0_2 :
    ∃ h : RSIntegrable Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ) + x) 0 2,
      rsIntegral Real.sqrt (fun x : ℝ => (⌊x⌋ : ℝ) + x) 0 2 h =
        1 + (7 * Real.sqrt 2) / 3 := by
  obtain ⟨hFloor, hFloorVal⟩ := rsIntegral_sqrt_floor_0_2
  obtain ⟨hId, hIdVal⟩ := rsIntegral_sqrt_id_0_2
  refine ⟨rsIntegrable_integrator_add hFloor hId, ?_⟩
  rw [rsIntegral_integrator_add hFloor hId, hFloorVal, hIdVal]
  ring

