import ToyApollo.Output.def_1_4

open Filter MeasureTheory Set

noncomputable section

/-!
Source-level truncation support for Theorem 7.9.

The theorem truncates `g` and `|g|` to symmetric finite intervals before using
MCT/DCT and the finite-interval bridge.  This file owns only those elementary
truncation facts.
-/

/-- The symmetric finite truncation used in the source proof of Theorem 7.9. -/
def thm_7_9_trunc (g : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (Icc (-(n : ℝ)) (n : ℝ)).indicator g

theorem thm_7_9_trunc_measurable {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (thm_7_9_trunc g n) := by
  exact hg.indicator measurableSet_Icc

theorem thm_7_9_trunc_support_subset (g : ℝ → ℝ) (n : ℕ) :
    Function.support (thm_7_9_trunc g n) ⊆ Icc (-(n : ℝ)) (n : ℝ) := by
  intro x hx
  by_contra hmem
  exact hx (by simp [thm_7_9_trunc, hmem])

theorem thm_7_9_abs_trunc_eq (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    |thm_7_9_trunc g n x| =
      thm_7_9_trunc (fun y => |g y|) n x := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · simp [thm_7_9_trunc, hx]
  · simp [thm_7_9_trunc, hx]

theorem thm_7_9_trunc_abs_le (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    |thm_7_9_trunc g n x| ≤ |g x| := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) (n : ℝ)
  · simp [thm_7_9_trunc, hx]
  · simp [thm_7_9_trunc, hx]

theorem thm_7_9_trunc_eventually_eq_self (g : ℝ → ℝ) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, thm_7_9_trunc g n x = g x := by
  rcases exists_nat_gt |x| with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by
    exact_mod_cast hn
  have hxabs : |x| ≤ (n : ℝ) := le_trans (le_of_lt hN) hNn
  have hxmem : x ∈ Icc (-(n : ℝ)) (n : ℝ) := by
    exact (abs_le.mp hxabs)
  exact Set.indicator_of_mem hxmem g

theorem thm_7_9_trunc_tendsto_self (g : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n : ℕ => thm_7_9_trunc g n x) atTop (nhds (g x)) := by
  have hEq : (fun _ : ℕ => g x) =ᶠ[atTop] fun n : ℕ => thm_7_9_trunc g n x :=
    (thm_7_9_trunc_eventually_eq_self g x).mono fun _ hn => hn.symm
  exact Filter.Tendsto.congr' hEq tendsto_const_nhds

theorem thm_7_9_abs_trunc_tendsto_self (g : ℝ → ℝ) (x : ℝ) :
    Tendsto (fun n : ℕ => thm_7_9_trunc (fun y => |g y|) n x) atTop
      (nhds (|g x|)) := by
  exact thm_7_9_trunc_tendsto_self (fun y => |g y|) x
