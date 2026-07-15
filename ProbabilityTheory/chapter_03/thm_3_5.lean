import ProbabilityTheory.chapter_03.def_3_8
import Mathlib.Tactic

open Set ENNReal

/-- ## Theorem 3.5  a sufficient condition for sigma-additivity

PROBLEM
A set function `μ` defined on a field `s`, with `μ(∅) = 0`, is `σ`-additive if it is
finitely additive and `σ`-subadditive.

PROVIDED SOLUTION
Prove le_antisymm. For ≤: use h_sigma_subadd directly. For ≥: Show μ(⋃ i, f i) ≥ ∑' i, μ(f i) by showing μ(⋃ i, f i) ≥ ∑ i in Finset.range n, μ(f i) for all n (using monotonicity: ⋃ i < n, f i ⊆ ⋃ i, f i, and finite additivity to get μ(⋃ i < n, f i) = ∑ i in Finset.range n, μ(f i)), then take the supremum over n. Use ENNReal.tsum_eq_iSup_nat or similar to convert tsum to a supremum of partial sums and use le_iSup.

Key steps for the ≥ direction:
1. It suffices to show ∀ n, ∑ i in Finset.range n, μ(f i) ≤ μ(⋃ i, f i), then use ENNReal.tsum_le_of_sum_range_le or take iSup.
2. For each n, show by induction that μ(⋃ i < n, f i) = ∑ i in Finset.range n, μ(f i) using h_fin_add.
3. Show μ(⋃ i < n, f i) ≤ μ(⋃ i, f i) using monotonicity: need to show that μ is monotone on s. For monotonicity: if A ⊆ B and both in s, then B = A ∪ (B \ A), and since s is a field B \ A = B ∩ Aᶜ ∈ s, these are disjoint, so μ(B) = μ(A) + μ(B \ A) ≥ μ(A).
-/
theorem thm_3_5 {α : Type*} (s : Set (Set α)) (μ : Set α → ℝ≥0∞)
    (h_empty_val : μ ∅ = 0)
    (h_field_empty : ∅ ∈ s)
    (h_field_compl : ∀ A ∈ s, Aᶜ ∈ s)
    (h_field_union : ∀ A ∈ s, ∀ B ∈ s, A ∪ B ∈ s)
    (h_fin_add : ∀ A ∈ s, ∀ B ∈ s, Disjoint A B → μ (A ∪ B) = μ A + μ B)
    (h_sigma_subadd : ∀ f : ℕ → Set α, (∀ i, f i ∈ s) → (⋃ i, f i) ∈ s →
      μ (⋃ i, f i) ≤ ∑' i, μ (f i)) :
    ∀ f : ℕ → Set α, (∀ i, f i ∈ s) → (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      (⋃ i, f i) ∈ s → μ (⋃ i, f i) = ∑' i, μ (f i) := by
        intro f hf_disjoint hf_union hf_disjoint'
        have h_monotone : ∀ A B : Set α, A ∈ s → B ∈ s → A ⊆ B → μ A ≤ μ B := by
          intro A B hA hB hAB
          have h_diff : B \ A ∈ s := by
            convert h_field_compl _ ( h_field_union _ hA _ ( h_field_compl _ hB ) ) using 1 ; ext ; aesop;
          have := h_fin_add A hA ( B \ A ) h_diff; simp_all  [ Set.disjoint_sdiff_right ] ;
          rw [ Set.union_eq_right.mpr hAB ] at this; aesop;
        refine' le_antisymm ( h_sigma_subadd f hf_disjoint hf_disjoint' ) _;
        -- For each $n$, we have $\sum_{i=0}^{n-1} \mu(f(i)) \leq \mu(\bigcup_{i=0}^{n-1} f(i))$.
        have h_partial_sum : ∀ n, ∑ i ∈ Finset.range n, μ (f i) ≤ μ (⋃ i < n, f i) := by
          intro n
          have h_partial_sum : μ (⋃ i < n, f i) = ∑ i ∈ Finset.range n, μ (f i) := by
            induction' n with n ih <;> simp_all  [ Finset.sum_range_succ ];
            rw [ ← ih, ← h_fin_add ];
            · congr with x ; simp  [ le_iff_lt_or_eq, or_comm ];
            · refine' Nat.recOn n _ _ <;> simp_all ;
              intro n hn; convert h_field_union _ hn _ ( hf_disjoint n ) using 1; ext; simp [ le_iff_lt_or_eq, or_comm ] ;
            · exact hf_disjoint n;
            · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by rcases Set.mem_iUnion₂.mp hx₁ with ⟨ i, hi, hx₁ ⟩ ; exact Set.disjoint_left.mp ( hf_union i n ( by linarith ) ) hx₁ hx₂;
          rw [h_partial_sum];
        -- Since $\bigcup_{i=0}^{n-1} f(i) \subseteq \bigcup_{i=0}^{\infty} f(i)$, we have $\mu(\bigcup_{i=0}^{n-1} f(i)) \leq \mu(\bigcup_{i=0}^{\infty} f(i))$.
        have h_monotone_union : ∀ n, μ (⋃ i < n, f i) ≤ μ (⋃ i, f i) := by
          intro n
          apply h_monotone
          simp at *;
          · induction' n with n ih <;> simp_all ;
            convert h_field_union _ ih _ ( hf_disjoint n ) using 1 ; ext ; simp  [ le_iff_lt_or_eq, or_comm ];
          · exact hf_disjoint';
          · exact Set.iUnion_subset fun i => Set.iUnion_subset fun hi => Set.subset_iUnion _ _;
        exact le_of_tendsto_of_tendsto' ( ENNReal.tendsto_nat_tsum _ ) tendsto_const_nhds fun n => le_trans ( h_partial_sum n ) ( h_monotone_union n )
