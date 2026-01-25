/-

 Question 6 in Homework 3
  Semi-Algebra and Algebra of Sets

-/

import Mathlib.Tactic

set_option linter.style.commandStart false
set_option linter.style.openClassical false

open Set

open Classical

namespace SemiAlgebraProb

variable {X : Type*}

variable (S : Set (Set X))  -- S is a set of sets in X

-- The definition of a Semi-Algebra
-- A collection S of subsets of X is a semi-algebra if:
-- (a) empty set is in S and X is in S
-- (b) S is closed under intersection
-- (c) for all A in S, Aᶜ is a finite disjoint union of sets in S
-- The last condition is formulated as:
--   For all A in S, there exists an n, and a sequence f indexed by 0...n-1
--   1. such that all sets in the sequence are in S
--   2. the sets in the sequence are pairwise disjoint, and
--   3. the union of the sets in the sequence equals the complement of A
structure IsSemiAlgebra (S : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ S
  univ_mem  : univ ∈ S
  inter_mem : ∀ A B, A ∈ S → B ∈ S → A ∩ B ∈ S
  compl_mem :
    ∀ A, A ∈ S → ∃ (n : ℕ) (f : Fin n → Set X),
      (∀ i, f i ∈ S) ∧                   -- 1. All sets are in S
      (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧   -- 2. Explicit Pairwise Disjointness
      Aᶜ = ⋃ i, f i                      -- 3. The union equals the complement


-- Formulate the meaning of Algebra as a structure (closed under complement and finite union)
structure IsAlgebra (A : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ A
  compl_mem : ∀ s, s ∈ A → sᶜ ∈ A
  union_mem : ∀ s t, s ∈ A → t ∈ A → s ∪ t ∈ A



/-
### Part 1: 
  Prove that under the assumption of axioms (a) and (b) of a semi-algebra,
    axioms (c) and (c') are equivalent.
-/


/-
Define Condition (c):  
  If $A\in\mathcal{S}$ then $A^c$ is a finite disjoint union of sets
  in \(\mathcal{S}\), i.e. there exist integer $n\geq 1$ and 
  pairwise disjoint $B_1,\dots,B_n\in\mathcal{S}$ 
  with $A^c= \bigcup_{i=1}^n B_i$.
-/
def Condition_c (S : Set (Set X)) : Prop :=
  ∀ A ∈ S, ∃ (n : ℕ) (f : Fin n → Set X),
    (∀ i, f i ∈ S) ∧
    (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧ -- i ≠ j implies intersection is empty
    Aᶜ = ⋃ i, f i

/- 
Define Condition (c') :
  For $A,B\in\mathcal{S}$, with $A\subset B$, 
  there exists integer $n\geq 1$ and pairwise disjoint 
  $A_1,\ldots, A_n \in \mathcal{S}$ such that 
  $B = A\cup A_1 \cup A_2 \cup \cdots \cup A_n$.
-/
def Condition_c_prime (S : Set (Set X)) : Prop :=
  ∀ A B, A ∈ S → B ∈ S → A ⊆ B →
    ∃ (n : ℕ) (f : Fin n → Set X),
      (∀ i, f i ∈ S) ∧
      (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧
      B \ A = ⋃ i, f i

/-
Solution 1. More mathematically styled proof
-/
theorem conditions_equiv
    (S : Set (Set X))
    (h_univ : univ ∈ S)
    (h_inter : ∀ A B, A ∈ S → B ∈ S → A ∩ B ∈ S) :
    Condition_c S ↔ Condition_c_prime S :=
by
  constructor

    --------------------------------------------------------------------
    -- (c) ⇒ (c′)
    --------------------------------------------------------------------
  · intro hc
    refine fun A B hA hB hAB => ?_

    -- Apply condition (c) to A to decompose Aᶜ
    obtain ⟨n, f, hfS, hf_disj, hAcompl⟩ := hc A hA

    -- Define g_i = B ∩ f_i
    let g : Fin n → Set X := fun i => B ∩ f i
    
    refine ⟨n, g, ?_, ?_, ?_⟩

    --------------------------------------------------------------------
    -- 1. Each g_i is in S
    --------------------------------------------------------------------
    · intro i
      exact h_inter B (f i) hB (hfS i)

    --------------------------------------------------------------------
    -- 2. The g_i are pairwise disjoint
    --------------------------------------------------------------------
    · intro i j hij
      have hdisj : f i ∩ f j = ∅ := hf_disj i j hij
      calc
        g i ∩ g j
            = (B ∩ f i) ∩ (B ∩ f j) := rfl
        _   = B ∩ (f i ∩ f j) := by
                ext x; constructor <;> intro hx
                · rcases hx with ⟨⟨hxB, hxi⟩, ⟨_, hxj⟩⟩
                  exact ⟨hxB, ⟨hxi, hxj⟩⟩
                · rcases hx with ⟨hxB, ⟨hxi, hxj⟩⟩
                  exact ⟨⟨hxB, hxi⟩, ⟨hxB, hxj⟩⟩
        _   = B ∩ ∅ := by simp [hdisj]
        _   = ∅ := by simp

    --------------------------------------------------------------------
    -- 3. The union of g_i equals B \ A
    --------------------------------------------------------------------
    · have : B \ A = B ∩ Aᶜ := by ext x; simp [diff_eq]
      calc
        B \ A
            = B ∩ Aᶜ := this
        _   = B ∩ (⋃ i, f i) := by simp [hAcompl]
        _   = ⋃ i, (B ∩ f i) := by simp [inter_iUnion]
        _   = ⋃ i, g i := rfl


  --------------------------------------------------------------------
  -- (c′) ⇒ (c)
  --------------------------------------------------------------------
  · intro hc' A hA

    -- A ⊆ univ, so apply (c′) to (A, univ)
    have hA_sub : A ⊆ univ := subset_univ A
    obtain ⟨n, f, hfS, hf_disj, hdiff⟩ :=
      hc' A univ hA h_univ hA_sub

    refine ⟨n, f, hfS, hf_disj, ?_⟩

    -- Convert X \ A to Aᶜ
    have : univ \ A = Aᶜ := by ext x; simp [compl_eq_univ_diff]
    simpa [this] using hdiff


/-
Second solution: More detailed proof with comments
-/
theorem conditions_equiv' (S : Set (Set X))
    -- (h_empty : ∅ ∈ S)  This axiom is not used in the proof
    (h_univ : univ ∈ S)  -- assume X is in S
    (h_inter : ∀ A B, A ∈ S → B ∈ S → A ∩ B ∈ S)  -- assume S is closed under intersection
     : Condition_c S ↔ Condition_c_prime S := by
  constructor
  · -- Direction: (c) implies (c')
    intro hc A B hA hB hSub

    -- 1. Use (c) to decompose Aᶜ
    obtain ⟨n, f, hf_in_S, hf_disj, hf_union⟩ := hc A hA

    -- 2. Define the new sequence g_i = B ∩ f_i
    let g : Fin n → Set X := fun i ↦ B ∩ f i

    -- 3. Show g satisfies the requirements
    use n, g
    constructor
    · -- Requirement 1: Each g_i is in S
      intro i
      -- Since B is in S and f_i is in S, their intersection is in S
      apply h_inter
      · exact hB
      exact hf_in_S i

    constructor
    · -- Requirement 2: g_i and g_j are disjoint if i ≠ j
      intro i j h_neq
      -- We calculate the intersection explicitly:
      -- (B ∩ f_i) ∩ (B ∩ f_j) = B ∩ (f_i ∩ f_j) = B ∩ ∅ = ∅
      calc (g i) ∩ (g j)
        _ = (B ∩ f i) ∩ (B ∩ f j) := rfl
        _ = B ∩ (f i ∩ (B ∩ f j)) := by rw [inter_assoc] -- Move bracket right
        _ = B ∩ (B ∩ (f i ∩ f j)) := by rw [inter_left_comm (f i)] -- Swap middle terms (f i and B)
        _ = (B ∩ B) ∩ (f i ∩ f j) := by rw [← inter_assoc] -- Move bracket left to group Bs
        _ = B ∩ (f i ∩ f j)       := by rw [inter_self] -- B ∩ B is just B
        _ = B ∩ ∅                 := by rw [hf_disj i j h_neq]
        _ = ∅                     := inter_empty B

    · -- Requirement 3: The union matches B \ A
      -- B \ A = B ∩ Aᶜ
      rw [diff_eq]
      -- Replace Aᶜ with the union of f
      rw [hf_union]
      -- Use distributivity: B ∩ (⋃ f_i) = ⋃ (B ∩ f_i)
      rw [inter_iUnion]
      

  · -- Direction: (c') implies (c)
    intro hc_prime A hA
    -- We want to find a decomposition for Aᶜ.
    -- We know Aᶜ = X \ A (where X is `univ`).
    -- Since A ⊆ X, we can use condition (c') on A and X.

    have h_sub : A ⊆ univ := subset_univ A

    -- Apply (c') to A and univ
    obtain ⟨n, f, hf_in_S, hf_disj, hf_union⟩ := hc_prime A univ hA h_univ h_sub

    use n, f
    -- We need to prove 3 small things.
    -- The first two (in S, disjoint) are given directly by hf_in_S and hf_disj.
    refine ⟨hf_in_S, hf_disj, ?_⟩

    -- We just need to show the union equals Aᶜ
    rw [← hf_union]
    -- And we know X \ A is Aᶜ
    rw [compl_eq_univ_diff]


/-
### Part 2
-/

namespace semi_algebra_part2

/-- The underlying space with 3 elements. -/
abbrev X3 : Type := Fin 3

/-- Names for the three points. -/
def a : X3 := 0
def b : X3 := 1
def c : X3 := 2

/-- The collection `S = {∅, univ, {a}, {b}, {c}}` as a `Set (Set X3)`. -/
def T : Set (Set X3) :=
  {s | s = (∅ : Set X3) ∨ s = Set.univ ∨ s = {a} ∨ s = {b} ∨ s = {c}}

-- Empty set is in T
lemma T_empty_mem : (∅ : Set X3) ∈ T := by
  simp [T]

-- X is in T
lemma T_univ_mem : (univ : Set X3) ∈ T := by
  simp [T]

-- T is closed under intersection
lemma T_inter_mem : ∀ s t : Set X3, s ∈ T → t ∈ T → s ∩ t ∈ T := by
  intro s t hs ht
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
  simp [T, a, b, c]

-- Show that if A is int T, then the complement of A 
-- can be expressed as a finite disjoint union of sets in T
theorem T_compl_mem :
    ∀ A, A ∈ T → ∃ (n : ℕ) (f : Fin n → Set X3),
      (∀ i, f i ∈ T) ∧
      (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧
      Aᶜ = ⋃ i, f i := by
  intro A hA
  -- Unfold T and split into the 5 cases
  simp only [T, Set.mem_setOf_eq] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl
  
  -- Case 1: A = ∅. Complement is Univ.
  · refine ⟨1, fun _ ↦ univ, ?_, ?_, ?_⟩
    · simp [T] -- Membership
    · simp       -- Disjointness (vacuous for n=1)
    · exact toFinset_inj.mp rfl       

  -- Case 2: A = Univ. Complement is ∅.
  · refine ⟨0, fun _ ↦ ∅, ?_, ?_, ?_⟩
    · simp       -- Membership (vacuous)
    · simp       -- Disjointness (vacuous)
    · simp       -- Union

  -- Case 3: A = {a}. Complement is {b} ∪ {c}.
  · refine ⟨2, fun i ↦ if i = 0 then {b} else {c}, ?_, ?_, ?_⟩
    · -- 1. Membership
      intro i; fin_cases i <;> simp [T]
    · -- 2. Disjointness
      intro i j hij
      fin_cases i <;> fin_cases j
      · contradiction -- 0 ≠ 0 is false
      · -- {b} ∩ {c} = ∅
        simp [b, c]
      · -- {c} ∩ {b} = ∅
        simp [b, c, Set.inter_comm]
      · contradiction
    · -- 3. Union equals complement
      ext x
      -- We check every element x ∈ {0,1,2}
      fin_cases x
      · -- x = a
        simp [a, b, c]
      · -- x = b
        simp [a, b, c]
      · -- x = c
        simp [a, b, c]

  -- Case 4: A = {b}. Complement is {a} ∪ {c}.
  · refine ⟨2, fun i ↦ if i = 0 then {a} else {c}, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [T]
    · intro i j hij
      fin_cases i <;> fin_cases j
      · contradiction
      · simp [a, c]
      · simp [a, c, Set.inter_comm]
      · contradiction
    · ext x
      fin_cases x
      · simp [a, b, c]
      · simp [a, b, c]
      · simp [a, b, c]

  -- Case 5: A = {c}. Complement is {a} ∪ {b}.
  · refine ⟨2, fun i ↦ if i = 0 then {a} else {b}, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [T]
    · intro i j hij
      fin_cases i <;> fin_cases j
      · contradiction
      · simp [a, b]
      · simp [a, b, Set.inter_comm]
      · contradiction
    · ext x
      fin_cases x
      · simp [a, b, c]
      · simp [a, b, c]
      · simp [a, b, c]


/- 
  Theorem: T is a Semi-Algebra 
-/
theorem T_is_semi_algebra : IsSemiAlgebra T :=
  { empty_mem := T_empty_mem
    univ_mem  := T_univ_mem
    inter_mem := T_inter_mem
    compl_mem := T_compl_mem }



/-- Lemma: {a} ∪ {b} is not in T. -/
lemma ab_union_notin_T : ({a} ∪ {b} : Set X3) ∉ T := by
  intro h
  -- Unfold T to see the 5 possible cases for what {a} ∪ {b} could be equal to
  simp [T] at h
  rcases h with h_eq | h_eq | h_eq | h_eq | h_eq
  
  · -- Case 1: {a} ∪ {b} = ∅
    -- Contradiction: a is in the union but not in empty
    have : a ∈ (∅ : Set X3) := by 
      rw [← h_eq] -- Change goal to: a ∈ {a} ∪ {b}
      simp    
    simp [a] at this

  · -- Case 2: {a} ∪ {b} = univ
    have : c ∈ ({a} ∪ {b} : Set X3) := by 
      simp [h_eq]   -- Replace {a} ∪ {b} with univ
    simp [a, b, c] at this

  · -- Case 3: {a} ∪ {b} = {a}
    -- Contradiction: b is in the union but not in {a}
    have : b ∈ ({a} : Set X3) := by
      rw [← h_eq] -- Change goal to: b ∈ {a} ∪ {b}
      simp 
    simp [a, b] at this

  · -- Case 4: {a} ∪ {b} = {b}
    -- Contradiction: a is in the union but not in {b}
    have : a ∈ ({b} : Set X3) := by
      rw [← h_eq] -- Change goal to: a ∈ {a} ∪ {b}
      simp    
    simp [a, b] at this

  · -- Case 5: {a} ∪ {b} = {c}
    -- Contradiction: a is in the union but not in {c}
    have : a ∈ ({c} : Set X3) := by 
      rw [← h_eq] -- Change goal to: a ∈ {a} ∪ {b}
      simp    
    simp [a, c] at this


/- Show that T is not an algebra
-/
theorem T_not_algebra : ¬ IsAlgebra T := by
  -- Assume T is an algebra (for the sake of contradiction)
  intro h_alg
  
  -- Since T is an algebra, it must contain {a} ∪ {b}
  have h_union_in_T : ({a} ∪ {b} : Set X3) ∈ T := by
    apply h_alg.union_mem
    · simp [T] -- Prove {a} ∈ T
    · simp [T] -- Prove {b} ∈ T

  -- This contradicts our previous lemma
  exact ab_union_notin_T h_union_in_T

end semi_algebra_part2


/-
### Part 3
Show that the collection of sets consdisting of intervals in the form [a,b) is a semi-algebra.
-/


/- 
The collection of half-open intervals on ℝ with extended real endpoints.
A set `s` is in this collection if there exist `a` and `b` of type Extended Real,
 such that `s` consists of all real numbers `x` where `x` (as an EReal) falls in `Ico a b`.
-/
def SemiAlgebraIntervals : Set (Set ℝ) :=
  { s | ∃ (a b : EReal), a ≤ b ∧ s = {x : ℝ | (x : EReal) ∈ Ico a b} }

-- ==========================================================
-- Lemma 1: The Empty Set is in the collection
-- ==========================================================
lemma empty_mem_intervals : ∅ ∈ SemiAlgebraIntervals := by
  -- We need to find a and b such that the set is empty
  -- Let's choose a = 0 and b = 0
  use 0, 0
  
  -- We need to prove: ∅ = {x | ↑x ∈ Ico 0 0}
  -- This is equivalent to proving that for all x, x is NOT in Ico 0 0
  constructor
  · norm_num
  · -- Prove the set is empty
    ext x
    simp only [mem_empty_iff_false, mem_setOf_eq, mem_Ico, false_iff]
    
    -- Goal: ¬(0 ≤ ↑x ∧ ↑x < 0)
    -- This is true because ↑x < 0 and 0 ≤ ↑x are contradictory if the bounds were equal,
    -- but specifically here, Ico a a is always empty because x < a is false if a ≤ x.
    intro h
    -- h.1 is 0 ≤ x, h.2 is x < 0.
    have h_con := lt_of_le_of_lt h.1 h.2
    -- h_con is 0 < 0, which is false
    exact lt_irrefl 0 h_con

-- ==========================================================
-- Lemma 2: The Universe is in the collection
-- ==========================================================
-- Use the interval [-∞, +∞)
lemma univ_mem_intervals : univ ∈ SemiAlgebraIntervals := by
  use ⊥, ⊤
  constructor
  · exact bot_le
  · -- Ico ⊥ ⊤ covers all reals because ⊥ ≤ x < ⊤ is always true
    ext x
    simp only [mem_univ, mem_setOf_eq, mem_Ico, bot_le, true_and]
    -- Goal is now: ↑x < ⊤
    constructor
    · intro _; simp 
    · intro _; trivial

      
    

-- ==========================================================
-- Lemma 3: Closed under Intersection
-- ==========================================================    
lemma inter_mem_intervals  (A B : Set ℝ) 
 (hA : A ∈ SemiAlgebraIntervals) (hB : B ∈ SemiAlgebraIntervals) : 
    A ∩ B ∈ SemiAlgebraIntervals := by
  -- 1. Unwrap definitions (Note: we now get the inequality hypotheses ha_le, hb_le)
  rcases hA with ⟨a1, b1, ha_le, rfl⟩
  rcases hB with ⟨a2, b2, hb_le, rfl⟩

  -- Let's define the standard intersection bounds
  let L := max a1 a2
  let R := min b1 b2

  -- 2. Check if the intersection is valid (L ≤ R) or empty (R < L)
  by_cases h_overlap : L ≤ R
  · -- CASE 1: Valid Overlap
    use L, R
    constructor
    · exact h_overlap -- satisfies a ≤ b
    · ext x
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ico]
      -- Standard intersection logic:
      -- x ∈ [a1, b1) ∩ [a2, b2) ↔ x ∈ [max a1 a2, min b1 b2)
      rw [← mem_Ico, ← mem_Ico, ← mem_inter_iff, Set.Ico_inter_Ico]
      rfl

  · -- CASE 2: Disjoint (Intersection is empty)
    -- If R < L, the intersection is empty.
    -- We must produce a valid interval (a ≤ b) that is empty. [0, 0) works.
    use 0, 0
    constructor
    · exact le_refl 0 -- 0 ≤ 0
    · ext x
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ico]
      
      -- LHS: Ico a1 b1 ∩ Ico a2 b2
      rw [← mem_Ico, ← mem_Ico, ← mem_inter_iff, Set.Ico_inter_Ico]
      
      -- Since L > R (from negation of h_overlap), LHS is empty
      rw [not_le] at h_overlap
      rw [Ico_eq_empty_of_le (le_of_lt h_overlap)]
      
      -- RHS: Ico 0 0 is empty
      rw [← mem_Ico]
      rw [Ico_self]
      
-- ==========================================================
-- Lemma 4: Complement is Finite Disjoint Union
-- ==========================================================
lemma compl_mem_intervals (A : Set ℝ) (hA : A ∈ SemiAlgebraIntervals) :
    ∃ (n : ℕ) (f : Fin n → Set ℝ),
      (∀ i, f i ∈ SemiAlgebraIntervals) ∧
      (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧
      Aᶜ = ⋃ i, f i := by
  -- 1. Unwrap the hypothesis
  rcases hA with ⟨a, b, h_le, rfl⟩

  -- 2. Define the two parts generically
  -- Part 1: (-∞, a) is Ico ⊥ a
  -- Part 2: [b, ∞) is Ico b ⊤
  let f : Fin 2 → Set ℝ := ![
    {x | (x : EReal) ∈ Ico ⊥ a},
    {x | (x : EReal) ∈ Ico b ⊤}
  ]
  
  use 2, f
  
  constructor
  · -- Requirement 1: Verify elements are in SemiAlgebraIntervals
    intro i
    fin_cases i
    · -- Case i=0: (-∞, a)
      -- Is ⊥ ≤ a? Yes, always.
      use ⊥, a
      constructor
      · exact bot_le
      · rfl
    · -- Case i=1: [b, ∞)
      -- Is b ≤ ⊤? Yes, always.
      use b, ⊤
      constructor
      · exact le_top
      · rfl

  constructor
  · -- Requirement 2: Verify disjointness
    intro i j h_neq
    fin_cases i <;> fin_cases j
    · contradiction -- 0 ≠ 0 is false
    
    · -- Case 0 vs 1: (-∞, a) ∩ [b, ∞)
      -- Strategy: Prove "For all x, if x is in the intersection, False"
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      
      -- 1. Unpack membership logic
      -- simp simplifies f 0, f 1, and intersection
      simp only [mem_inter_iff] at hx
      
      -- hx is now: (⊥ ≤ x ∧ x < a) ∧ (b ≤ x ∧ x < ⊤)
      rcases hx with ⟨⟨_, h_lt_a⟩, ⟨h_ge_b, _⟩⟩
      
      -- 2. Mathematical Contradiction
      -- Chain: x < a ≤ b ≤ x  =>  x < x
      have h_con := lt_of_lt_of_le (lt_of_lt_of_le h_lt_a h_le) h_ge_b
      have h_real : x < x := by
        simp at h_con
      exact lt_irrefl x h_real      

    · -- Case 1 vs 0 (Symmetric)
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [mem_inter_iff] at hx
      
      -- hx is now: (b ≤ x ∧ x < ⊤) ∧ (⊥ ≤ x ∧ x < a)
      rcases hx with ⟨⟨h_ge_b, _⟩, ⟨_, h_lt_a⟩⟩
      
      have h_con := lt_of_lt_of_le (lt_of_lt_of_le h_lt_a h_le) h_ge_b
      have h_real : x < x := by
        simp at h_con      
      exact lt_irrefl x h_real      
      
    · contradiction -- 1 ≠ 1 is false

  · -- Requirement 3: Union matches Complement
    ext x
    -- 1. Unwrap the left side (Complement) explicitly
    -- This ensures we get ¬(a ≤ x ∧ x < b) instead of an implication
    simp only [mem_compl_iff, mem_setOf_eq]

    simp only [mem_Ico, not_and, not_lt, Ico_bot, mem_Iio, EReal.coe_lt_top, and_true, mem_iUnion,
      Fin.exists_fin_two, Fin.isValue, Matrix.cons_val_zero, mem_setOf_eq, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, f]
    -- Goal: (a ≤ ↑x → b ≤ ↑x) ↔ ↑x < a ∨ b ≤ ↑x
    
    -- 1. Convert implication (P → Q) to (¬P ∨ Q)
    rw [imp_iff_not_or]
    
    -- 2. Convert ¬(a ≤ x) to (x < a)
    rw [not_le]

-- ==========================================================
-- In summary: The Collection is a semi-Algebra
-- ==========================================================
theorem Intervals_are_SemiAlgebra : IsSemiAlgebra SemiAlgebraIntervals := {
  empty_mem := empty_mem_intervals
  univ_mem  := univ_mem_intervals
  inter_mem := inter_mem_intervals
  compl_mem := compl_mem_intervals
}




/-
### Part 4
  Let F denote the collection of all finite disjoint unions of sets in S. 
  Prove that F is an algebra, and that it is the smallest algebra containing S.
-/



/-
  Define the meaning of "finite disjoint unions of sets in S"
-/
def FiniteDisjointUnions (S : Set (Set X)) : Set (Set X) :=
  { A | ∃ (n : ℕ) (f : Fin n → Set X),
        (∀ i, f i ∈ S) ∧                   -- f_i are in S
        (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧   -- pairwise disjoint
        A = ⋃ i, f i }                     -- A is their union

-- Define F as the collection of finite disjoint unions of sets in S
def F := FiniteDisjointUnions S


-- Helper lemma 1: S is a subset of F (since A = A ∪ ∅ ∪ ∅...) 
theorem S_subset_F' : S ⊆ FiniteDisjointUnions S := by
  intro A hA
  -- We represent A as a union of a sequence of length 1: f(0) = A
  use 1, (fun _ ↦ A)
  simp only [forall_const, ne_eq, inter_self, Fin.forall_fin_one, Fin.isValue, not_true_eq_false,
    IsEmpty.forall_iff, true_and]
  constructor
  · exact hA
  · exact Eq.symm (iUnion_const A)


-- Helper lemma 2: The union over Fin (n+1) can be split into 
-- the union over Fin n and the last element
-- This helper lemma is used in mathematical induction
theorem iUnion_fin_succ {α : Type*} {n : ℕ} (f : Fin (n + 1) → Set α) :
  (⋃ (i : Fin (n + 1)), f i) = (⋃ (i : Fin n), f (Fin.castSucc i)) ∪ f (Fin.last n)
    := by 
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.1 hx with ⟨i, hi⟩
    by_cases h : i.val < n
    · -- `i` is in the first `n` indices
      have hxleft : x ∈ ⋃ i : Fin n, f (Fin.castSucc i) := by
        refine mem_iUnion.2 ?_
        refine ⟨⟨i.val, h⟩, ?_⟩
        have hcast : Fin.castSucc ⟨i.val, h⟩ = i := by
          apply Fin.ext
          rfl
        simpa [hcast] using hi
      exact mem_union_left (f (Fin.last n)) hxleft
    · -- otherwise `i` must be the last index
      have hiLast : i = Fin.last n := Fin.eq_last_of_not_lt h
      have : x ∈ f (Fin.last n) := by simpa [hiLast] using hi
      exact mem_union_right (⋃ i : Fin n, f (Fin.castSucc i)) this
  · intro hx
    have hx' :
        x ∈ (⋃ i : Fin n, f (Fin.castSucc i)) ∨ x ∈ f (Fin.last n) := by
      simpa [Set.mem_union] using hx
    cases hx' with
    | inl hxL =>
        rcases mem_iUnion.1 hxL with ⟨i, hi⟩
        exact mem_iUnion.2 ⟨Fin.castSucc i, hi⟩
    | inr hxR =>
        exact mem_iUnion.2 ⟨Fin.last n, hxR⟩
  
/--
The "Smallest" property:
If B is any algebra containing S, then B contains all finite disjoint unions of S.
-/
theorem F_is_smallest (B : Set (Set X)) (h_alg : IsAlgebra B) (h_sub : S ⊆ B) :
    FiniteDisjointUnions S ⊆ B := by
  intro A hA
  rcases hA with ⟨n, f, hf_in_S, hf_disj, rfl⟩

  -- We must generalize f so the induction hypothesis works for sequences of length k
  induction n with 
  | zero =>
    -- Case n=0: Union over Fin 0 is empty
    simp only [iUnion_of_empty]
    exact h_alg.empty_mem
  | succ k ih =>
    -- Case n = k+1
    -- Use the specific lemma for splitting Fin (k+1) unions
    -- Split the union over `Fin (k+1)` into the first piece and the remaining tail
    rw [iUnion_fin_succ]
    apply h_alg.union_mem
    · -- Part 1: The union of the first k elements
      -- We construct a new sequence of length k: g i = f (Fin.castSucc i)
      apply ih (fun i ↦ f (Fin.castSucc i))
      · -- Subgoal 1: Elements are in S
        intro i
        exact hf_in_S (Fin.castSucc i)
      · -- Subgoal 2: Elements are pairwise disjoint
        -- FIX 2: Use hf_disj and the fact that castSucc is injective
        intro i j h_neq
        apply hf_disj
        -- We need to prove castSucc i ≠ castSucc j
        -- If castSucc i = castSucc j, then i = j, which contradicts h_neq
        intro h_eq
        apply h_neq
        apply Fin.castSucc_inj.mp h_eq
    · -- Second part: The last element
      apply h_sub
      exact hf_in_S (Fin.last k)

-- Prove that F is closed under intersection
lemma F_inter_mem (h_semi : IsSemiAlgebra S) :
    ∀ A B, A ∈ FiniteDisjointUnions S → B ∈ FiniteDisjointUnions S →
    A ∩ B ∈ FiniteDisjointUnions S := by
  classical
  intro A B hA hB
  rcases hA with ⟨n, f, hfS, hf_disj, rfl⟩
  rcases hB with ⟨m, g, hgS, hg_disj, rfl⟩

  -- Re-index `Fin n × Fin m` as `Fin (n*m)`.
  let e : Fin (n * m) ≃ (Fin n × Fin m) := by
    -- `Fintype.equivFin` gives `(Fin n × Fin m) ≃ Fin (card (Fin n × Fin m))`
    -- so we take `.symm` and simp the cardinality.
    simpa [Fintype.card_prod] using (Fintype.equivFin (Fin n × Fin m)).symm

  -- Define the pieces of the intersection: h(k) = f(i) ∩ g(j).
  let h : Fin (n * m) → Set X := fun k => f (e k).1 ∩ g (e k).2

  refine ⟨n * m, h, ?_, ?_, ?_⟩

  · -- each piece is in S, since S is closed under intersection
    intro k
    exact h_semi.inter_mem (f (e k).1) (g (e k).2) (hfS (e k).1) (hgS (e k).2)

  · -- pieces are pairwise disjoint
    intro k₁ k₂ hk
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx1 : x ∈ h k₁ := hx.1
    have hx2 : x ∈ h k₂ := hx.2
    have hx_f1 : x ∈ f (e k₁).1 := mem_of_mem_inter_left hx1 
    have hx_g1 : x ∈ g (e k₁).2 := by exact mem_of_mem_inter_right hx1 
    have hx_f2 : x ∈ f (e k₂).1 := by exact mem_of_mem_inter_left hx2 
    have hx_g2 : x ∈ g (e k₂).2 := by exact mem_of_mem_inter_right hx2

    have hk' : e k₁ ≠ e k₂ := by
      intro hEq
      exact hk (e.injective hEq)

    by_cases hfst : (e k₁).1 = (e k₂).1
    · have hsnd : (e k₁).2 ≠ (e k₂).2 := by
        intro hsndEq
        apply hk'
        exact Prod.ext hfst hsndEq
      have : x ∈ g (e k₁).2 ∩ g (e k₂).2 := ⟨hx_g1, hx_g2⟩
      have : x ∈ (∅ : Set X) := by
        simpa [hg_disj _ _ hsnd] 
      simpa
    · have : x ∈ f (e k₁).1 ∩ f (e k₂).1 := ⟨hx_f1, hx_f2⟩
      have : x ∈ (∅ : Set X) := by
        simpa [hf_disj _ _ hfst] 
      simpa


  · -- finally, show the union of these pieces is exactly the intersection
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxA, hxB⟩
      rcases mem_iUnion.1 hxA with ⟨i, hi⟩
      rcases mem_iUnion.1 hxB with ⟨j, hj⟩
      let k : Fin (n * m) := e.symm ⟨i, j⟩
      refine mem_iUnion.2 ⟨k, ?_⟩
      have hk : e k = ⟨i, j⟩ := by simp only [Equiv.apply_symm_apply, k]
      have : x ∈ f i ∩ g j := ⟨hi, hj⟩
      simpa [h, hk] using this
    · intro hx
      rcases mem_iUnion.1 hx with ⟨k, hkx⟩
      have hx_f : x ∈ f (e k).1 := by exact mem_of_mem_inter_left hkx
      have hx_g : x ∈ g (e k).2 := by exact mem_of_mem_inter_right hkx
      refine ⟨?_, ?_⟩
      · exact mem_iUnion.2 ⟨(e k).1, hx_f⟩
      · exact mem_iUnion.2 ⟨(e k).2, hx_g⟩


-- Prove that if F is closed under complement
lemma F_compl_mem (h_semi : IsSemiAlgebra S) :
    ∀ s, s ∈ FiniteDisjointUnions S → sᶜ ∈ FiniteDisjointUnions S := by
  
  intro s hs
  rcases hs with ⟨n, f, hfS, hf_disj, rfl⟩
  -- prove: (⋃ i, f i)ᶜ ∈ F by induction on n
  revert f hfS hf_disj
  induction n with
  | zero =>
      intro f hfS hf_disj
      -- (⋃ i : Fin 0, f i) = ∅, so complement is univ
      have huniv : (Set.univ : Set X) ∈ FiniteDisjointUnions S := by
        -- univ = (∅)ᶜ, and ∅ ∈ S in a semi-algebra
        simpa using (h_semi.compl_mem (A := (∅ : Set X)) h_semi.empty_mem)
      simpa using huniv
  | succ k ih =>
      intro f hfS hf_disj

      -- Tail union complement is in F by IH
      have htail :
          (⋃ i : Fin k, f (Fin.castSucc i))ᶜ ∈ FiniteDisjointUnions S := by
        apply ih (f := fun i : Fin k => f (Fin.castSucc i))
        · intro i
          exact hfS (Fin.castSucc i)
        · intro i j hij
          -- disjointness is preserved under `castSucc`
          refine hf_disj (Fin.castSucc i) (Fin.castSucc j) ?_
          intro hEq
          refine Nat.not_succ_le_zero i ?_ 
          · simp_all only [ne_eq, compl_iUnion, Fin.castSucc_inj]

      -- Last piece complement is in F by semi-algebra axiom (since last piece ∈ S)
      have hlast : (f (Fin.last k))ᶜ ∈ FiniteDisjointUnions S := by 
        simpa using h_semi.compl_mem (f (Fin.last k)) (hfS (Fin.last k))

      -- Now De Morgan: complement of union = intersection of complements
      have hinter :
          ( (⋃ i : Fin k, f (Fin.castSucc i))ᶜ ∩ (f (Fin.last k))ᶜ )
            ∈ FiniteDisjointUnions S :=
        F_inter_mem (S := S) h_semi _ _ htail hlast

      -- rewrite the original union using `iUnion_fin_succ`
      simpa [iUnion_fin_succ, Set.compl_union] using hinter


/-- Main Theorem: The collection F is an algebra. -/
theorem F_is_algebra (h_semi : IsSemiAlgebra S) :
    IsAlgebra (FiniteDisjointUnions S) := by 
  
  -- Define F as the collection of finite disjoint unions of sets in S
  let F := (FiniteDisjointUnions S)

  -- Show that empty set is in F
  have empty_mem : ∅ ∈ F := by 
    refine ⟨0, (fun i : Fin 0 => (∅ : Set X)), ?_, ?_, ?_⟩
    · simp  -- ∀ i : Fin 0, ... is trivial
    · simp  -- ∀ i j : Fin 0, ... is trivial
    · simp  -- ⋃ i : Fin 0, f i = ∅
  
  -- Show that complement of a set in F is in F
  have union_mem : ∀ s t, s ∈ F → t ∈ F → s ∪ t ∈ F := by 
    intro s t hs ht
    have hsC : sᶜ ∈ F := F_compl_mem (S := S) h_semi s hs
    have htC : tᶜ ∈ F := F_compl_mem (S := S) h_semi t ht
    have hInter : sᶜ ∩ tᶜ ∈ F := F_inter_mem (S := S) h_semi _ _ hsC htC
    have hCompl : (sᶜ ∩ tᶜ)ᶜ ∈ F := F_compl_mem (S := S) h_semi (sᶜ ∩ tᶜ) hInter
    simpa [Set.compl_inter, compl_compl] using hCompl  
  
  exact ⟨empty_mem, F_compl_mem S h_semi, union_mem⟩


end SemiAlgebraProb
