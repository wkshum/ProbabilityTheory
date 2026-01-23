/-
 MAT3280 Homework 2 Question 5

 Show that in a sigma algebra, we can perform
 (a) finite union
 (b) countble intersection, and
 (c) symmetric difference

-/

import Mathlib.Tactic

open Classical  -- we need to work in Classical logic

variable {α : Type}  -- α is a generic type

/-
  Define a data structure for sigma algebra
  There are three requirements:
  1. The empty set is in F
  2. If a set is in F, its complement is also in F
  3. F is closed under countable unions
-/
structure IsSigmaAlgebra (F : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ F
  compl_mem : ∀ s, s ∈ F → sᶜ ∈ F
  -- f is a sequence of sets (f 0, f 1, f 2, ...)
  -- Closure under Countable Union
  iUnion_mem : ∀ (f : ℕ → Set α), (∀ i, f i ∈ F) → (⋃ i, f i) ∈ F


-- 1. Prove that if F is a sigma-algebra, then it is closed under finite unions.
-- We want to prove that s ∪ t is also in F.
theorem union_mem (F : Set (Set α)) (h : IsSigmaAlgebra F) 
    (s t : Set α) (hs : s ∈ F) (ht : t ∈ F) : 
    s ∪ t ∈ F := by
--  The hypotheses are:
-- F is a collection of sets
-- F is a sigma-algebra (the assumption is denoted by h)
-- s and t are in F (this assumption are represented by hs and ht)

  -- Step 1: Define a sequence `f` that represents s ∪ t
  -- f 0 = s, f 1 = t, f 2 = t, ...
  let f : ℕ → Set α := fun i => if i = 0 then s else t

  -- Step 2: Prove that the countable union of `f` equals s ∪ t
  have h_eq : (⋃ i, f i) = s ∪ t := by
    ext x
    simp [f] -- Unwrap the definition of f and Union
    constructor
    · -- If x is in the countable union, it is in s or t
      intro h_union
      rcases h_union with ⟨i, hi⟩ -- There is some index i...
      split at hi -- Split cases based on whether i = 0
      · left; exact hi  -- i=0 implies s
      · right; exact hi -- i≠0 implies t
    · -- If x is in s ∪ t, it is in the countable union
      intro h_union
      cases h_union with
      | inl xs => use 0; simp; exact xs -- Index 0 for s
      | inr xt => use 1; simp; exact xt -- Index 1 for t

  -- Step 3: Rewrite the goal using our equality
  rw [← h_eq]
  -- Step 4: Apply the sigma-algebra rule
  apply h.iUnion_mem
  -- Step 5: Verify every element in our sequence is in F
  intro i
  simp [f]
  split -- Split based on i = 0
  · exact hs -- If i=0, it is s, which is in F
  · exact ht -- If i≠0, it is t, which is in F

-- 2. Theorem: If An are in F, then ⋂ An is in F
theorem sigma_closed_inter (F : Set (Set α)) (hF : IsSigmaAlgebra F) 
  (A : ℕ → Set α) (h_mem : ∀ n, A n ∈ F) : 
  (⋂ n, A n) ∈ F := by

  -- Step 1: Rewrite A as Aᶜᶜ. 
  -- We do this because we want to turn the Intersection into a Union, 
  -- and the standard theorem `compl_iInter` works on (Intersection)ᶜ.
  rw [← compl_compl (⋂ n, A n)]

  -- Step 2: Apply De Morgan's Law: (⋂ A_n)ᶜ = ⋃ (A_nᶜ)
  rw [Set.compl_iInter]

  -- Current Goal: (⋃ n, (A n)ᶜ)ᶜ ∈ F

  -- Step 3: The outer set is a complement, so use the sigma-algebra property
  apply hF.compl_mem

  -- Step 4: Now we have a countable union, use the sigma-algebra property
  apply hF.iUnion_mem

  -- Step 5: Verify that every element inside the union is in F
  intro n
  apply hF.compl_mem
  exact h_mem n


-- 3. Closed under Finite Intersection
-- Strategy: A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ
theorem inter_mem (F : Set (Set α)) (h : IsSigmaAlgebra F) 
    (s t : Set α) (hs : s ∈ F) (ht : t ∈ F) : 
    s ∩ t ∈ F := by
  -- Step 1: Rewrite s ∩ t using double complement
  rw [← compl_compl (s ∩ t)]
  
  -- Step 2: Apply De Morgan's Law: (s ∩ t)ᶜ = sᶜ ∪ tᶜ
  rw [Set.compl_inter]
  
  -- Step 3: Now the goal is (sᶜ ∪ tᶜ)ᶜ ∈ F. 
  -- We peel off the layers using our known rules.
  apply h.compl_mem     -- The outer complement is fine
  apply union_mem F h   -- The union is fine (using your theorem!)
  
  -- Step 4: Prove the parts sᶜ and tᶜ are in F
  · apply h.compl_mem; exact hs
  · apply h.compl_mem; exact ht


-- 4. Set Difference
-- Strategy: A \ B = A ∩ Bᶜ
theorem diff_mem (F : Set (Set α)) (h : IsSigmaAlgebra F) 
    (A B : Set α) (hA : A ∈ F) (hB : B ∈ F) : 
    (A \ B) ∈ F := by
  -- Step 1: Rewrite difference as intersection
  rw [Set.diff_eq]
  
  -- Step 2: Apply the intersection theorem we just proved
  apply inter_mem F h
  
  -- Step 3: Prove A is in F (Given)
  · exact hA
  
  -- Step 4: Prove Bᶜ is in F
  · apply h.compl_mem
    exact hB
