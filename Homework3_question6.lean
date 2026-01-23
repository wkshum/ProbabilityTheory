/-

 Theorem: If S is a semi-algebra, then the collection F of finite disjoint unions of sets in S
  is an algebra.
  We also prove that F is the smallest such algebra containing S.

-/

import Mathlib.Tactic

set_option linter.style.commandStart false
set_option linter.style.openClassical false

open Set

open Classical

variable {X : Type*}
variable (S : Set (Set X))

namespace SemiAlgebraProb

-- The definition of a Semi-Algebra  
structure IsSemiAlgebra (S : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ S
  univ_mem  : univ ∈ S
  inter_mem : ∀ A B, A ∈ S → B ∈ S → A ∩ B ∈ S
  -- For all A in S, there exists an n, and a sequence f indexed by 0...n-1
  -- 1. such that all sets in the sequence are in S
  -- 2. the sets in the sequence are pairwise disjoint, and
  -- 3. the union of the sets in the sequence equals the complement of A
  compl_mem :
    ∀ A, A ∈ S → ∃ (n : ℕ) (f : Fin n → Set X),
      (∀ i, f i ∈ S) ∧                   -- 1. All sets are in S
      (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧   -- 2. Explicit Pairwise Disjointness
      Aᶜ = ⋃ i, f i                      -- 3. The union equals the complement

/-
 Condition c:  
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

/- Condition c' :
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
Part 1: Prove that under the assumption of the first three axioms of a semi-algebra,
  conditions (c) and (c') are equivalent.
-/
theorem conditions_equiv (S : Set (Set X))
    -- (h_empty : ∅ ∈ S)  This axiom is not used in the proof
    (h_univ : univ ∈ S)
    (h_inter : ∀ A B, A ∈ S → B ∈ S → A ∩ B ∈ S) :
    Condition_c S ↔ Condition_c_prime S := by
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


-- Define an Algebra (closed under complement and finite union)
structure IsAlgebra (A : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ A
  compl_mem : ∀ s, s ∈ A → sᶜ ∈ A
  union_mem : ∀ s t, s ∈ A → t ∈ A → s ∪ t ∈ A

/--
The collection F consisting of finite disjoint unions of elements of S.
A set A is in F if there exists a finite disjoint sequence in S whose union is A.
-/
def FiniteDisjointUnions (S : Set (Set X)) : Set (Set X) :=
  { A | ∃ (n : ℕ) (f : Fin n → Set X),
        (∀ i, f i ∈ S) ∧                   -- f_i are in S
        (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧   -- pairwise disjoint
        A = ⋃ i, f i }                     -- A is their union

/-- Lemma: S is a subset of F (since A = A ∪ ∅ ∪ ∅...) -/
theorem S_subset_F : S ⊆ FiniteDisjointUnions S := by
  intro A hA
  -- We represent A as a union of a sequence of length 1: f(0) = A
  use 1, (fun _ ↦ A)
  simp; constructor
  · exact hA
  · exact Eq.symm (iUnion_const A)

-- helper lemma
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
    simp
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
      have hk : e k = ⟨i, j⟩ := by simp [k]
      have : x ∈ f i ∩ g j := ⟨hi, hj⟩
      simpa [h, hk] using this
    · intro hx
      rcases mem_iUnion.1 hx with ⟨k, hkx⟩
      have hx_f : x ∈ f (e k).1 := by exact mem_of_mem_inter_left hkx
      have hx_g : x ∈ g (e k).2 := by exact mem_of_mem_inter_right hkx
      refine ⟨?_, ?_⟩
      · exact mem_iUnion.2 ⟨(e k).1, hx_f⟩
      · exact mem_iUnion.2 ⟨(e k).2, hx_g⟩



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
  

