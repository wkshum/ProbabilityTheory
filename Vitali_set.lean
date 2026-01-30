/-
  Vitali set
  Proof of Theorem 2.9 in textbook
-/

import Mathlib.Tactic
-- import for the proof of theorem about Vitali set
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable

noncomputable section Vitali_set

namespace Vitali_set

open Classical  -- It is essential to use choice axioms here
open Rat
open Set

/-- `I` is the closed unit interval `[0,1]` in `ℝ`. 
  This is the domain on which the Vitali construction is carried out.
-/
def I : Set ℝ := Icc 0 1

/-- `translate A d` is the mod‑1 translation of a set `A ⊆ ℝ` by a real number `d`.  
  It sends each `x ∈ A` to `fract (x + d) ∈ [0,1)`, using `Int.fract`.  
  This models the equivalence relation on the circle.
-/
def translate (A : Set ℝ) (d : ℝ) : Set ℝ :=
  (fun x => Int.fract (x + d)) '' A

/-- A *Vitali measure* is a function `m : Set ℝ → ENNReal` satisfying:

* **Domain restriction:** sets not contained in `[0,1]` have measure `0`.  
* **Monotonicity:** `A ⊆ B` implies `m A ≤ m B`.  
* **Countable additivity:** disjoint countable unions have additive measure.  
* **Translation invariance:** `m (A + d) = m A` for mod‑1 translation.  
* **Geometric length:** intervals have their usual length.

This is the classical axiom system used to derive the Vitali paradox.
-/
def IsVitaliMeasure (m : Set ℝ → ENNReal) : Prop :=
  -- 0. Domain constraint (m is zero outside I, implicitly) & Empty set is 0
  (∀ A, ¬(A ⊆ I) → m A = 0) ∧ 
  (m ∅ = 0) ∧

  -- 1. Monotonicity
  (∀ A B, A ⊆ I → B ⊆ I → A ⊆ B → m A ≤ m B) ∧

  -- 2. Countable Additivity
  (∀ f : ℕ → Set ℝ, 
    (∀ n, f n ⊆ I) →              -- All sets are in [0,1]
    Pairwise (fun i j => Disjoint (f i) (f j)) →    -- Sets are pairwise disjoint
    m (⋃ n, f n) = ∑' n, m (f n)) ∧

  -- 3. Translation Invariance (mod 1)
  (∀ A, A ⊆ I → ∀ d : ℝ, m (translate A d) = m A) ∧

  -- 4. Geometric Length (m([a,b]) = b - a)
  (∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → 
    m (Icc a b) = ENNReal.ofReal (b - a))


/-- `vitali_rel x y` means that `x - y` is rational.  
This is the equivalence relation used to partition `[0,1]` into rational cosets.
-/
def vitali_rel (x y : ℝ) : Prop := ∃ q : ℚ, x - y = q


-- Proof that this is indeed an equivalence relation 
lemma vitali_rel_equiv : Equivalence vitali_rel := by
  constructor
  · -- Reflexive: x - x = 0, which is rational
    intro x; use 0; simp
  · -- Symmetric: if x - y = q, then y - x = -q
    intro x y ⟨q, h⟩
    use -q
    -- Turn ↑(-q) into -(↑q)
    rw [Rat.cast_neg] 
    -- Substitute q with (x - y)
    rw [← h]
    -- Now prove y - x = -(x - y)
    ring

  · -- Transitive: if x - y = q1 and y - z = q2, then x - z = q1 + q2
    intro x y z ⟨q1, h1⟩ ⟨q2, h2⟩
    use q1 + q2
    -- Turn ↑(q1 + q2) into ↑q1 + ↑q2
    rw [Rat.cast_add]
    -- Substitute q1 and q2
    rw [← h1, ← h2]
    -- Now prove x - z = (x - y) + (y - z)
    ring


--  We define a Setoid on the subtype I = [0,1].
--  Two points in [0,1] are equivalent if their difference is rational.
instance vitaliSetoid : Setoid I :=
  { r := fun x y => vitali_rel x.1 y.1
    iseqv := by
      constructor
      · intro x
        apply vitali_rel_equiv.1
      · -- Symmetric
        intro x y h
        exact vitali_rel_equiv.symm h
      · -- Transitive
        intro x y z h1 h2
        exact vitali_rel_equiv.trans h1 h2
  }


/-- The subtype of rationals in [0, 1) -/
def Q_I_Type := {x : ℚ // 0 ≤ x ∧ x < 1}

/-! 
  We define the sequence by filtering the standard enumeration of ALL rationals.
  We use 'Encodable.decode' which gives the n-th rational (if it exists).
  However, to ensure we get an infinite distinct sequence in [0,1), 
  it is easier to use the fact that Q_I is infinite and Denumerable.
-/

-- Helper instance: The set of rationals in [0,1) is encodable
--Since ℚ is encodable and the predicate `0 ≤ x ∧ x < 1` is decidable,
instance : Encodable Q_I_Type :=
  (inferInstance : Encodable {x : ℚ // 0 ≤ x ∧ x < 1})

-- Helper instance: The set of rationals in [0,1) is infinite 
instance : Infinite Q_I_Type := by
  classical
  refine Infinite.of_injective
    (fun n : ℕ =>
      ⟨(1 : ℚ) / (n + 2),
        by
          constructor
          · -- 0 ≤ 1 / (n + 2)
            have h : (0 : ℚ) < n + 2 := by
              -- n + 2 ≥ 2 > 0
              have : (0 : ℚ) < (2 : ℕ) := by norm_num
              have : (0 : ℚ) < (n : ℚ) + 2 := by
                have hn : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
                linarith
              exact this
            have h' := div_nonneg (show (0 : ℚ) ≤ 1 by norm_num) (le_of_lt h)
            simpa using h'
          · -- 1 / (n + 2) < 1
            have hpos : (0 : ℚ) < n + 2 := by
              have : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
              linarith
            have hlt : (1 : ℚ) < n + 2 := by
              -- n + 2 ≥ 2 > 1
              have : (2 : ℚ) ≤ n + 2 := by
                have : (2 : ℕ) ≤ n + 2 := by exact Nat.le_add_left 2 n 
                exact_mod_cast this
              linarith
            -- use the → direction of `div_lt_one`
            have h' : (1 : ℚ) / (n + 2) < 1 :=
              (div_lt_one hpos).2 hlt
            simpa using h'⟩)
  
    (by -- Injectivity proof
      intro n m h
      have := congrArg Subtype.val h
      have h' : (1 : ℚ) / (n + 2) = 1 / (m + 2) := this
      have hn : (n : ℚ) + 2 ≠ 0 := by linarith
      have hm : (m : ℚ) + 2 ≠ 0 := by linarith
      have := (div_eq_div_iff hn hm).1 h'
      have h'' : (m : ℚ) = n := by
        have := congrArg (fun x => x - (2 : ℚ)) this
        simpa using this
      norm_cast at h''
      exact h''.symm)

instance : Denumerable Q_I_Type :=
  Denumerable.ofEncodableOfInfinite Q_I_Type

--  The bijection between ℕ and the rationals in [0,1).
--  We use '.symm' because 'Denumerable.eqv' gives (Q_I_Type ≃ ℕ).
def q_bij : ℕ ≃ Q_I_Type :=
  (Denumerable.eqv Q_I_Type).symm


/-- The sequence of rationals in [0, 1) as Real numbers -/
noncomputable def q_seq (n : ℕ) : ℝ := (q_bij n).val



/-- A *Vitali set* is a choice of one representative from each equivalence class  
of the relation `x ~ y` iff `x - y ∈ ℚ`, restricted to `[0,1]`.

It is defined using `Quotient.out`, which relies on classical choice.
-/
noncomputable def VitaliSet : Set ℝ :=
  range (fun (x : Quotient vitaliSetoid) => (@Quotient.out _ vitaliSetoid x).val)


/-- The sequence of translated Vitali sets. V_n = V + q_n -/
noncomputable def VitaliSeq (n : ℕ) : Set ℝ := translate VitaliSet (q_seq n)



-- Translate of Vitali sets are disjoint
lemma vitali_seq_disjoint : Pairwise (fun i j => Disjoint (VitaliSeq i) (VitaliSeq j)) := by
  intro i j hij
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  -- Expand definitions to expose the elements v1, v2 and the fractional part logic
  simp only [VitaliSeq, translate, mem_inter_iff, mem_image, Set.mem_empty_iff_false, iff_false]

  intro h_inter
  rcases h_inter with ⟨h_i, h_j⟩
  -- Unpack the first witness (from VitaliSeq i)
  rcases h_i with ⟨v1, hv1_mem, hx1⟩
  -- Unpack the second witness (from VitaliSeq j)
  rcases h_j with ⟨v2, hv2_mem, hx2⟩

  -- 1. Combine the fractional equations
  have h_fract_eq : Int.fract (v1 + q_seq i) = Int.fract (v2 + q_seq j) := by rw [hx1, ← hx2]
  rw [Int.fract_eq_fract] at h_fract_eq
  rcases h_fract_eq with ⟨k, hk⟩

  have h_fract_eq : Int.fract (v1 + q_seq i) = Int.fract (v2 + q_seq j) 
    := by rw [hx1, ← hx2]
  rw [Int.fract_eq_fract] at h_fract_eq
  rcases h_fract_eq with ⟨k, hk⟩
  
  -- 2. Rearrange: v1 - v2 = qj - qi + k. This implies v1 ~ v2.
  have h_diff : v1 - v2 = q_seq j - q_seq i + k := by linarith
  have h_rel : vitali_rel v1 v2 := by
    use (q_bij j).val - (q_bij i).val + k
    rw [h_diff]; simp [q_seq]

  -- 3. Since v1 and v2 are representatives from the quotient, 
  -- v1 ~ v2 implies they are the same representative.
  have h_v_eq : v1 = v2 := by
    -- Retrieve the quotient classes c1, c2 now
    rcases hv1_mem with ⟨c1, rfl⟩
    rcases hv2_mem with ⟨c2, rfl⟩
    
    -- v1 corresponds to representative of c1, v2 to c2.
    -- v1 ~ v2 means Quotient.mk v1 = Quotient.mk v2
    -- The Setoid is defined on I, so we use the subtype elements.
    let v1_sub : I := @Quotient.out _ vitaliSetoid c1
    let v2_sub : I := @Quotient.out _ vitaliSetoid c2
    
    -- The relation h_rel is exactly the equivalence relation for the subtype elements
    have h_equiv : v1_sub ≈ v2_sub := h_rel
    
    -- Therefore their classes are equal
    have h_mk_eq : Quotient.mk vitaliSetoid v1_sub = Quotient.mk vitaliSetoid v2_sub :=
      Quotient.sound h_equiv
      
    -- Since they are output of Quotient.out, their class is just c1 (and c2)
    rw [Quotient.out_eq c1] at h_mk_eq
    rw [Quotient.out_eq c2] at h_mk_eq
    
    -- So c1 = c2, which implies v1 = v2
    rw [h_mk_eq]

  subst h_v_eq
  
  -- 4. Now the equation is qj - qi + k = 0
  have h_k_eq : q_seq j - q_seq i + k = 0 := by linarith [hk]
  
  -- 5. Bound k. Since q_seq ∈ [0, 1), the difference is in (-1, 1). Integer k must be 0.
  have h_k_zero : k = 0 := by
    -- Explicitly state bounds for q_seq in ℝ
    have hi : 0 ≤ q_seq i ∧ q_seq i < 1 := by
      have h := (q_bij i).2
      simp [q_seq]; norm_cast
    have hj : 0 ≤ q_seq j ∧ q_seq j < 1 := by
      have h := (q_bij j).2
      simp [q_seq]; norm_cast
    
    have h_bound : -1 < (k : ℝ) ∧ (k : ℝ) < 1 := by
      -- Use linarith with explicit hypotheses
      rcases hi with ⟨hi_lo, hi_hi⟩
      rcases hj with ⟨hj_lo, hj_hi⟩
      -- Rearrange h_k_eq to k = qi - qj for clarity (optional, linarith should catch it)
      have : (k : ℝ) = q_seq i - q_seq j := by linarith [h_k_eq]
      rw [this]
      constructor <;> linarith
      
    norm_cast at h_bound
    rcases h_bound with ⟨h_gt, h_lt⟩
    -- Convert integer strict inequalities to non-strict
    change -1 < k at h_gt
    -- Convert strict inequalities to non-strict to help linarith
    -- k < 1 ↔ k ≤ 0
    rw [← zero_add 1, Int.lt_add_one_iff] at h_lt
    -- -1 < k ↔ 0 ≤ k
    rw [← Int.add_one_le_iff] at h_gt
    norm_num at h_gt
    linarith


  -- 6. If k=0, then qj = qi. Since q_bij is injective, j = i.
  rw [h_k_zero] at h_k_eq
  -- Simplify `↑0` to `0` and remove it
  simp only [Int.cast_zero, add_zero, sub_eq_zero] at h_k_eq
  
  -- Now h_k_eq is `q_seq j = q_seq i`.
  have h_idx : i = j := by
    unfold q_seq at h_k_eq
    -- Remove the coercion from Rat to Real
    norm_cast at h_k_eq 
    -- Use injectivity of the sequence bijection
    apply q_bij.injective
    apply Subtype.ext
    exact h_k_eq.symm
    
  -- Contradiction
  exact hij h_idx


/-!
  **Helper Lemma 1**: The sequence of translated Vitali sets covers [0, 1).
-/
lemma vitali_covers_Ico : Ico 0 1 ⊆ ⋃ n, VitaliSeq n := by
  intro x hx
  -- 1. Identify the representative y for x's equivalence class
  let c := Quotient.mk vitaliSetoid ⟨x, Ico_subset_Icc_self hx⟩
  let y_sub := @Quotient.out _ vitaliSetoid c
  let y := y_sub.val

  -- 2. Establish that y is in VitaliSet
  have hy : y ∈ VitaliSet := by
    -- y is defined as the value of the representative of c
    use c

  -- 3. x and y are related (x ~ y)
  have h_equiv : ⟨x, Ico_subset_Icc_self hx⟩ ≈ y_sub := Quotient.eq.mp (Quotient.out_eq c).symm
  
  rcases h_equiv with ⟨q_diff, h_diff⟩ -- x - y = q_diff

  -- 4. Consider the fractional part of the difference: fract(x - y)
  -- Since x - y is rational, its fractional part is also rational.
  let q_frac := Int.fract (x - y)

  have h_q_rat : ∃ q_rat : ℚ, (q_rat : ℝ) = q_frac := by
    use Int.fract q_diff
    dsimp [q_frac]
    rw [h_diff]
    simp only [Int.fract]
    -- Distribute the cast over subtraction: ↑(a - b) = ↑a - ↑b
    rw [Rat.cast_sub]
    -- Simplify the integer cast: ↑(↑n) = ↑n
    rw [Rat.cast_intCast]
    -- Use the lemma you found: ⌊↑q⌋ = ⌊q⌋
    rw [Rat.floor_cast]

  rcases h_q_rat with ⟨q_rat, h_q_eq⟩    

  -- 5. Show this rational is in our enumeration range [0, 1)
  have h_mem_Q_I : 0 ≤ q_rat ∧ q_rat < 1 := by
    rw [← Rat.cast_le (K := ℝ), ← Rat.cast_lt (K := ℝ), h_q_eq]
    simp only [Rat.cast_zero, Rat.cast_one]     
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  -- 6. Find the index n such that q_seq n = fract(x - y)
  let q_elt : Q_I_Type := ⟨q_rat, h_mem_Q_I⟩
  let n := q_bij.symm q_elt

  -- 6. Find the index n such that q_seq n = fract(x - y)
  let q_elt : Q_I_Type := ⟨q_rat, h_mem_Q_I⟩
  let n := q_bij.symm q_elt

  refine mem_iUnion.2 ⟨n, ?_⟩

  -- 7. Show x is in translate VitaliSet (q_seq n)
  use y, hy
  -- We need to prove: x = fract(y + q_seq n)
  rw [q_seq]
  -- Expand the definition of n to see (q_bij.symm q_elt)
  dsimp only [n]
  -- Apply the property: q_bij (q_bij.symm x) = x
  rw [q_bij.apply_symm_apply]
  rw [h_q_eq]

  -- 8. Verify the arithmetic: fract(y + fract(x - y)) = x
  -- Uses the identity: fract(a + fract(b)) = fract(a + b)
  have h_arith : y + Int.fract (x - y) = x - ↑⌊x - y⌋ := by
    rw [Int.fract]
    ring

  -- Substitute back
  rw [h_arith]
  -- Use property: fract(a - integer) = fract(a)
  -- Since x ∈ [0, 1), fract(x) = x
  -- Use property: fract(a - integer) = fract(a)
  rw [Int.fract_sub_intCast]
  
  -- Goal is now: Int.fract x = x  
  exact Int.fract_eq_self.mpr hx


/-- **Helper Lemma 2**: The Vitali Set is contained in [0, 1]
-/
lemma vitali_subset_I : VitaliSet ⊆ I := by
  -- Take an arbitrary element x from VitaliSet
  rintro x ⟨c, rfl⟩
  -- It comes from Quotient.out, which returns a subtype element of I.
  -- The property .2 of the subtype is exactly that the value is in I.
  exact (@Quotient.out _ vitaliSetoid c).2

-- Helper: Range of translation is always in [0, 1)
lemma translate_subset_Ico (A : Set ℝ) (d : ℝ) : translate A d ⊆ Ico 0 1 := by
  rintro x ⟨y, _, rfl⟩
  rw [Set.mem_Ico]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

-- Helper: Range of translation is subset of I
lemma translate_subset_I (A : Set ℝ) (d : ℝ) : translate A d ⊆ I := by
  intro x hx
  have := translate_subset_Ico A d hx
  exact Ico_subset_Icc_self this



/-- `m (VitaliSeq n) = m VitaliSet`.

This lemma states that every rational translate of the Vitali set has the
same measure as the Vitali set itself. It is a direct consequence of the
translation invariance axiom in `IsVitaliMeasure`.

Formally, `VitaliSeq n = translate VitaliSet (q_seq n)`, and the axiom
`m (translate A d) = m A` applies because `VitaliSet ⊆ I`.
-/
lemma measure_vitali_invariant (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m) (n : ℕ) :
    m (VitaliSeq n) = m VitaliSet := by
  -- Unpack translation invariance
  rcases h with ⟨_, _, _, _, h_trans, _⟩
  apply h_trans
  exact vitali_subset_I


/-- **Helper Lemma 3**: Sum of measures equals measure of union.
The measure of the union of all translated Vitali sets equals the sum of
their individual measures.

This is an application of countable additivity: the sets `VitaliSeq n`
are pairwise disjoint and all lie inside `[0,1]`, so the Vitali measure
axioms guarantee

`m (⋃ n, VitaliSeq n) = ∑' n, m (VitaliSeq n)`.
-/

lemma sum_vitali_eq_union (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m) : 
    (∑' n, m (VitaliSeq n)) = m (⋃ n, VitaliSeq n) := by
  rcases h with ⟨_, _, _, h_add, _, _⟩
  apply (h_add VitaliSeq _ _).symm
  · intro n; exact translate_subset_I _ _
  · exact vitali_seq_disjoint


/-- **Helper Lemma 4**: Measure of a singleton is 0.
A Vitali measure assigns measure zero to every singleton `{x}` in `[0,1]`.

This follows from the geometric length axiom:  
`m [x, x] = 0`, and the interval `[x, x]` is exactly the singleton `{x}`.
-/
lemma measure_singleton_zero (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m)
    (x : ℝ) (hx : x ∈ I) : 
  m {x} = 0 := by
  rcases h with ⟨_, _, _, _, _, h_len⟩
  rw [← Set.Icc_self, h_len x x hx.1 le_rfl hx.2]
  simp


/-- **Helper Lemma 5**: Measure of [0, 1) is 1.
The Vitali measure of the half‑open interval `[0,1)` is equal to `1`.

The proof decomposes `[0,1]` as `[0,1) ∪ {1}`, uses countable additivity
on a finite partition, and applies:

* geometric length: `m [0,1] = 1`,
* singleton lemma: `m {1} = 0`.

Thus `m [0,1) = m [0,1] - m {1} = 1`.
-/
lemma measure_Ico_one (m : Set ℝ → ENNReal) (h : IsVitaliMeasure m) : 
    m (Ico 0 1) = 1 := by
  rcases h with ⟨h_dom, h_empty, h_mono, h_add, h_trans, h_len⟩
  have h_union : Icc 0 1 = Ico 0 1 ∪ {1} := by ext; simp [le_iff_lt_or_eq]

  -- 1. Disjointness
  have h_disj : Disjoint (Ico 0 1) {1} := by 
    rw [Set.disjoint_iff_inter_eq_empty]
    ext
    simp only [mem_inter_iff, mem_Ico, zero_le, Nat.lt_one_iff, true_and, mem_singleton_iff,
      mem_empty_iff_false, iff_false, not_and] 
    intro h
    rw [h]
    norm_num

  -- 2. Define the sequence f
  let f : ℕ → Set ℝ := fun n => if n = 0 then Ico 0 1 else if n = 1 then {1} else ∅
  
  have h_sub : ∀ n, f n ⊆ I := by 
    intro n; dsimp [f]; split_ifs <;> simp [I, Ico_subset_Icc_self]
  
  -- 3. Pairwise disjointness  
  have h_pw : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    dsimp [f]
    -- This splits into cases (0 vs 0), (0 vs 1), (1 vs 0), (1 vs 1), etc.
    split_ifs <;> try (simp; done)
    -- We are left with the diagonal cases (0 vs 0, 1 vs 1) which are contradictions,
    -- and the cross cases (0 vs 1, 1 vs 0) which are valid disjointness.
    -- We use a sequence of tactics to handle any of them order-independently.
    all_goals {
      try simp_all           -- Solves the contradictions (i=j vs i≠j)
      try exact h_disj       -- Solves Disjoint (Ico 0 1) {1}
      try exact h_disj.symm  -- Solves Disjoint {1} (Ico 0 1)
    }
    
  have h_sum := h_add f h_sub h_pw

  -- 4. Prove Union f = Icc 0 1
  have h_U : (⋃ n, f n) = Icc 0 1 := by
    -- Apply extensionality first to match elements
    ext x
    constructor    
    · intro hx
      -- Explicitly rewrite with mem_iUnion to ensure n is treated as ℕ
      rw [mem_iUnion] at hx
      rcases hx with ⟨n, hn⟩
      dsimp [f] at hn
      by_cases h0 : n = 0
      · subst h0; simp at hn; exact Ico_subset_Icc_self hn
      by_cases h1 : n = 1
      · subst h1; simp at hn; rw [hn]; exact right_mem_Icc.2 zero_le_one
      · -- If n is neither 0 nor 1, f n is empty, so x cannot be in it
        simp [h0, h1] at hn
    · -- Backward:  x ∈ Icc 0 1 → x ∈ ⋃ n, f n
      intro hx
      -- Rewrite hx using the decomposition lemma
      rw [mem_Icc] at hx
      -- Split cases on whether x is the endpoint 1 or inside [0, 1)
      by_cases h_eq : x = 1
      · -- Case x = 1: found in index 1
        rw [mem_iUnion]; use 1
        dsimp [f]; simp [h_eq]
      · -- Case x ≠ 1: found in index 0 (since 0 ≤ x ≤ 1 and x ≠ 1 implies x < 1)
        rw [mem_iUnion]; use 0
        dsimp [f]; rw [mem_Ico]
        exact ⟨hx.1, lt_of_le_of_ne hx.2 h_eq⟩

  -- rw [tsum_eq_add_tsum_ite (b := 0), tsum_eq_add_tsum_ite (b := 1)] at h_sum
  simp [f] at h_sum

  -- 5. Calculate sum using Finset  
  have h_sum_calc : (∑' n, m (f n)) = m (Ico 0 1) + m {1} := by
    let s : Finset ℕ := {0, 1}
    -- Support condition
    have h_supp : ∀ n, n ∉ s → m (f n) = 0 := by
      intro n hn
      rw [Finset.mem_insert, Finset.mem_singleton] at hn
      push_neg at hn
      dsimp [f]
      rw [if_neg hn.1, if_neg hn.2]
      exact h_empty
    
    rw [tsum_eq_sum h_supp]
    -- Expand finite sum {0, 1}
    rw [Finset.sum_pair (by norm_num : 0 ≠ 1)]
    dsimp [f]
    
  -- 6. Define known values
  have h_meas_one : m {1} = 0 := 
    measure_singleton_zero m 
      (by exact ⟨h_dom, h_empty, h_mono, h_add, h_trans, h_len⟩) 1 (by simp [I])
  have h_meas_I : m (Icc 0 1) = 1 := 
    by rw [h_len 0 1 le_rfl zero_le_one le_rfl]; simp

  -- 7. Final Calculation using the Additivity Hypothesis
  calc m (Ico 0 1)
    _ = m (Ico 0 1) + 0 := by rw [add_zero]
    _ = m (Ico 0 1) + m {1} := by rw [h_meas_one]
    _ = ∑' n, m (f n) := by rw [h_sum_calc]
    _ = m (⋃ n, f n) := (h_add f h_sub h_pw).symm
    _ = m (Icc 0 1) := by rw [h_U]
    _ = 1 := h_meas_I




/-- **There is no Vitali measure.**

Assume `m` satisfies the Vitali axioms.  
Let `V` be a Vitali set and `Vₙ = V + qₙ` its rational translates.

Key facts:
* the sets `Vₙ` are pairwise disjoint,
* they cover `[0,1)`,
* translation invariance forces `m(Vₙ) = c` for all `n`,
* countable additivity gives `m (⋃ Vₙ) = ∑ c`.

Two cases:
1. `c = 0`: then the sum is `0`, contradicting `m([0,1)) = 1`;
2. `c > 0`: then the sum is `∞`, contradicting `m([0,1)) ≤ 1`.

Thus no such measure `m` can exist.
-/
theorem not_exists_vitali_measure : ¬ ∃ m, IsVitaliMeasure m := by
  intro h
  rcases h with ⟨m, h_V⟩ 
  
  -- Helper: Measure of a singleton is 0
  -- have h_sing : ∀ x ∈ I, m {x} = 0 := by
  --   intro x hx
  --   exact measure_singleton_zero m h_V x hx

  have h_V_sub_I : VitaliSet ⊆ I := by
    rintro x ⟨c, rfl⟩
    exact (@Quotient.out _ vitaliSetoid c).2

  have h_disjoint : Pairwise (fun i j => Disjoint (VitaliSeq i) (VitaliSeq j)) 
    := by exact vitali_seq_disjoint
 
  have h_cover : Ico 0 1 ⊆ ⋃ n, VitaliSeq n := vitali_covers_Ico

  -- apply the countable additivity assumption
  have h_sum_eq : (∑' n, m (VitaliSeq n)) = m (⋃ n, VitaliSeq n) := 
    -- Bundle the loose hypotheses back into the structure to call the lemma
    sum_vitali_eq_union m h_V

  have h_invariant : ∀ n, m (VitaliSeq n) = m VitaliSet := 
    measure_vitali_invariant m h_V

  have h_one_le_union : 1 ≤ m (⋃ n, VitaliSeq n) := by 
    rw [← measure_Ico_one m h_V]
    rcases h_V with ⟨_, _, h_mono, _, _, _⟩
    apply h_mono (Ico 0 1) (⋃ n, VitaliSeq n)
    · exact Ico_subset_Icc_self
    · apply Set.iUnion_subset; intro n; exact translate_subset_I _ _
    · exact h_cover

  have h_union_le_one : m (⋃ n, VitaliSeq n) ≤ 1 := by 
    rcases h_V with ⟨_, _, h_mono, _, _, h_len⟩
    
    -- 1. Show m(I) = 1
    have h_m_I : m I = 1 := by
      rw [I, h_len 0 1 le_rfl zero_le_one le_rfl]
      simp
      
    -- 2. Rewrite the goal to match h_mono
    rw [← h_m_I]
    
    -- 3. Apply monotonicity
    apply h_mono (⋃ n, VitaliSeq n) I
    · -- Union is subset of I
      apply Set.iUnion_subset
      intro n
      exact translate_subset_I _ _
    · -- I is subset of I
      exact rfl.le
    · -- Union is subset of I (same as first goal)
      apply Set.iUnion_subset
      intro n
      exact translate_subset_I _ _


  let c := m VitaliSet

  -- Rewrite the sum to be explicitly ∑ c
  have h_sum_c : (∑' n, m (VitaliSeq n)) = ∑' (n : ℕ), c := by
    congr; ext n; exact h_invariant n
  
  rw [h_sum_c] at h_sum_eq

  by_cases hc0 : c = 0
  · -- Case c = 0
    rw [hc0, tsum_zero] at h_sum_eq  -- Sum of zeros is 0
    rw [← h_sum_eq] at h_one_le_union
    -- We have 1 ≤ 0, contradiction
    exact not_le_of_gt zero_lt_one h_one_le_union
  · -- If c > 0, the infinite sum of c is ∞ (top).
    -- This implies m(Union) = ∞.
    rw [ENNReal.tsum_const_eq_top_of_ne_zero hc0] at h_sum_eq -- Sum is ∞
    rw [← h_sum_eq] at h_union_le_one
    -- We know 1 < ⊤, so ⊤ ≤ 1 is impossible.
    apply not_le_of_gt ENNReal.one_lt_top h_union_le_one

end Vitali_set
