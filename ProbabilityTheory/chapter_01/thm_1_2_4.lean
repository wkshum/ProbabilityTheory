import ProbabilityTheory.chapter_01.def_1_2
import ProbabilityTheory.chapter_01.thm_1_2


/-

  Theorem 1.2 part 4

-/


noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise


-----------------------------------------------------------------------------
-- 1. Analytical Helper Lemmas
-----------------------------------------------------------------------------

/-- Boundedness on [a, b] implies boundedness on the subinterval [a, c]. -/
lemma sourceHypotheses_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (h : SourceHypotheses a b f α) :
    SourceHypotheses a c f α := by
  -- Unpack the hypotheses on the full interval [a, b]
  rcases h with ⟨_hab, hAbove, hBelow, hmono⟩

  -- Establish that [a, c] is a subset of [a, b]
  have h_subset : Set.Icc a c ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (le_of_lt hcb)⟩

  -- Establish the image inclusion manually to avoid Mathlib naming issues
  have h_img_subset : f '' Set.Icc a c ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  -- Construct the new SourceHypotheses
  refine ⟨hac, ?_, ?_, ?_⟩
  · exact BddAbove.mono h_img_subset hAbove
  · exact BddBelow.mono h_img_subset hBelow
  · exact MonotoneOn.mono hmono h_subset



/-- Boundedness on [a, b] implies boundedness on the subinterval [c, b]. -/
lemma sourceHypotheses_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (h : SourceHypotheses a b f α) :
    SourceHypotheses c b f α := by
  -- Unpack the hypotheses on the full interval [a, b]
  rcases h with ⟨_hab, hAbove, hBelow, hmono⟩

  -- Establish that [c, b] is a subset of [a, b]
  have h_subset : Set.Icc c b ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨le_trans (le_of_lt hac) hx.1, hx.2⟩

  -- Establish the image inclusion manually
  have h_img_subset : f '' Set.Icc c b ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  -- Construct the new SourceHypotheses
  refine ⟨hcb, ?_, ?_, ?_⟩
  · exact BddAbove.mono h_img_subset hAbove
  · exact BddBelow.mono h_img_subset hBelow
  · exact MonotoneOn.mono hmono h_subset



noncomputable section SubintervalIntegrability

-----------------------------------------------------------------------------
-- 1. Constructing the Exact Value (Darboux Supremum)
-----------------------------------------------------------------------------

/-- The set of all possible lower sums on the interval [a, c] -/
def lowerSumSet (a c : ℝ) (f α : ℝ → ℝ) : Set ℝ :=
  { y | ∃ P : Partition a c, y = lowerSum P f α }

/--
Because we must explicitly provide a `value` for the integral witness,
we define it analytically as the supremum of all lower sums on [a, c].
-/
noncomputable def lowerDarboux (a c : ℝ) (f α : ℝ → ℝ) : ℝ :=
  sSup (lowerSumSet a c f α)

-----------------------------------------------------------------------------
-- 2. Partition Surgery
-----------------------------------------------------------------------------

/--
Concatenating a partition of [a, c] and a partition of [c, b]
yields a valid, strictly monotonic partition of [a, b].
-/
def concatPartition {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) : Partition a b where
  n := P1.n + P2.n
  hn := by
    have h1 := P1.hn
    have h2 := P2.hn
    omega
  pts := fun i =>
    -- If the index is in the left partition's range, use P1
    if h : i.val ≤ P1.n then
      P1.pts ⟨i.val, by omega⟩
    -- Otherwise, shift the index and use P2
    else
      P2.pts ⟨i.val - P1.n, by have := i.isLt; omega⟩

  pts_start := by
    -- Lean automatically evaluates the `if 0 ≤ P1.n` to true!
    exact P1.pts_start

  pts_end := by
    -- Expose the if/else logic explicitly for the last point
    -- change (if h : (Fin.last (P1.n + P2.n)).val ≤ P1.n then _ else _) = b
    have h_nle : ¬ ((Fin.last (P1.n + P2.n)).val ≤ P1.n) := by
      have h1 := P2.hn
      grind
    rw [dif_neg h_nle]
    -- Prove the shifted index hits the last point of P2
    have eq_last : (⟨(Fin.last (P1.n + P2.n)).val - P1.n, by omega⟩ : Fin (P2.n + 1)) = Fin.last P2.n := by
      ext
      change (P1.n + P2.n) - P1.n = P2.n
      omega
    rw [eq_last]
    exact P2.pts_end

  strict_mono := by
    intro i j hij
    have h_val_lt : i.val < j.val := hij
    -- Expose the if/else logic for both points
    change (if hi : i.val ≤ P1.n then _ else _) < (if hj : j.val ≤ P1.n then _ else _)
    split_ifs with hi hj
    · -- Case 1: Both points are in P1
      apply P1.strict_mono
      exact h_val_lt
    · -- Case 2: i is in P1, j is in P2
      have h_left : P1.pts ⟨i.val, by omega⟩ ≤ P1.pts ⟨P1.n, by omega⟩ := by
        apply P1.strict_mono.monotone
        exact hi
      have eq1 : (⟨P1.n, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; change P1.n = P1.n; omega
      have eq2 : (⟨0, by omega⟩ : Fin (P2.n + 1)) = 0 := by ext; change 0 = 0; omega
      have h_mid1 : P1.pts ⟨P1.n, by omega⟩ = c := by rw [eq1, P1.pts_end]
      have h_mid2 : c = P2.pts ⟨0, by omega⟩ := by rw [eq2, P2.pts_start]

      have h_right : P2.pts ⟨0, by omega⟩ < P2.pts ⟨j.val - P1.n, by omega⟩ := by
        apply P2.strict_mono
        change 0 < j.val - P1.n
        omega

      -- Bypass `rw` entirely by chaining inequalities via transitivity!
      have h_left_c : P1.pts ⟨i.val, by omega⟩ ≤ c := le_trans h_left (le_of_eq h_mid1)
      have h_c_right : c < P2.pts ⟨j.val - P1.n, by omega⟩ := lt_of_eq_of_lt h_mid2 h_right

      exact lt_of_le_of_lt h_left_c h_c_right
    · -- Case 3: i is in P2, j is in P1 (Mathematically impossible)
        exfalso
        omega
    · -- Case 4: Both points are in P2
        apply P2.strict_mono
        change i.val - P1.n < j.val - P1.n
        omega





/-- The mesh of the concatenated partition is bounded by the maximum of the two meshes. -/
lemma concatPartition_mesh {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) :
    (concatPartition P1 P2).mesh ≤ max P1.mesh P2.mesh := by
  unfold Partition.mesh
  apply Finset.sup'_le
  intro i _

  -- We branch on whether the interval index belongs to P1 or P2
  by_cases h_lt : i.val < P1.n
  · -- Case 1: The subinterval is entirely inside P1
    have b1 : i.val < P1.n + 1 := by omega
    have b2 : i.val + 1 < P1.n + 1 := by omega

    have h_cast : (concatPartition P1 P2).pts i.castSucc = P1.pts ⟨i.val, b1⟩ := by
      change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
      have h_cond : i.castSucc.val ≤ P1.n := by
        have : i.castSucc.val = i.val := rfl
        omega
      rw [dif_pos h_cond]
      congr 1;

    have h_succ : (concatPartition P1 P2).pts i.succ = P1.pts ⟨i.val + 1, b2⟩ := by
      change (if h : i.succ.val ≤ P1.n then _ else _) = _
      have h_cond : i.succ.val ≤ P1.n := by
        have : i.succ.val = i.val + 1 := rfl
        omega
      rw [dif_pos h_cond]
      congr 1;

    rw [h_cast, h_succ]

    -- Map it back to the exact subinterval j in P1
    let j : Fin P1.n := ⟨i.val, h_lt⟩
    have eq_succ : (⟨i.val + 1, b2⟩ : Fin (P1.n + 1)) = j.succ := by ext; rfl
    have eq_cast : (⟨i.val, b1⟩ : Fin (P1.n + 1)) = j.castSucc := by ext; rfl
    rw [eq_succ, eq_cast]

    have H_mesh : P1.pts j.succ - P1.pts j.castSucc ≤ P1.mesh := by
      unfold Partition.mesh
      exact Finset.le_sup' (fun (k : Fin P1.n) => P1.pts k.succ - P1.pts k.castSucc) (Finset.mem_univ j)

    exact le_trans H_mesh (le_max_left _ _)

  · -- Case 2: The subinterval belongs to P2
    have h_ge : P1.n ≤ i.val := by omega

    by_cases h_eq : i.val = P1.n
    · -- Subcase 2a: The boundary interval (touches c)
      have h_cast : (concatPartition P1 P2).pts i.castSucc = c := by
        change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
        have h_cond : i.castSucc.val ≤ P1.n := by
          have : i.castSucc.val = i.val := rfl
          omega
        rw [dif_pos h_cond]
        have eq_last : (⟨i.castSucc.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by
          ext
          have : i.castSucc.val = i.val := rfl
          grind
        rw [eq_last, P1.pts_end]

      have b_succ : 1 < P2.n + 1 := by have := P2.hn; omega
      have h_succ : (concatPartition P1 P2).pts i.succ = P2.pts ⟨1, b_succ⟩ := by
        change (if h : i.succ.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.succ.val ≤ P1.n) := by
          have : i.succ.val = i.val + 1 := rfl
          omega
        rw [dif_neg h_cond]
        congr 1; ext
        have : i.succ.val = i.val + 1 := rfl
        grind

      rw [h_cast, h_succ]

      -- Map it to the 0-th subinterval in P2
      let j : Fin P2.n := ⟨0, P2.hn⟩
      have eq_succ : (⟨1, b_succ⟩ : Fin (P2.n + 1)) = j.succ := by ext; rfl
      have eq_cast : P2.pts j.castSucc = c := by
        have h0 : j.castSucc = 0 := by ext; rfl
        rw [h0, P2.pts_start]

      rw [eq_succ]

      have H_mesh : P2.pts j.succ - P2.pts j.castSucc ≤ P2.mesh := by
        unfold Partition.mesh
        exact Finset.le_sup' (fun (k : Fin P2.n) => P2.pts k.succ - P2.pts k.castSucc) (Finset.mem_univ j)

      have H_mesh_c : P2.pts j.succ - c ≤ P2.mesh := by linarith [H_mesh, eq_cast]
      exact le_trans H_mesh_c (le_max_right _ _)

    · -- Subcase 2b: Strictly inside P2
      have h_gt : P1.n < i.val := by omega
      have hi_lt : i.val < P1.n + P2.n := i.isLt

      -- Pre-prove all bounds to keep omega completely isolated and happy!
      have b1 : i.val - P1.n < P2.n + 1 := by omega
      have b2 : i.val + 1 - P1.n < P2.n + 1 := by omega

      have h_cast : (concatPartition P1 P2).pts i.castSucc = P2.pts ⟨i.val - P1.n, b1⟩ := by
        change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.castSucc.val ≤ P1.n) := by
          have : i.castSucc.val = i.val := rfl
          omega
        rw [dif_neg h_cond]
        congr 1;

      have h_succ : (concatPartition P1 P2).pts i.succ = P2.pts ⟨i.val + 1 - P1.n, b2⟩ := by
        change (if h : i.succ.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.succ.val ≤ P1.n) := by
          have : i.succ.val = i.val + 1 := rfl
          omega
        rw [dif_neg h_cond]
        congr 1;
        -- have : i.succ.val = i.val + 1 := rfl
        -- omega

      rw [h_cast, h_succ]

      -- Map it back to the exact shifted subinterval j in P2
      have bj : i.val - P1.n < P2.n := by omega
      let j : Fin P2.n := ⟨i.val - P1.n, bj⟩

      have eq_succ : (⟨i.val + 1 - P1.n, b2⟩ : Fin (P2.n + 1)) = j.succ := by ext; grind
      have eq_cast : (⟨i.val - P1.n, b1⟩ : Fin (P2.n + 1)) = j.castSucc := by ext; rfl

      rw [eq_succ, eq_cast]

      have H_mesh : P2.pts j.succ - P2.pts j.castSucc ≤ P2.mesh := by
        unfold Partition.mesh
        exact Finset.le_sup' (fun (k : Fin P2.n) => P2.pts k.succ - P2.pts k.castSucc) (Finset.mem_univ j)

      exact le_trans H_mesh (le_max_right _ _)




/-- Lower sums distribute perfectly over concatenated partitions. -/
lemma lowerSum_concat {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) (f α : ℝ → ℝ) :
    lowerSum (concatPartition P1 P2) f α = lowerSum P1 f α + lowerSum P2 f α := by
  let P := concatPartition P1 P2
  unfold lowerSum

  -- Define the generalized summation term on pure natural numbers
  let g : ℕ → ℝ := fun i =>
    if h : i < P.n then
      lowerStep P f ⟨i, h⟩ * (α (P.pts ⟨i + 1, by omega⟩) - α (P.pts ⟨i, by omega⟩))
    else 0

  -- 1. Map the combined sum down to natural numbers
  have h_sumP : ∑ i : Fin P.n, lowerStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc)) =
                ∑ i ∈ Finset.range P.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      dsimp only [g]
      rw [dif_pos i.isLt]
      congr

  -- 2. Split the sum algebraically using Mathlib!
  have hn : P.n = P1.n + P2.n := rfl
  rw [h_sumP, hn, Finset.sum_range_add]

  -- 3. Map the left half back to P1
  have h_left : ∑ i : Fin P1.n, lowerStep P1 f i * (α (P1.pts i.succ) - α (P1.pts i.castSucc)) =
                ∑ i ∈ Finset.range P1.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : i.val < P.n := by change i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]
      -- Prove the points match exactly
      have eq_cast : P.pts ⟨i.val, by omega⟩ = P1.pts i.castSucc := by
        change (if h : i.val ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      have eq_succ : P.pts ⟨i.val + 1, by omega⟩ = P1.pts i.succ := by
        change (if h : i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      -- Prove the subintervals match exactly
      have h_sub : Partition.subinterval P ⟨i.val, hiP⟩ = Partition.subinterval P1 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨i.val, by omega⟩) (P.pts ⟨i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]
      -- Substitute into the step
      have h_step : lowerStep P f ⟨i.val, hiP⟩ = lowerStep P1 f i := by
        unfold lowerStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  -- 4. Map the right half back to P2
  have h_right : ∑ i : Fin P2.n, lowerStep P2 f i * (α (P2.pts i.succ) - α (P2.pts i.castSucc)) =
                 ∑ i ∈ Finset.range P2.n, g (P1.n + i) := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : P1.n + i.val < P.n := by change P1.n + i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]

      -- Carefully prove the left boundary condition matching 'c'
      have eq_cast : P.pts ⟨P1.n + i.val, by omega⟩ = P2.pts i.castSucc := by
        change (if h : P1.n + i.val ≤ P1.n then _ else _) = _
        by_cases h0 : i.val = 0
        · rw [dif_pos (by omega)]
          have e1 : (⟨P1.n + i.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; grind
          have e2 : i.castSucc = 0 := by ext; exact h0
          rw [e1, P1.pts_end, e2, P2.pts_start]
        · rw [dif_neg (by omega)]
          congr 1; ext; grind

      have eq_succ : P.pts ⟨P1.n + i.val + 1, by omega⟩ = P2.pts i.succ := by
        change (if h : P1.n + i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_neg (by omega)]
        congr 1; ext; grind

      have h_sub : Partition.subinterval P ⟨P1.n + i.val, hiP⟩ = Partition.subinterval P2 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨P1.n + i.val, by omega⟩) (P.pts ⟨P1.n + i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]

      have h_step : lowerStep P f ⟨P1.n + i.val, hiP⟩ = lowerStep P2 f i := by
        unfold lowerStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  -- 5. Combine everything!
  rw [← h_left, ← h_right]


/-- Upper sums distribute perfectly over concatenated partitions. -/
lemma upperSum_concat {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) (f α : ℝ → ℝ) :
    upperSum (concatPartition P1 P2) f α = upperSum P1 f α + upperSum P2 f α := by
  let P := concatPartition P1 P2
  unfold upperSum

  let g : ℕ → ℝ := fun i =>
    if h : i < P.n then
      upperStep P f ⟨i, h⟩ * (α (P.pts ⟨i + 1, by omega⟩) - α (P.pts ⟨i, by omega⟩))
    else 0

  have h_sumP : ∑ i : Fin P.n, upperStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc)) =
                ∑ i ∈ Finset.range P.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      dsimp only [g]
      rw [dif_pos i.isLt]
      congr

  have hn : P.n = P1.n + P2.n := rfl
  rw [h_sumP, hn, Finset.sum_range_add]

  have h_left : ∑ i : Fin P1.n, upperStep P1 f i * (α (P1.pts i.succ) - α (P1.pts i.castSucc)) =
                ∑ i ∈ Finset.range P1.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : i.val < P.n := by change i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]
      have eq_cast : P.pts ⟨i.val, by omega⟩ = P1.pts i.castSucc := by
        change (if h : i.val ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      have eq_succ : P.pts ⟨i.val + 1, by omega⟩ = P1.pts i.succ := by
        change (if h : i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      have h_sub : Partition.subinterval P ⟨i.val, hiP⟩ = Partition.subinterval P1 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨i.val, by omega⟩) (P.pts ⟨i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]
      -- Only this line changes to upperStep
      have h_step : upperStep P f ⟨i.val, hiP⟩ = upperStep P1 f i := by
        unfold upperStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  have h_right : ∑ i : Fin P2.n, upperStep P2 f i * (α (P2.pts i.succ) - α (P2.pts i.castSucc)) =
                 ∑ i ∈ Finset.range P2.n, g (P1.n + i) := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : P1.n + i.val < P.n := by change P1.n + i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]
      have eq_cast : P.pts ⟨P1.n + i.val, by omega⟩ = P2.pts i.castSucc := by
        change (if h : P1.n + i.val ≤ P1.n then _ else _) = _
        by_cases h0 : i.val = 0
        · rw [dif_pos (by omega)]
          have e1 : (⟨P1.n + i.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; grind
          have e2 : i.castSucc = 0 := by ext; exact h0
          rw [e1, P1.pts_end, e2, P2.pts_start]
        · rw [dif_neg (by omega)]
          congr 1; ext; grind
      have eq_succ : P.pts ⟨P1.n + i.val + 1, by omega⟩ = P2.pts i.succ := by
        change (if h : P1.n + i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_neg (by omega)]
        congr 1; ext; grind
      have h_sub : Partition.subinterval P ⟨P1.n + i.val, hiP⟩ = Partition.subinterval P2 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨P1.n + i.val, by omega⟩) (P.pts ⟨P1.n + i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]
      -- Only this line changes to upperStep
      have h_step : upperStep P f ⟨P1.n + i.val, hiP⟩ = upperStep P2 f i := by
        unfold upperStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  rw [← h_left, ← h_right]


-----------------------------------------------------------------------------
-- 3. The Cauchy Squeeze Lemma
-----------------------------------------------------------------------------

/--
If `f` is integrable on the whole interval `[a, b]`, then the upper and lower sums
on the subinterval `[a, c]` can be forced arbitrarily close together.
(Proof idea: P = P1 ⊕ P2. Since U(P) - L(P) < ε, and U(P2) - L(P2) ≥ 0,
 it mathematically forces U(P1) - L(P1) < ε).
-/
lemma upper_sub_lower_lt_left {a c b : ℝ} {f α : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta > 0, ∀ P1 : Partition a c, P1.mesh < delta →
      upperSum P1 f α - lowerSum P1 f α < eps := by

  -- 1. Extract the limit properties on the full interval [a, b]
  have h_spec : UpperLowerCommonLimit a b f α (rsIntegral f α a b hab) := rsIntegral_source_spec hab
  rcases h_spec with ⟨hs_ab, hlim⟩

  -- We will need to prove U(P2) - L(P2) ≥ 0, which requires SourceHypotheses on [c, b]
  have hs_cb := sourceHypotheses_right hac hcb hs_ab

  -- Ask for delta corresponding to eps / 2
  have heps2 : 0 < eps / 2 := half_pos heps
  rcases hlim (eps / 2) heps2 with ⟨δ, hδ, H_lim⟩

  -- Obtain a valid, fine partition P2 for the right interval [c, b]
  rcases exists_partition_mesh_lt hcb hδ with ⟨P2, hP2_mesh⟩

  -- Provide delta as our witness for P1
  refine ⟨δ, hδ, ?_⟩
  intro P1 hP1_mesh

  -- 2. Concatenate the partitions
  let P := concatPartition P1 P2
  have hP_mesh : P.mesh < δ := by
    have h_max : max P1.mesh P2.mesh < δ := max_lt hP1_mesh hP2_mesh
    exact lt_of_le_of_lt (concatPartition_mesh P1 P2) h_max

  -- 3. Apply the global convergence bound to the concatenated partition P
  have H_P := H_lim P hP_mesh

  have h_P_bound : upperSum P f α - lowerSum P f α < eps := by
    -- |U(P) - L| < eps/2 and |L(P) - L| < eps/2
    have hU_lt : upperSum P f α - rsIntegral f α a b hab < eps / 2 := (abs_lt.mp H_P.1).2
    have hL_lt : rsIntegral f α a b hab - lowerSum P f α < eps / 2 := by
      have := (abs_lt.mp H_P.2).1
      linarith
    -- Therefore U(P) - L(P) < eps
    linarith

  -- 4. Distribute the sums across P1 and P2
  have h_concat : upperSum P f α - lowerSum P f α =
      (upperSum P1 f α - lowerSum P1 f α) + (upperSum P2 f α - lowerSum P2 f α) := by
    -- Using `change` to unfold `P` into `concatPartition P1 P2` so rewrites trigger
    change upperSum (concatPartition P1 P2) f α - lowerSum (concatPartition P1 P2) f α = _
    rw [upperSum_concat P1 P2 f α, lowerSum_concat P1 P2 f α]
    ring

  -- 5. Prove that the remaining chunk from P2 is non-negative
  have h_P2_nonneg : 0 ≤ upperSum P2 f α - lowerSum P2 f α := by
    have h_le := DarbouxRS.lowerSum_le_upperSum_core P2 hs_cb
    linarith

  -- 6. Conclude algebraically!
  linarith

-----------------------------------------------------------------------------
-- 4. Limits Converging to the Darboux Supremum
-----------------------------------------------------------------------------


/--
Using the Cauchy Squeeze lemma, the upper and lower sums on [a, c]
strictly converge to the Darboux supremum.
-/
lemma upperLowerCommonLimit_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    UpperLowerCommonLimit a c f α (lowerDarboux a c f α) := by
  -- 1. Extract source hypotheses for [a, c]
  have hs_ab : SourceHypotheses a b f α := (rsIntegral_source_spec hab).1
  have hs_ac : SourceHypotheses a c f α := sourceHypotheses_left hac hcb hs_ab

  -- 2. Establish that the set of all lower sums is bounded above
  have h_bdd : BddAbove (lowerSumSet a c f α) := by
    -- We can use ANY partition's upper sum to bound it. We spawn a dummy uniform partition.
    rcases exists_partition_mesh_lt hac zero_lt_one with ⟨P2, _⟩
    use upperSum P2 f α
    rintro y ⟨P1, rfl⟩
    exact lowerSum_le_upperSum_any hs_ac P1 P2

  -- 3. By definition of supremum, L(P) ≤ Darboux for all P
  have h_L_le_Darboux : ∀ P : Partition a c, lowerSum P f α ≤ lowerDarboux a c f α := by
    intro P
    apply le_csSup h_bdd
    exact ⟨P, rfl⟩

  -- 4. Because Darboux is the LEAST upper bound, Darboux ≤ U(P) for all P
  have h_Darboux_le_U : ∀ P : Partition a c, lowerDarboux a c f α ≤ upperSum P f α := by
    intro P
    apply csSup_le
    · -- The set of lower sums is clearly non-empty
      exact ⟨lowerSum P f α, ⟨P, rfl⟩⟩
    · -- Every element in the set is bounded by U(P)
      rintro y ⟨P1, rfl⟩
      exact lowerSum_le_upperSum_any hs_ac P1 P

  -- 5. Prepare the formal limit wrapper
  refine ⟨hs_ac, ?_⟩
  intro eps heps

  -- Ask the Cauchy Squeeze lemma for our delta
  rcases upper_sub_lower_lt_left hac hcb hab eps heps with ⟨δ, hδ, H_sqz⟩
  refine ⟨δ, hδ, ?_⟩

  -- For any partition with mesh < δ
  intro P hP_mesh
  have h_sqz := H_sqz P hP_mesh

  -- 6. Mathematically Squeeze the limits!
  constructor
  · -- Prove |U(P) - Darboux| < eps
    have h1 : 0 ≤ upperSum P f α - lowerDarboux a c f α := sub_nonneg.mpr (h_Darboux_le_U P)
    have h2 : upperSum P f α - lowerDarboux a c f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_left (h_L_le_Darboux P) _
    have h3 : upperSum P f α - lowerDarboux a c f α < eps := lt_of_le_of_lt h2 h_sqz

    -- Absolute value of a non-negative number is itself
    rw [abs_of_nonneg h1]
    exact h3

  · -- Prove |L(P) - Darboux| < eps
    have h1 : 0 ≤ lowerDarboux a c f α - lowerSum P f α := sub_nonneg.mpr (h_L_le_Darboux P)
    have h2 : lowerDarboux a c f α - lowerSum P f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_right (h_Darboux_le_U P) _
    have h3 : lowerDarboux a c f α - lowerSum P f α < eps := lt_of_le_of_lt h2 h_sqz

    have h4 : |lowerDarboux a c f α - lowerSum P f α| < eps := by rwa [abs_of_nonneg h1]
    -- |Darboux - L(P)| is identical to |L(P) - Darboux|
    rw [abs_sub_comm] at h4
    exact h4


-----------------------------------------------------------------------------
-- Helper Lemmas: Tagged Sums are Squeezed by Upper and Lower Sums
-----------------------------------------------------------------------------

lemma tag_le_upperStep {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) (i : Fin P.n) {f : ℝ → ℝ}
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    f (tags i) ≤ upperStep P f i := by
  unfold upperStep
  have h_subset : Partition.subinterval P i ⊆ Set.Icc a b :=
    DarbouxRS.subinterval_subset_Icc_core P

  -- Bulletproof manual image inclusion
  have h_img_subset : f '' Partition.subinterval P i ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  have h_bdd : BddAbove (f '' Partition.subinterval P i) := BddAbove.mono h_img_subset hAbove
  apply le_csSup h_bdd

  -- Bulletproof manual image membership
  exact ⟨tags i, htags i, rfl⟩

lemma lowerStep_le_tag {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) (i : Fin P.n) {f : ℝ → ℝ}
    (hBelow : BddBelow (f '' Set.Icc a b)) :
    lowerStep P f i ≤ f (tags i) := by
  unfold lowerStep
  have h_subset : Partition.subinterval P i ⊆ Set.Icc a b :=
    DarbouxRS.subinterval_subset_Icc_core P

  -- Bulletproof manual image inclusion
  have h_img_subset : f '' Partition.subinterval P i ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  have h_bdd : BddBelow (f '' Partition.subinterval P i) := BddBelow.mono h_img_subset hBelow
  apply csInf_le h_bdd

  -- Bulletproof manual image membership
  exact ⟨tags i, htags i, rfl⟩

lemma taggedSum_le_upperSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) {f α : ℝ → ℝ} (hs : SourceHypotheses a b f α) :
    taggedSum P tags f α ≤ upperSum P f α := by
  -- Extract hAbove without destroying hs
  have hAbove := hs.2.1
  unfold taggedSum upperSum
  apply Finset.sum_le_sum
  intro i _
  have h_step := tag_le_upperStep P tags htags i hAbove
  have h_inc : 0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
    DarbouxRS.partition_increment_nonneg_of_source_core P hs
  exact mul_le_mul_of_nonneg_right h_step h_inc

lemma lowerSum_le_taggedSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) {f α : ℝ → ℝ} (hs : SourceHypotheses a b f α) :
    lowerSum P f α ≤ taggedSum P tags f α := by
  -- Extract hBelow without destroying hs
  have hBelow := hs.2.2.1
  unfold lowerSum taggedSum
  apply Finset.sum_le_sum
  intro i _
  have h_step := lowerStep_le_tag P tags htags i hBelow
  have h_inc : 0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
    DarbouxRS.partition_increment_nonneg_of_source_core P hs
  exact mul_le_mul_of_nonneg_right h_step h_inc

-----------------------------------------------------------------------------
-- The Squeeze Theorem Application
-----------------------------------------------------------------------------

/--
If the Darboux limit exists, the local tagged sums must also converge to it.
-/
lemma taggedCommonLimit_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    TaggedCommonLimit a c f α (lowerDarboux a c f α) := by

  -- 1. Obtain the Darboux convergence we just proved
  have h_ul := upperLowerCommonLimit_left hac hcb hab
  rcases h_ul with ⟨hs_ac, hlim⟩

  -- 2. Prepare the tagged limit wrapper
  refine ⟨hs_ac, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, H_lim⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh

  -- 3. Obtain the Darboux limits and Squeeze bounds for this specific partition
  have h_P := H_lim P hmesh
  have h_upper := taggedSum_le_upperSum P tags htags hs_ac
  have h_lower := lowerSum_le_taggedSum P tags htags hs_ac

  -- 4. Unpack the absolute value gaps:
  -- |U - L| < eps implies U - L < eps
  have hU_lt : upperSum P f α - lowerDarboux a c f α < eps := (abs_lt.mp h_P.1).2

  -- |L - L| < eps implies -eps < L - L
  have hL_gt : -(eps) < lowerSum P f α - lowerDarboux a c f α := (abs_lt.mp h_P.2).1

  -- 5. Squeeze the Tagged sum into the exact same absolute value gap using linarith!
  apply abs_lt.mpr
  constructor
  · linarith
  · linarith

-----------------------------------------------------------------------------
-- 5. Main Existence Theorem
-----------------------------------------------------------------------------

/--
If f is Riemann-Stieltjes integrable on [a, b], it is integrable on [a, c].
-/
theorem rsIntegrable_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α a c := by
  -- The existential witness is satisfied by explicitly packing our `lowerDarboux` value
  -- alongside the two convergence lemmas we isolated above!
  exact ⟨ ⟨
    lowerDarboux a c f α,
    upperLowerCommonLimit_left hac hcb hab,
    taggedCommonLimit_left hac hcb hab
  ⟩ ⟩


-----------------------------------------------------------------------------
-- 6. The Right Subinterval Limits and Existence (Symmetric to Left)
-----------------------------------------------------------------------------

/--
If `f` is integrable on the whole interval `[a, b]`, then the upper and lower sums
on the right subinterval `[c, b]` can be forced arbitrarily close together.
-/
lemma upper_sub_lower_lt_right {a c b : ℝ} {f α : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta > 0, ∀ P2 : Partition c b, P2.mesh < delta →
      upperSum P2 f α - lowerSum P2 f α < eps := by

  have h_spec : UpperLowerCommonLimit a b f α (rsIntegral f α a b hab) := rsIntegral_source_spec hab
  rcases h_spec with ⟨hs_ab, hlim⟩

  -- We need to prove U(P1) - L(P1) ≥ 0, which requires SourceHypotheses on [a, c]
  have hs_ac := sourceHypotheses_left hac hcb hs_ab

  have heps2 : 0 < eps / 2 := half_pos heps
  rcases hlim (eps / 2) heps2 with ⟨δ, hδ, H_lim⟩

  -- Obtain a valid, fine partition P1 for the left interval [a, c]
  rcases exists_partition_mesh_lt hac hδ with ⟨P1, hP1_mesh⟩

  refine ⟨δ, hδ, ?_⟩
  intro P2 hP2_mesh

  let P := concatPartition P1 P2
  have hP_mesh : P.mesh < δ := by
    have h_max : max P1.mesh P2.mesh < δ := max_lt hP1_mesh hP2_mesh
    exact lt_of_le_of_lt (concatPartition_mesh P1 P2) h_max

  have H_P := H_lim P hP_mesh

  have h_P_bound : upperSum P f α - lowerSum P f α < eps := by
    have hU_lt : upperSum P f α - rsIntegral f α a b hab < eps / 2 := (abs_lt.mp H_P.1).2
    have hL_lt : rsIntegral f α a b hab - lowerSum P f α < eps / 2 := by
      have := (abs_lt.mp H_P.2).1
      linarith
    linarith

  have h_concat : upperSum P f α - lowerSum P f α =
      (upperSum P1 f α - lowerSum P1 f α) + (upperSum P2 f α - lowerSum P2 f α) := by
    change upperSum (concatPartition P1 P2) f α - lowerSum (concatPartition P1 P2) f α = _
    rw [upperSum_concat P1 P2 f α, lowerSum_concat P1 P2 f α]
    ring

  -- Prove that the chunk from P1 is non-negative
  have h_P1_nonneg : 0 ≤ upperSum P1 f α - lowerSum P1 f α := by
    have h_le := DarbouxRS.lowerSum_le_upperSum_core P1 hs_ac
    linarith

  linarith

/--
Using the Cauchy Squeeze lemma, the upper and lower sums on [c, b]
strictly converge to the Darboux supremum.
-/
lemma upperLowerCommonLimit_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    UpperLowerCommonLimit c b f α (lowerDarboux c b f α) := by
  have hs_ab : SourceHypotheses a b f α := (rsIntegral_source_spec hab).1
  have hs_cb : SourceHypotheses c b f α := sourceHypotheses_right hac hcb hs_ab

  have h_bdd : BddAbove (lowerSumSet c b f α) := by
    rcases exists_partition_mesh_lt hcb zero_lt_one with ⟨P2, _⟩
    use upperSum P2 f α
    rintro y ⟨P1, rfl⟩
    exact lowerSum_le_upperSum_any hs_cb P1 P2

  have h_L_le_Darboux : ∀ P : Partition c b, lowerSum P f α ≤ lowerDarboux c b f α := by
    intro P
    apply le_csSup h_bdd
    exact ⟨P, rfl⟩

  have h_Darboux_le_U : ∀ P : Partition c b, lowerDarboux c b f α ≤ upperSum P f α := by
    intro P
    apply csSup_le
    · exact ⟨lowerSum P f α, ⟨P, rfl⟩⟩
    · rintro y ⟨P1, rfl⟩
      exact lowerSum_le_upperSum_any hs_cb P1 P

  refine ⟨hs_cb, ?_⟩
  intro eps heps

  rcases upper_sub_lower_lt_right hac hcb hab eps heps with ⟨δ, hδ, H_sqz⟩
  refine ⟨δ, hδ, ?_⟩

  intro P hP_mesh
  have h_sqz := H_sqz P hP_mesh

  constructor
  · have h1 : 0 ≤ upperSum P f α - lowerDarboux c b f α := sub_nonneg.mpr (h_Darboux_le_U P)
    have h2 : upperSum P f α - lowerDarboux c b f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_left (h_L_le_Darboux P) _
    have h3 : upperSum P f α - lowerDarboux c b f α < eps := lt_of_le_of_lt h2 h_sqz
    rw [abs_of_nonneg h1]
    exact h3

  · have h1 : 0 ≤ lowerDarboux c b f α - lowerSum P f α := sub_nonneg.mpr (h_L_le_Darboux P)
    have h2 : lowerDarboux c b f α - lowerSum P f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_right (h_Darboux_le_U P) _
    have h3 : lowerDarboux c b f α - lowerSum P f α < eps := lt_of_le_of_lt h2 h_sqz
    have h4 : |lowerDarboux c b f α - lowerSum P f α| < eps := by rwa [abs_of_nonneg h1]
    rw [abs_sub_comm] at h4
    exact h4

/--
If the Darboux limit exists, the local tagged sums must also converge to it on [c, b].
-/
lemma taggedCommonLimit_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    TaggedCommonLimit c b f α (lowerDarboux c b f α) := by

  have h_ul := upperLowerCommonLimit_right hac hcb hab
  rcases h_ul with ⟨hs_cb, hlim⟩

  refine ⟨hs_cb, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, H_lim⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh

  have h_P := H_lim P hmesh
  have h_upper := taggedSum_le_upperSum P tags htags hs_cb
  have h_lower := lowerSum_le_taggedSum P tags htags hs_cb

  have hU_lt : upperSum P f α - lowerDarboux c b f α < eps := (abs_lt.mp h_P.1).2
  have hL_gt : -(eps) < lowerSum P f α - lowerDarboux c b f α := (abs_lt.mp h_P.2).1

  apply abs_lt.mpr
  constructor
  · linarith
  · linarith

/--
If f is Riemann-Stieltjes integrable on [a, b], it is integrable on [c, b].
-/
theorem rsIntegrable_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α c b := by
  exact ⟨ ⟨
    lowerDarboux c b f α,
    upperLowerCommonLimit_right hac hcb hab,
    taggedCommonLimit_right hac hcb hab
  ⟩ ⟩

end SubintervalIntegrability




/-
The core limit additivity: If the tagged sums converge to L₁ on [a, c]
and to L₂ on [c, b], then their combined partition sums converge to L₁ + L₂
on the whole interval [a, b].
(This requires the partition surgery bound: |S(P) - S(P ∪ {c})| < ε).
-/
-- theorem taggedCommonLimit_split {f α : ℝ → ℝ} {a c b L₁ L₂ : ℝ}
--     (hac : a < c) (hcb : c < b)
--     (h₁ : TaggedCommonLimit a c f α L₁)
--     (h₂ : TaggedCommonLimit c b f α L₂) :
--     TaggedCommonLimit a b f α (L₁ + L₂) := sorry


/-- Combines tags from P1 and P2 into tags for the concatenated partition. -/
def concatTags {a c b : ℝ} {P1 : Partition a c} {P2 : Partition c b}
    (tags1 : Fin P1.n → ℝ) (tags2 : Fin P2.n → ℝ) : Fin (concatPartition P1 P2).n → ℝ :=
  fun i =>
    if h : i.val < P1.n then
      tags1 ⟨i.val, h⟩
    else
      tags2 ⟨i.val - P1.n, by
        -- Explicitly state the bound so omega sees P1.n + P2.n instead of an opaque function call
        have h_bound : i.val < P1.n + P2.n := i.isLt
        omega⟩


/-- The concatenated tags are strictly inside the concatenated subintervals. -/
lemma tagsInPartition_concat {a c b : ℝ} {P1 : Partition a c} {P2 : Partition c b}
    {tags1 : Fin P1.n → ℝ} {tags2 : Fin P2.n → ℝ}
    (ht1 : tagsInPartition P1 tags1) (ht2 : tagsInPartition P2 tags2) :
    tagsInPartition (concatPartition P1 P2) (concatTags tags1 tags2) := by

  intro i
  unfold Partition.subinterval concatTags
  let P := concatPartition P1 P2
  simp
  by_cases h_lt : i.val < P1.n
  · -- Case 1: Inside P1
    have hiP : i.val < P1.n := h_lt
    rw [dif_pos hiP]
    have b1 : i.val < P1.n + 1 := by omega
    have b2 : i.val + 1 < P1.n + 1 := by omega
    have eq_cast : P.pts i.castSucc = P1.pts ⟨i.val, b1⟩ := by
      change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
      have h_cond : i.castSucc.val ≤ P1.n := by have : i.castSucc.val = i.val := rfl; omega
      rw [dif_pos h_cond]; congr 1;
    have eq_succ : P.pts i.succ = P1.pts ⟨i.val + 1, b2⟩ := by
      change (if h : i.succ.val ≤ P1.n then _ else _) = _
      have h_cond : i.succ.val ≤ P1.n := by have : i.succ.val = i.val + 1 := rfl; omega
      rw [dif_pos h_cond]; congr 1;
    rw [eq_cast, eq_succ]
    exact ht1 ⟨i.val, hiP⟩

  · -- Case 2: Inside P2
    have h_ge : P1.n ≤ i.val := by omega
    rw [dif_neg h_lt]
    have hi_lt : i.val < P1.n + P2.n := i.isLt

    -- We MUST branch on the boundary, just like in the mesh proof!
    by_cases h_eq : i.val = P1.n
    · -- Subcase 2a: The boundary interval (touches c)
      have b1 : i.val - P1.n < P2.n := by omega
      have b2 : 1 < P2.n + 1 := by have := P2.hn; omega

      have eq_cast : P.pts i.castSucc = P2.pts ⟨0, by omega⟩ := by
        change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
        -- On the boundary, the castSucc is EXACTLY P1.n, so it uses the first branch!
        have h_cond : i.castSucc.val ≤ P1.n := by have : i.castSucc.val = i.val := rfl; omega
        rw [dif_pos h_cond]
        have e1 : (⟨i.castSucc.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; have : i.castSucc.val = i.val := rfl; grind
        have e2 : (⟨0, by omega⟩ : Fin (P2.n + 1)) = 0 := by ext; rfl
        rw [e1, P1.pts_end, e2, P2.pts_start]

      have eq_succ : P.pts i.succ = P2.pts ⟨1, b2⟩ := by
        change (if h : i.succ.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.succ.val ≤ P1.n) := by have : i.succ.val = i.val + 1 := rfl; omega
        rw [dif_neg h_cond]
        congr 1; ext; have : i.succ.val = i.val + 1 := rfl; grind

      rw [eq_cast, eq_succ]

      -- Map it to the exact tag logic for the first interval of P2
      have h_tag_eq : tags2 ⟨i.val - P1.n, b1⟩ = tags2 ⟨0, P2.hn⟩ := by congr 1; ext; grind
      rw [h_tag_eq]

      have e3 : (⟨0, by omega⟩ : Fin (P2.n + 1)) = (⟨0, P2.hn⟩ : Fin P2.n).castSucc := by ext; rfl
      have e4 : (⟨1, b2⟩ : Fin (P2.n + 1)) = (⟨0, P2.hn⟩ : Fin P2.n).succ := by ext; rfl
      rw [e3, e4]

      exact ht2 ⟨0, P2.hn⟩

    · -- Subcase 2b: Strictly inside P2
      have h_gt : P1.n < i.val := by omega
      have b1 : i.val - P1.n < P2.n + 1 := by omega
      have b2 : i.val + 1 - P1.n < P2.n + 1 := by omega

      have eq_cast : P.pts i.castSucc = P2.pts ⟨i.val - P1.n, b1⟩ := by
        change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
        -- Now it is strictly greater, so it uses the second branch safely!
        have h_cond : ¬(i.castSucc.val ≤ P1.n) := by have : i.castSucc.val = i.val := rfl; omega
        rw [dif_neg h_cond]; congr 1;

      have eq_succ : P.pts i.succ = P2.pts ⟨i.val + 1 - P1.n, b2⟩ := by
        change (if h : i.succ.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.succ.val ≤ P1.n) := by have : i.succ.val = i.val + 1 := rfl; omega
        rw [dif_neg h_cond]; congr 1;

      rw [eq_cast, eq_succ]

      -- Map it back to the exact shifted subinterval j in P2
      have b3 : i.val - P1.n < P2.n := by omega
      let j : Fin P2.n := ⟨i.val - P1.n, b3⟩

      have e1 : (⟨i.val - P1.n, b1⟩ : Fin (P2.n + 1)) = j.castSucc := by ext; rfl
      have e2 : (⟨i.val + 1 - P1.n, b2⟩ : Fin (P2.n + 1)) = j.succ := by ext; dsimp; grind
      rw [e1, e2]

      exact ht2 j


/-- Tagged sums distribute perfectly over concatenated partitions. -/
lemma taggedSum_concat {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b)
    (tags1 : Fin P1.n → ℝ) (tags2 : Fin P2.n → ℝ) (f α : ℝ → ℝ) :
    taggedSum (concatPartition P1 P2) (concatTags tags1 tags2) f α =
    taggedSum P1 tags1 f α + taggedSum P2 tags2 f α := by
  let P := concatPartition P1 P2
  let tags := concatTags tags1 tags2
  unfold taggedSum

  let g : ℕ → ℝ := fun i =>
    if h : i < P.n then
      f (tags ⟨i, h⟩) * (α (P.pts ⟨i + 1, by omega⟩) - α (P.pts ⟨i, by omega⟩))
    else 0

  have h_sumP : ∑ i : Fin P.n, f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) =
                ∑ i ∈ Finset.range P.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      dsimp only [g]
      rw [dif_pos i.isLt]
      congr 1

  have hn : P.n = P1.n + P2.n := rfl
  rw [h_sumP, hn, Finset.sum_range_add]

  have h_left : ∑ i : Fin P1.n, f (tags1 i) * (α (P1.pts i.succ) - α (P1.pts i.castSucc)) =
                ∑ i ∈ Finset.range P1.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : i.val < P.n := by change i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]
      have eq_cast : P.pts ⟨i.val, by omega⟩ = P1.pts i.castSucc := by
        change (if h : i.val ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]; congr 1;
      have eq_succ : P.pts ⟨i.val + 1, by omega⟩ = P1.pts i.succ := by
        change (if h : i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]; congr 1;
      have h_tag : tags ⟨i.val, hiP⟩ = tags1 i := by
        unfold tags concatTags
        dsimp only
        rw [dif_pos i.isLt]

      rw [h_tag, eq_succ, eq_cast]

  have h_right : ∑ i : Fin P2.n, f (tags2 i) * (α (P2.pts i.succ) - α (P2.pts i.castSucc)) =
                 ∑ i ∈ Finset.range P2.n, g (P1.n + i) := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : P1.n + i.val < P.n := by change P1.n + i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]

      have eq_cast : P.pts ⟨P1.n + i.val, by omega⟩ = P2.pts i.castSucc := by
        change (if h : P1.n + i.val ≤ P1.n then _ else _) = _
        by_cases h0 : i.val = 0
        · rw [dif_pos (by omega)]
          have e1 : (⟨P1.n + i.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; grind
          have e2 : i.castSucc = 0 := by ext; exact h0
          rw [e1, P1.pts_end, e2, P2.pts_start]
        · rw [dif_neg (by omega)]
          congr 1; ext; grind

      have eq_succ : P.pts ⟨P1.n + i.val + 1, by omega⟩ = P2.pts i.succ := by
        change (if h : P1.n + i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_neg (by omega)]
        congr 1; ext; grind

      have h_tag : tags ⟨P1.n + i.val, hiP⟩ = tags2 i := by
        unfold tags concatTags
        dsimp only
        have h_nle : ¬(P1.n + i.val < P1.n) := by omega
        rw [dif_neg h_nle]
        congr 1; ext; grind

      rw [h_tag, eq_succ, eq_cast]

  rw [← h_left, ← h_right]


-----------------------------------------------------------------------------
--  The Main Theorem: Integral Splitting
-----------------------------------------------------------------------------

/--
Additivity of the Riemann-Stieltjes integral over adjacent intervals.
If f is integrable on [a, b], and a < c < b, then
  ∫_a^b f dα = ∫_a^c f dα + ∫_c^b f dα.
-/
theorem rsIntegral_split {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b)
    (hab : RSIntegrable f α a b) :
    rsIntegral f α a b hab =
      rsIntegral f α a c (rsIntegrable_left hac hcb hab) +
      rsIntegral f α c b (rsIntegrable_right hac hcb hab) := by

  -- 1. Extract the limits
  have hL := rsIntegral_spec hab
  have hL1 := rsIntegral_spec (rsIntegrable_left hac hcb hab)
  have hL2 := rsIntegral_spec (rsIntegrable_right hac hcb hab)

  let L := rsIntegral f α a b hab
  let L1 := rsIntegral f α a c (rsIntegrable_left hac hcb hab)
  let L2 := rsIntegral f α c b (rsIntegrable_right hac hcb hab)

  -- 2. Prove equality via an epsilon distance bound
  apply eq_of_forall_dist_le
  intro eps heps
  have heps3 : 0 < eps / 3 := by linarith

  -- Request delta for eps/3 for all three limits
  rcases hL.2 (eps / 3) heps3 with ⟨δ, hδ, H⟩
  rcases hL1.2 (eps / 3) heps3 with ⟨δ1, hδ1, H1⟩
  rcases hL2.2 (eps / 3) heps3 with ⟨δ2, hδ2, H2⟩

  -- Take the tightest delta
  let δ_star := min δ (min δ1 δ2)
  have hδ_star : 0 < δ_star := lt_min hδ (lt_min hδ1 hδ2)

  -- Conjure partitions matching the tight delta
  rcases exists_partition_mesh_lt hac hδ_star with ⟨P1, hP1_mesh⟩
  rcases exists_partition_mesh_lt hcb hδ_star with ⟨P2, hP2_mesh⟩

  -- Conjure their respective tags (we just use the left endpoints)
  let tags1 : Fin P1.n → ℝ := fun i => P1.pts i.castSucc
  have ht1 : tagsInPartition P1 tags1 := leftTagsInPartition P1

  let tags2 : Fin P2.n → ℝ := fun i => P2.pts i.castSucc
  have ht2 : tagsInPartition P2 tags2 := leftTagsInPartition P2

  -- 3. Construct the perfectly joined partition P
  let P := concatPartition P1 P2
  let tags := concatTags tags1 tags2
  have ht : tagsInPartition P tags := tagsInPartition_concat ht1 ht2

  have hP_mesh : P.mesh < δ := by
    have h_max : max P1.mesh P2.mesh < δ_star := max_lt hP1_mesh hP2_mesh
    have h_le : δ_star ≤ δ := min_le_left _ _
    exact lt_of_le_of_lt (concatPartition_mesh P1 P2) (lt_of_lt_of_le h_max h_le)

  have hP1_mesh_real : P1.mesh < δ1 := lt_of_lt_of_le hP1_mesh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hP2_mesh_real : P2.mesh < δ2 := lt_of_lt_of_le hP2_mesh (le_trans (min_le_right _ _) (min_le_right _ _))

  -- 4. Evaluate the bounds
  have h_val := H P tags ht hP_mesh
  have h_val1 := H1 P1 tags1 ht1 hP1_mesh_real
  have h_val2 := H2 P2 tags2 ht2 hP2_mesh_real

  -- S(P) = S(P1) + S(P2)
  have h_sum : taggedSum P tags f α = taggedSum P1 tags1 f α + taggedSum P2 tags2 f α :=
    taggedSum_concat P1 P2 tags1 tags2 f α

  -- 5. A 3-epsilon Triangle Inequality Squeeze
  have h_decomp : L - (L1 + L2) =
      -(taggedSum P tags f α - L) + (taggedSum P1 tags1 f α - L1) + (taggedSum P2 tags2 f α - L2) := by
    rw [h_sum]
    ring

  -- Pre-prove the triangle inequalities using `abs_add`
  have h_tri1 : |-(taggedSum P tags f α - L) + (taggedSum P1 tags1 f α - L1) + (taggedSum P2 tags2 f α - L2)| ≤
      |-(taggedSum P tags f α - L) + (taggedSum P1 tags1 f α - L1)| + |taggedSum P2 tags2 f α - L2| := abs_add_le _ _

  have h_tri2 : |-(taggedSum P tags f α - L) + (taggedSum P1 tags1 f α - L1)| ≤
      |-(taggedSum P tags f α - L)| + |taggedSum P1 tags1 f α - L1| := abs_add_le _ _

  have h_abs_bound : |L - (L1 + L2)| < eps := by
    calc |L - (L1 + L2)|
      _ = |-(taggedSum P tags f α - L) + (taggedSum P1 tags1 f α - L1) + (taggedSum P2 tags2 f α - L2)| := by rw [h_decomp]
      _ ≤ |-(taggedSum P tags f α - L) + (taggedSum P1 tags1 f α - L1)| + |taggedSum P2 tags2 f α - L2| := h_tri1
      _ ≤ |-(taggedSum P tags f α - L)| + |taggedSum P1 tags1 f α - L1| + |taggedSum P2 tags2 f α - L2| := by linarith
      _ = |taggedSum P tags f α - L| + |taggedSum P1 tags1 f α - L1| + |taggedSum P2 tags2 f α - L2| := by rw [abs_neg]
      _ < eps / 3 + eps / 3 + eps / 3 := by linarith
      _ = eps := by ring

  -- `dist` on real numbers is definitionally identical to the absolute difference
  -- We just apply `le_of_lt` to convert `< eps` to `≤ eps`!
  exact le_of_lt h_abs_bound



end Thm_1_2_4

end Thm_1_2_4
