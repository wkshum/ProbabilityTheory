import Mathlib
import ToyApollo.Output.def_1_2

/-
TASK ID: thm_1_2
TYPE: Theorem_Statement
SOURCE PLAN: 38_chap1_riemann_stieltjes
TASK CONTENT:
\begin{thmbox}{1.2}
\begin{enumerate}[label=\arabic*.]
    \item If $f\in \mathcal{R}(\alpha)$ and $g\in \mathcal{R}(\alpha)$, then $f+g\in \mathcal{R}(\alpha)$ and
    \[
    \int_a^b f+g\, d\alpha = \int_a^b f\, d\alpha + \int_a^b g\, d\alpha.
    \]
    \item If $f\in \mathcal{R}(\alpha)$, then $cf\in \mathcal{R}(\alpha)$ for any constant $c$ and
    \[
    \int_a^b cf\, d\alpha = c\int_a^b f\, d\alpha.
    \]
    \item If $f,g\in \mathcal{R}(\alpha)$ and $f(x)\le g(x)$ for all $x\in [a,b]$, then
    \[
    \int_a^b f\, d\alpha \le \int_a^b g\, d\alpha.
    \]
    \item Suppose $a<c<b$. If $f\in \mathcal{R}(\alpha)$ on $[a,c]$ and $f\in \mathcal{R}(\alpha)$ on $[c,b]$, then $f$ is RS-integrable on $[a,b]$, and
    \[
    \int_a^b f\, d\alpha = \int_a^c f\, d\alpha + \int_c^b f\, d\alpha.
    \]
\end{enumerate}
\end{thmbox}
These properties are all analogous to the properties of Riemann integrals, and hence, the proofs are omitted. The following property concerns the effect of changing the function $\alpha(x)$ on the Riemann--Stieltjes integral.
-/

-- WRITE FINAL LEAN CODE BELOW

open Set

noncomputable section

namespace Thm12Item4

open DarbouxRS

/-! ## Split a partition at an existing grid point `c = P.pts k`, `0 < k < P.n`. -/

/-- Left piece of a partition split at grid index `k`. -/
def splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k) (hkn : k ≤ P.n)
    (c : ℝ) (hc : P.pts k = c) : Partition a c where
  n := k
  hn := hk0
  pts := P.pts
  pts_start := P.pts_start
  pts_end := hc
  strict_mono := by
    intro i hi
    exact P.strict_mono i (lt_of_lt_of_le hi hkn)

/-- Right piece of a partition split at grid index `k`. -/
def splitRight {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc : P.pts k = c) : Partition c b where
  n := P.n - k
  hn := Nat.sub_pos_of_lt hkn
  pts := fun j => P.pts (k + j)
  pts_start := by simpa using hc
  pts_end := by
    have hkk : k + (P.n - k) = P.n := by omega
    rw [hkk]; exact P.pts_end
  strict_mono := by
    intro j hj
    have hlt : k + j < P.n := by omega
    have hsm := P.strict_mono (k + j) hlt
    have : k + (j + 1) = (k + j) + 1 := by omega
    rw [this]
    exact hsm

/-- Per-cell step equality: the left piece reuses `P`'s cells verbatim. -/
lemma upperStep_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k ≤ P.n) (c : ℝ) (hc : P.pts k = c) (f : ℝ → ℝ) {i : ℕ} :
    upperStep (splitLeft P k hk0 hkn c hc) f i = upperStep P f i := rfl

lemma lowerStep_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k ≤ P.n) (c : ℝ) (hc : P.pts k = c) (f : ℝ → ℝ) {i : ℕ} :
    lowerStep (splitLeft P k hk0 hkn c hc) f i = lowerStep P f i := rfl

lemma upperStep_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc : P.pts k = c) (f : ℝ → ℝ) {j : ℕ} :
    upperStep (splitRight P k hkn c hc) f j = upperStep P f (k + j) := rfl

lemma lowerStep_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc : P.pts k = c) (f : ℝ → ℝ) {j : ℕ} :
    lowerStep (splitRight P k hkn c hc) f j = lowerStep P f (k + j) := rfl

/-! ### Additivity of the sums across a grid-point split. -/

lemma upperSum_split {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ) (hc : P.pts k = c) (f α : ℝ → ℝ) :
    upperSum P f α =
      upperSum (splitLeft P k hk0 (le_of_lt hkn) c hc) f α +
        upperSum (splitRight P k hkn c hc) f α := by
  have hsplit : k + (P.n - k) = P.n := by omega
  unfold upperSum
  conv_lhs => rw [← hsplit, Finset.sum_range_add]
  rfl

lemma lowerSum_split {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ) (hc : P.pts k = c) (f α : ℝ → ℝ) :
    lowerSum P f α =
      lowerSum (splitLeft P k hk0 (le_of_lt hkn) c hc) f α +
        lowerSum (splitRight P k hkn c hc) f α := by
  have hsplit : k + (P.n - k) = P.n := by omega
  unfold lowerSum
  conv_lhs => rw [← hsplit, Finset.sum_range_add]
  rfl

lemma taggedSum_split {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ) (hc : P.pts k = c) (tags : ℕ → ℝ) (f α : ℝ → ℝ) :
    taggedSum P tags f α =
      taggedSum (splitLeft P k hk0 (le_of_lt hkn) c hc) tags f α +
        taggedSum (splitRight P k hkn c hc) (fun j => tags (k + j)) f α := by
  have hsplit : k + (P.n - k) = P.n := by omega
  unfold taggedSum
  conv_lhs => rw [← hsplit, Finset.sum_range_add]
  rfl

/-! ### Mesh monotonicity: each split piece has mesh ≤ mesh P. -/

lemma partition_length_le_mesh {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    P.pts (i + 1) - P.pts i ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup' (s := Finset.range P.n)
    (f := fun j => P.pts (j + 1) - P.pts j) (Finset.mem_range.mpr hi)

lemma mesh_splitLeft_le {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ) (hc : P.pts k = c) :
    (splitLeft P k hk0 (le_of_lt hkn) c hc).mesh ≤ P.mesh := by
  unfold Partition.mesh
  apply Finset.sup'_le
  intro i hi
  have hi' : i < k := Finset.mem_range.mp hi
  have : i < P.n := lt_trans hi' hkn
  exact partition_length_le_mesh P this

lemma mesh_splitRight_le {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ) (hc : P.pts k = c) :
    (splitRight P k hkn c hc).mesh ≤ P.mesh := by
  unfold Partition.mesh
  apply Finset.sup'_le
  intro j hj
  have hj' : j < P.n - k := Finset.mem_range.mp hj
  have hlt : k + j < P.n := by omega
  have hstep : P.pts (k + j + 1) - P.pts (k + j) ≤ P.mesh :=
    partition_length_le_mesh P hlt
  -- goal: (splitRight ...).pts (j+1) - (splitRight ...).pts j ≤ P.mesh
  show P.pts (k + (j + 1)) - P.pts (k + j) ≤ P.mesh
  have : k + (j + 1) = k + j + 1 := by omega
  rw [this]
  exact hstep

/-! ## Tag transport across an insertion (seam sub-cells both get tag `d`). -/

/-- Transported tags: seam sub-cells both get tag `d` (which lies in both). -/
def insTags (tags : ℕ → ℝ) (k : ℕ) (d : ℝ) : ℕ → ℝ :=
  fun j => if j < k then tags j else if j ≤ k + 1 then d else tags (j - 1)

lemma insTags_lt (tags : ℕ → ℝ) (k : ℕ) (d : ℝ) {j : ℕ} (hj : j < k) :
    insTags tags k d j = tags j := by simp [insTags, hj]

lemma insTags_seamL (tags : ℕ → ℝ) (k : ℕ) (d : ℝ) :
    insTags tags k d k = d := by simp [insTags]

lemma insTags_seamR (tags : ℕ → ℝ) (k : ℕ) (d : ℝ) :
    insTags tags k d (k + 1) = d := by simp [insTags]

lemma insTags_gt (tags : ℕ → ℝ) (k : ℕ) (d : ℝ) {j : ℕ} (hj : k + 1 < j) :
    insTags tags k d j = tags (j - 1) := by
  have h1 : ¬ j < k := by omega
  have h2 : ¬ j ≤ k + 1 := by omega
  simp [insTags, h1, h2]

/-! ### Tag restriction across a grid-point split. -/

lemma tagsInPartition_splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ) (hk0 : 0 < k)
    (hkn : k < P.n) (c : ℝ) (hc : P.pts k = c) (tags : ℕ → ℝ)
    (htags : tagsInPartition P tags) :
    tagsInPartition (splitLeft P k hk0 (le_of_lt hkn) c hc) tags := by
  intro i hi
  have hi' : i < k := hi
  exact htags i (lt_trans hi' hkn)

lemma tagsInPartition_splitRight {a b : ℝ} (P : Partition a b) (k : ℕ)
    (hkn : k < P.n) (c : ℝ) (hc : P.pts k = c) (tags : ℕ → ℝ)
    (htags : tagsInPartition P tags) :
    tagsInPartition (splitRight P k hkn c hc) (fun j => tags (k + j)) := by
  intro j hj
  have hj' : j < P.n - k := hj
  have hlt : k + j < P.n := by omega
  have := htags (k + j) hlt
  -- subinterval (splitRight) j = subinterval P (k+j) definitionally
  exact this

/-! ## Insert a new grid point `c` strictly inside cell `k` of `P`. -/

/-- The point function of the inserted partition. -/
def insPts {a b : ℝ} (P : Partition a b) (k : ℕ) (c : ℝ) : ℕ → ℝ :=
  fun j => if j ≤ k then P.pts j else if j = k + 1 then c else P.pts (j - 1)

lemma insPts_le {a b : ℝ} (P : Partition a b) (k : ℕ) (c : ℝ) {j : ℕ} (hj : j ≤ k) :
    insPts P k c j = P.pts j := by
  simp [insPts, hj]

lemma insPts_seam {a b : ℝ} (P : Partition a b) (k : ℕ) (c : ℝ) :
    insPts P k c (k + 1) = c := by
  simp [insPts]

lemma insPts_gt {a b : ℝ} (P : Partition a b) (k : ℕ) (c : ℝ) {j : ℕ}
    (hj : k + 1 < j) :
    insPts P k c j = P.pts (j - 1) := by
  have h1 : ¬ j ≤ k := by omega
  have h2 : j ≠ k + 1 := by omega
  simp [insPts, h1, h2]

/-- The partition with `c` inserted after index `k`. -/
def insertPoint {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc1 : P.pts k < c) (hc2 : c < P.pts (k + 1)) : Partition a b where
  n := P.n + 1
  hn := by omega
  pts := insPts P k c
  pts_start := by rw [insPts_le P k c (Nat.zero_le k)]; exact P.pts_start
  pts_end := by
    rw [insPts_gt P k c (by omega)]
    simp only [Nat.add_sub_cancel]
    exact P.pts_end
  strict_mono := by
    intro j hj
    rcases lt_trichotomy j k with hlt | heq | hgt
    · -- j < k : both are P points
      rw [insPts_le P k c (le_of_lt hlt), insPts_le P k c (by omega)]
      exact P.strict_mono j (lt_trans hlt hkn)
    · -- j = k : P.pts k < c
      subst heq
      rw [insPts_le P j c (le_refl j), insPts_seam]
      exact hc1
    · -- j > k
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · omega
      · rcases Nat.eq_or_lt_of_le h with heq1 | hgt1
        · -- j = k + 1 : c < P.pts (k+1)
          rw [← heq1, insPts_seam, insPts_gt P k c (by omega)]
          have hsimp : k + 1 + 1 - 1 = k + 1 := by omega
          rw [hsimp]
          exact hc2
        · -- j ≥ k + 2 : both are shifted P points
          rw [insPts_gt P k c hgt1, insPts_gt P k c (by omega)]
          have hjn : j - 1 < P.n := by omega
          have hsm := P.strict_mono (j - 1) hjn
          have he : (j + 1) - 1 = (j - 1) + 1 := by omega
          rw [he]
          exact hsm

/-! ### `c` is a grid point of the inserted partition. -/

lemma insertPoint_pts_eq {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc1 : P.pts k < c) (hc2 : c < P.pts (k + 1)) :
    (insertPoint P k hkn c hc1 hc2).pts = insPts P k c := rfl

lemma insertPoint_pts_seam {a b : ℝ} (P : Partition a b) (k : ℕ) (hkn : k < P.n)
    (c : ℝ) (hc1 : P.pts k < c) (hc2 : c < P.pts (k + 1)) :
    (insertPoint P k hkn c hc1 hc2).pts (k + 1) = c := insPts_seam P k c

/-! ### A generic sum comparison across a single-point insertion.

For any real families `u` (the `P`-cell contributions) and split values `uL, uR`
at the seam cell `k`, if the `P'`-contributions agree with `u` away from the seam
and split into `uL, uR` there, the sums differ only by `u k - (uL + uR)`. -/
lemma sum_insert_diff (n k : ℕ) (hk : k < n)
    (u u' : ℕ → ℝ) (uL uR : ℝ)
    (hlt : ∀ i, i < k → u' i = u i)
    (hkL : u' k = uL)
    (hkR : u' (k + 1) = uR)
    (hgt : ∀ j, u' (k + 1 + (j + 1)) = u (k + (j + 1))) :
    ∑ i ∈ Finset.range n, u i =
      (∑ i ∈ Finset.range (n + 1), u' i) - (uL + uR) + u k := by
  -- Split range n at k: [0,k) ++ {k+j : j < n-k}
  have hsplitn : k + (n - k) = n := by omega
  have hnk : n - k = (n - k - 1) + 1 := by omega
  -- LHS
  have hLHS : ∑ i ∈ Finset.range n, u i
      = (∑ i ∈ Finset.range k, u i)
        + ∑ j ∈ Finset.range (n - k), u (k + j) := by
    conv_lhs => rw [← hsplitn, Finset.sum_range_add]
  -- RHS sum over range (n+1): split at k+1 into [0,k+1) ++ shifted
  have hsplitn1 : (k + 1) + (n - k) = n + 1 := by omega
  have hRHS : ∑ i ∈ Finset.range (n + 1), u' i
      = (∑ i ∈ Finset.range (k + 1), u' i)
        + ∑ j ∈ Finset.range (n - k), u' (k + 1 + j) := by
    conv_lhs => rw [← hsplitn1, Finset.sum_range_add]
  -- Decompose the u-tail: peel index 0.
  have hUtail : ∑ j ∈ Finset.range (n - k), u (k + j)
      = (∑ j ∈ Finset.range (n - k - 1), u (k + (j + 1))) + u k := by
    rw [hnk, Finset.sum_range_succ']
    simp
  -- Decompose the u'-left block range (k+1): peel last index k.
  have hU'left : ∑ i ∈ Finset.range (k + 1), u' i
      = (∑ i ∈ Finset.range k, u' i) + u' k :=
    Finset.sum_range_succ (fun i => u' i) k
  -- Decompose the u'-tail: peel index 0.
  have hU'tail : ∑ j ∈ Finset.range (n - k), u' (k + 1 + j)
      = (∑ j ∈ Finset.range (n - k - 1), u' (k + 1 + (j + 1))) + u' (k + 1) := by
    rw [hnk, Finset.sum_range_succ']
    simp
  -- Termwise equalities.
  have hleft : ∑ i ∈ Finset.range k, u' i = ∑ i ∈ Finset.range k, u i :=
    Finset.sum_congr rfl (fun i hi => hlt i (Finset.mem_range.mp hi))
  have htail : ∑ j ∈ Finset.range (n - k - 1), u' (k + 1 + (j + 1))
      = ∑ j ∈ Finset.range (n - k - 1), u (k + (j + 1)) :=
    Finset.sum_congr rfl (fun j _ => hgt j)
  rw [hLHS, hRHS, hUtail, hU'left, hU'tail, hleft, htail, hkL, hkR]
  ring

/-! ### Cell identities between `P` and `P' = insertPoint P k ...`. -/

variable {a b : ℝ}

section InsertCells
variable (P : Partition a b) (k : ℕ) (hkn : k < P.n)
  (c : ℝ) (hc1 : P.pts k < c) (hc2 : c < P.pts (k + 1))

/-- Away-from-seam cells (index `< k`) coincide. -/
lemma insert_subinterval_lt {i : ℕ} (hi : i < k) :
    subinterval (insertPoint P k hkn c hc1 hc2) i = subinterval P i := by
  unfold subinterval
  simp only [insertPoint_pts_eq]
  rw [insPts_le P k c (le_of_lt hi), insPts_le P k c (by omega : i + 1 ≤ k)]

/-- Seam left sub-cell is `[P.pts k, c]`. -/
lemma insert_subinterval_seamL :
    subinterval (insertPoint P k hkn c hc1 hc2) k = Icc (P.pts k) c := by
  unfold subinterval
  simp only [insertPoint_pts_eq]
  rw [insPts_le P k c (le_refl k), insPts_seam P k c]

/-- Seam right sub-cell is `[c, P.pts (k+1)]`. -/
lemma insert_subinterval_seamR :
    subinterval (insertPoint P k hkn c hc1 hc2) (k + 1) = Icc c (P.pts (k + 1)) := by
  unfold subinterval
  simp only [insertPoint_pts_eq]
  rw [insPts_seam P k c, insPts_gt P k c (by omega : k + 1 < k + 1 + 1)]
  rw [show k + 1 + 1 - 1 = k + 1 from by omega]

/-- Shifted cells (index `≥ k+2`) coincide with `P`'s cells (index `≥ k+1`). -/
lemma insert_subinterval_gt (j : ℕ) :
    subinterval (insertPoint P k hkn c hc1 hc2) (k + 1 + (j + 1))
      = subinterval P (k + (j + 1)) := by
  unfold subinterval
  simp only [insertPoint_pts_eq]
  rw [insPts_gt P k c (by omega : k + 1 < k + 1 + (j + 1)),
     insPts_gt P k c (by omega : k + 1 < k + 1 + (j + 1) + 1)]
  congr 1
  · congr 1; omega
  · congr 1; omega

/-- Step equalities from the cell identities. -/
lemma insert_upperStep_lt (f : ℝ → ℝ) {i : ℕ} (hi : i < k) :
    upperStep (insertPoint P k hkn c hc1 hc2) f i = upperStep P f i := by
  unfold upperStep; rw [insert_subinterval_lt P k hkn c hc1 hc2 hi]

lemma insert_lowerStep_lt (f : ℝ → ℝ) {i : ℕ} (hi : i < k) :
    lowerStep (insertPoint P k hkn c hc1 hc2) f i = lowerStep P f i := by
  unfold lowerStep; rw [insert_subinterval_lt P k hkn c hc1 hc2 hi]

lemma insert_upperStep_gt (f : ℝ → ℝ) (j : ℕ) :
    upperStep (insertPoint P k hkn c hc1 hc2) f (k + 1 + (j + 1))
      = upperStep P f (k + (j + 1)) := by
  unfold upperStep; rw [insert_subinterval_gt P k hkn c hc1 hc2 j]

lemma insert_lowerStep_gt (f : ℝ → ℝ) (j : ℕ) :
    lowerStep (insertPoint P k hkn c hc1 hc2) f (k + 1 + (j + 1))
      = lowerStep P f (k + (j + 1)) := by
  unfold lowerStep; rw [insert_subinterval_gt P k hkn c hc1 hc2 j]

/-- `pts` values needed for the α-increments. -/
lemma insert_pts_lt {i : ℕ} (hi : i ≤ k) :
    (insertPoint P k hkn c hc1 hc2).pts i = P.pts i := by
  simp only [insertPoint_pts_eq]; exact insPts_le P k c hi

lemma insert_pts_ge (j : ℕ) :
    (insertPoint P k hkn c hc1 hc2).pts (k + 1 + (j + 1)) = P.pts (k + (j + 1)) := by
  simp only [insertPoint_pts_eq]
  rw [insPts_gt P k c (by omega : k + 1 < k + 1 + (j + 1))]
  congr 1; omega

/-! ### The upper/lower sum change identity across an insertion. -/

lemma upperSum_insert_eq (f α : ℝ → ℝ) :
    upperSum P f α =
      upperSum (insertPoint P k hkn c hc1 hc2) f α
        - (upperStep (insertPoint P k hkn c hc1 hc2) f k * (α c - α (P.pts k))
            + upperStep (insertPoint P k hkn c hc1 hc2) f (k + 1)
              * (α (P.pts (k + 1)) - α c))
        + upperStep P f k * (α (P.pts (k + 1)) - α (P.pts k)) := by
  have key := sum_insert_diff P.n k hkn
    (fun i => upperStep P f i * (α (P.pts (i + 1)) - α (P.pts i)))
    (fun i => upperStep (insertPoint P k hkn c hc1 hc2) f i
      * (α ((insertPoint P k hkn c hc1 hc2).pts (i + 1))
          - α ((insertPoint P k hkn c hc1 hc2).pts i)))
    (upperStep (insertPoint P k hkn c hc1 hc2) f k * (α c - α (P.pts k)))
    (upperStep (insertPoint P k hkn c hc1 hc2) f (k + 1) * (α (P.pts (k + 1)) - α c))
    ?hlt ?hkL ?hkR ?hgt
  · simpa [upperSum] using key
  case hlt =>
    intro i hi
    simp only []
    rw [insert_upperStep_lt P k hkn c hc1 hc2 f hi,
       insert_pts_lt P k hkn c hc1 hc2 (by omega : i + 1 ≤ k),
       insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hi)]
  case hkL =>
    simp only []
    rw [insert_pts_lt P k hkn c hc1 hc2 (le_refl k),
       insertPoint_pts_seam P k hkn c hc1 hc2]
  case hkR =>
    simp only []
    rw [insertPoint_pts_seam P k hkn c hc1 hc2,
       show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + 1) = P.pts (k + 1) from by
         have := insert_pts_ge P k hkn c hc1 hc2 0
         simpa using this]
  case hgt =>
    intro j
    simp only []
    rw [insert_upperStep_gt P k hkn c hc1 hc2 f j,
       insert_pts_ge P k hkn c hc1 hc2 j,
       show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + (j + 1) + 1)
           = P.pts (k + (j + 1) + 1) from by
         have := insert_pts_ge P k hkn c hc1 hc2 (j + 1)
         rw [show k + 1 + (j + 1 + 1) = k + 1 + (j + 1) + 1 from by omega,
            show k + (j + 1 + 1) = k + (j + 1) + 1 from by omega] at this
         exact this]

lemma lowerSum_insert_eq (f α : ℝ → ℝ) :
    lowerSum P f α =
      lowerSum (insertPoint P k hkn c hc1 hc2) f α
        - (lowerStep (insertPoint P k hkn c hc1 hc2) f k * (α c - α (P.pts k))
            + lowerStep (insertPoint P k hkn c hc1 hc2) f (k + 1)
              * (α (P.pts (k + 1)) - α c))
        + lowerStep P f k * (α (P.pts (k + 1)) - α (P.pts k)) := by
  have key := sum_insert_diff P.n k hkn
    (fun i => lowerStep P f i * (α (P.pts (i + 1)) - α (P.pts i)))
    (fun i => lowerStep (insertPoint P k hkn c hc1 hc2) f i
      * (α ((insertPoint P k hkn c hc1 hc2).pts (i + 1))
          - α ((insertPoint P k hkn c hc1 hc2).pts i)))
    (lowerStep (insertPoint P k hkn c hc1 hc2) f k * (α c - α (P.pts k)))
    (lowerStep (insertPoint P k hkn c hc1 hc2) f (k + 1) * (α (P.pts (k + 1)) - α c))
    ?hlt ?hkL ?hkR ?hgt
  · simpa [lowerSum] using key
  case hlt =>
    intro i hi
    simp only []
    rw [insert_lowerStep_lt P k hkn c hc1 hc2 f hi,
       insert_pts_lt P k hkn c hc1 hc2 (by omega : i + 1 ≤ k),
       insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hi)]
  case hkL =>
    simp only []
    rw [insert_pts_lt P k hkn c hc1 hc2 (le_refl k),
       insertPoint_pts_seam P k hkn c hc1 hc2]
  case hkR =>
    simp only []
    rw [insertPoint_pts_seam P k hkn c hc1 hc2,
       show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + 1) = P.pts (k + 1) from by
         have := insert_pts_ge P k hkn c hc1 hc2 0
         simpa using this]
  case hgt =>
    intro j
    simp only []
    rw [insert_lowerStep_gt P k hkn c hc1 hc2 f j,
       insert_pts_ge P k hkn c hc1 hc2 j,
       show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + (j + 1) + 1)
           = P.pts (k + (j + 1) + 1) from by
         have := insert_pts_ge P k hkn c hc1 hc2 (j + 1)
         rw [show k + 1 + (j + 1 + 1) = k + 1 + (j + 1) + 1 from by omega,
            show k + (j + 1 + 1) = k + (j + 1) + 1 from by omega] at this
         exact this]

/-! ### Sub-cell membership: the seam sub-cell steps lie in `[m_k, M_k]`. -/

/-- The left seam sub-cell of `P'` is contained in cell `k` of `P`. -/
lemma insert_seamL_subset :
    subinterval (insertPoint P k hkn c hc1 hc2) k ⊆ subinterval P k := by
  rw [insert_subinterval_seamL P k hkn c hc1 hc2]
  intro x hx
  exact ⟨hx.1, le_trans hx.2 (le_of_lt hc2)⟩

lemma insert_seamR_subset :
    subinterval (insertPoint P k hkn c hc1 hc2) (k + 1) ⊆ subinterval P k := by
  rw [insert_subinterval_seamR P k hkn c hc1 hc2]
  intro x hx
  exact ⟨le_trans (le_of_lt hc1) hx.1, hx.2⟩

include hkn in
lemma cell_bddAbove (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    BddAbove (f '' subinterval P k) :=
  BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P hkn)) hAbove

include hkn in
lemma cell_bddBelow (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    BddBelow (f '' subinterval P k) :=
  BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P hkn)) hBelow

/-- Seam sub-cell upper steps are `≤ M_k`. -/
lemma seam_upperStep_le_L (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    upperStep (insertPoint P k hkn c hc1 hc2) f k ≤ upperStep P f k := by
  unfold upperStep
  refine csSup_le_csSup (cell_bddAbove P k hkn f hAbove) ?_
    (Set.image_mono (insert_seamL_subset P k hkn c hc1 hc2))
  refine ⟨f (P.pts k), P.pts k, ?_, rfl⟩
  rw [insert_subinterval_seamL P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc1⟩

lemma seam_upperStep_le_R (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    upperStep (insertPoint P k hkn c hc1 hc2) f (k + 1) ≤ upperStep P f k := by
  unfold upperStep
  refine csSup_le_csSup (cell_bddAbove P k hkn f hAbove) ?_
    (Set.image_mono (insert_seamR_subset P k hkn c hc1 hc2))
  refine ⟨f c, c, ?_, rfl⟩
  rw [insert_subinterval_seamR P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc2⟩

/-- Boundedness of a seam sub-cell image (both sides), used for its sSup/sInf. -/
lemma seamL_bddAbove (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    BddAbove (f '' subinterval (insertPoint P k hkn c hc1 hc2) k) :=
  BddAbove.mono (Set.image_mono (fun z hz =>
    subinterval_subset_Icc_core P hkn (insert_seamL_subset P k hkn c hc1 hc2 hz))) hAbove

lemma seamR_bddAbove (f : ℝ → ℝ) (hAbove : BddAbove (f '' Icc a b)) :
    BddAbove (f '' subinterval (insertPoint P k hkn c hc1 hc2) (k + 1)) :=
  BddAbove.mono (Set.image_mono (fun z hz =>
    subinterval_subset_Icc_core P hkn (insert_seamR_subset P k hkn c hc1 hc2 hz))) hAbove

/-- Seam sub-cell upper steps are `≥ m_k` (left). -/
lemma seam_lowerStep_le_upperStep_L (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStep P f k ≤ upperStep (insertPoint P k hkn c hc1 hc2) f k := by
  -- pick x = P.pts k in the left seam sub-cell
  have hxmem : P.pts k ∈ subinterval (insertPoint P k hkn c hc1 hc2) k := by
    rw [insert_subinterval_seamL P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc1⟩
  have hxcell : P.pts k ∈ subinterval P k :=
    insert_seamL_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStep P f k ≤ f (P.pts k) :=
    csInf_le (cell_bddBelow P k hkn f hBelow) ⟨P.pts k, hxcell, rfl⟩
  have h2 : f (P.pts k) ≤ upperStep (insertPoint P k hkn c hc1 hc2) f k :=
    le_csSup (seamL_bddAbove P k hkn c hc1 hc2 f hAbove) ⟨P.pts k, hxmem, rfl⟩
  exact le_trans h1 h2

/-- Seam sub-cell upper steps are `≥ m_k` (right). -/
lemma seam_lowerStep_le_upperStep_R (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStep P f k ≤ upperStep (insertPoint P k hkn c hc1 hc2) f (k + 1) := by
  have hxmem : c ∈ subinterval (insertPoint P k hkn c hc1 hc2) (k + 1) := by
    rw [insert_subinterval_seamR P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc2⟩
  have hxcell : c ∈ subinterval P k :=
    insert_seamR_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStep P f k ≤ f c :=
    csInf_le (cell_bddBelow P k hkn f hBelow) ⟨c, hxcell, rfl⟩
  have h2 : f c ≤ upperStep (insertPoint P k hkn c hc1 hc2) f (k + 1) :=
    le_csSup (seamR_bddAbove P k hkn c hc1 hc2 f hAbove) ⟨c, hxmem, rfl⟩
  exact le_trans h1 h2

/-- Boundedness below of seam sub-cell images. -/
lemma seamL_bddBelow (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    BddBelow (f '' subinterval (insertPoint P k hkn c hc1 hc2) k) :=
  BddBelow.mono (Set.image_mono (fun z hz =>
    subinterval_subset_Icc_core P hkn (insert_seamL_subset P k hkn c hc1 hc2 hz))) hBelow

lemma seamR_bddBelow (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    BddBelow (f '' subinterval (insertPoint P k hkn c hc1 hc2) (k + 1)) :=
  BddBelow.mono (Set.image_mono (fun z hz =>
    subinterval_subset_Icc_core P hkn (insert_seamR_subset P k hkn c hc1 hc2 hz))) hBelow

/-- Seam sub-cell lower steps are `≥ m_k`. -/
lemma seam_lowerStep_ge_L (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStep P f k ≤ lowerStep (insertPoint P k hkn c hc1 hc2) f k := by
  have hne : (f '' subinterval (insertPoint P k hkn c hc1 hc2) k).Nonempty := by
    rw [insert_subinterval_seamL P k hkn c hc1 hc2]
    exact ⟨f (P.pts k), P.pts k, ⟨le_rfl, le_of_lt hc1⟩, rfl⟩
  unfold lowerStep
  refine le_csInf hne ?_
  rintro y ⟨x, hx, rfl⟩
  have hxcell : x ∈ subinterval P k := insert_seamL_subset P k hkn c hc1 hc2 hx
  exact csInf_le (cell_bddBelow P k hkn f hBelow) ⟨x, hxcell, rfl⟩

lemma seam_lowerStep_ge_R (f : ℝ → ℝ) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStep P f k ≤ lowerStep (insertPoint P k hkn c hc1 hc2) f (k + 1) := by
  have hne : (f '' subinterval (insertPoint P k hkn c hc1 hc2) (k + 1)).Nonempty := by
    rw [insert_subinterval_seamR P k hkn c hc1 hc2]
    exact ⟨f c, c, ⟨le_rfl, le_of_lt hc2⟩, rfl⟩
  unfold lowerStep
  refine le_csInf hne ?_
  rintro y ⟨x, hx, rfl⟩
  have hxcell : x ∈ subinterval P k := insert_seamR_subset P k hkn c hc1 hc2 hx
  exact csInf_le (cell_bddBelow P k hkn f hBelow) ⟨x, hxcell, rfl⟩

/-- Seam sub-cell lower steps are `≤ M_k`. -/
lemma seam_lowerStep_le_upper_L (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStep (insertPoint P k hkn c hc1 hc2) f k ≤ upperStep P f k := by
  have hxmem : P.pts k ∈ subinterval (insertPoint P k hkn c hc1 hc2) k := by
    rw [insert_subinterval_seamL P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc1⟩
  have hxcell : P.pts k ∈ subinterval P k :=
    insert_seamL_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStep (insertPoint P k hkn c hc1 hc2) f k ≤ f (P.pts k) :=
    csInf_le (seamL_bddBelow P k hkn c hc1 hc2 f hBelow) ⟨P.pts k, hxmem, rfl⟩
  have h2 : f (P.pts k) ≤ upperStep P f k :=
    le_csSup (cell_bddAbove P k hkn f hAbove) ⟨P.pts k, hxcell, rfl⟩
  exact le_trans h1 h2

lemma seam_lowerStep_le_upper_R (f : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    lowerStep (insertPoint P k hkn c hc1 hc2) f (k + 1) ≤ upperStep P f k := by
  have hxmem : c ∈ subinterval (insertPoint P k hkn c hc1 hc2) (k + 1) := by
    rw [insert_subinterval_seamR P k hkn c hc1 hc2]; exact ⟨le_rfl, le_of_lt hc2⟩
  have hxcell : c ∈ subinterval P k :=
    insert_seamR_subset P k hkn c hc1 hc2 hxmem
  have h1 : lowerStep (insertPoint P k hkn c hc1 hc2) f (k + 1) ≤ f c :=
    csInf_le (seamR_bddBelow P k hkn c hc1 hc2 f hBelow) ⟨c, hxmem, rfl⟩
  have h2 : f c ≤ upperStep P f k :=
    le_csSup (cell_bddAbove P k hkn f hAbove) ⟨c, hxcell, rfl⟩
  exact le_trans h1 h2

/-! ### The cell-oscillation change bound (α-continuous branch core). -/

include hkn in
lemma cptk_mem : P.pts k ∈ Icc a b := partition_pts_mem_Icc_core P (Nat.le_of_lt hkn)

include hkn in
lemma cptk1_mem : P.pts (k + 1) ∈ Icc a b :=
  partition_pts_mem_Icc_core P (Nat.succ_le_of_lt hkn)

include hkn hc1 hc2 in
lemma c_mem : c ∈ Icc a b := by
  have h1 := cptk_mem P k hkn
  have h2 := cptk1_mem P k hkn
  exact ⟨le_trans h1.1 (le_of_lt hc1), le_trans (le_of_lt hc2) h2.2⟩

/-- The upper-sum change under insertion is dominated by the cell oscillation. -/
lemma abs_upperSum_insert_le (f α : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b))
    (hmono : MonotoneOn α (Icc a b)) :
    |upperSum P f α - upperSum (insertPoint P k hkn c hc1 hc2) f α|
      ≤ (upperStep P f k - lowerStep P f k)
          * (α (P.pts (k + 1)) - α (P.pts k)) := by
  set P' := insertPoint P k hkn c hc1 hc2 with hP'
  -- increments
  have hkmem := cptk_mem P k hkn
  have hk1mem := cptk1_mem P k hkn
  have hcmem := c_mem P k hkn c hc1 hc2
  have hdL : 0 ≤ α c - α (P.pts k) :=
    sub_nonneg.mpr (hmono hkmem hcmem (le_of_lt hc1))
  have hdR : 0 ≤ α (P.pts (k + 1)) - α c :=
    sub_nonneg.mpr (hmono hcmem hk1mem (le_of_lt hc2))
  -- sub-cell step bounds
  have hML_le : upperStep P' f k ≤ upperStep P f k := seam_upperStep_le_L P k hkn c hc1 hc2 f hAbove
  have hMR_le : upperStep P' f (k + 1) ≤ upperStep P f k := seam_upperStep_le_R P k hkn c hc1 hc2 f hAbove
  have hm_le_L : lowerStep P f k ≤ upperStep P' f k :=
    seam_lowerStep_le_upperStep_L P k hkn c hc1 hc2 f hAbove hBelow
  have hm_le_R : lowerStep P f k ≤ upperStep P' f (k + 1) :=
    seam_lowerStep_le_upperStep_R P k hkn c hc1 hc2 f hAbove hBelow
  -- the difference identity
  have hid := upperSum_insert_eq P k hkn c hc1 hc2 f α
  -- abbreviations
  set M := upperStep P f k
  set m := lowerStep P f k
  set ML := upperStep P' f k
  set MR := upperStep P' f (k + 1)
  set dL := α c - α (P.pts k)
  set dR := α (P.pts (k + 1)) - α c
  -- Δα_k = dL + dR
  have hsum : α (P.pts (k + 1)) - α (P.pts k) = dL + dR := by
    simp only [dL, dR]; ring
  rw [hsum]
  -- from identity: upperSum P - upperSum P' = M*(dL+dR) - (ML*dL + MR*dR)
  have hdiff : upperSum P f α - upperSum P' f α
      = M * (dL + dR) - (ML * dL + MR * dR) := by
    rw [hid]; ring
  rw [hdiff]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hm_le_L hdL,
      mul_le_mul_of_nonneg_right hm_le_R hdR]
  · nlinarith [mul_le_mul_of_nonneg_right hML_le hdL,
      mul_le_mul_of_nonneg_right hMR_le hdR]

/-- The lower-sum change under insertion is dominated by the cell oscillation. -/
lemma abs_lowerSum_insert_le (f α : ℝ → ℝ)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b))
    (hmono : MonotoneOn α (Icc a b)) :
    |lowerSum P f α - lowerSum (insertPoint P k hkn c hc1 hc2) f α|
      ≤ (upperStep P f k - lowerStep P f k)
          * (α (P.pts (k + 1)) - α (P.pts k)) := by
  set P' := insertPoint P k hkn c hc1 hc2 with hP'
  have hkmem := cptk_mem P k hkn
  have hk1mem := cptk1_mem P k hkn
  have hcmem := c_mem P k hkn c hc1 hc2
  have hdL : 0 ≤ α c - α (P.pts k) :=
    sub_nonneg.mpr (hmono hkmem hcmem (le_of_lt hc1))
  have hdR : 0 ≤ α (P.pts (k + 1)) - α c :=
    sub_nonneg.mpr (hmono hcmem hk1mem (le_of_lt hc2))
  have hmL_ge : lowerStep P f k ≤ lowerStep P' f k := seam_lowerStep_ge_L P k hkn c hc1 hc2 f hBelow
  have hmR_ge : lowerStep P f k ≤ lowerStep P' f (k + 1) := seam_lowerStep_ge_R P k hkn c hc1 hc2 f hBelow
  have hmL_le : lowerStep P' f k ≤ upperStep P f k :=
    seam_lowerStep_le_upper_L P k hkn c hc1 hc2 f hAbove hBelow
  have hmR_le : lowerStep P' f (k + 1) ≤ upperStep P f k :=
    seam_lowerStep_le_upper_R P k hkn c hc1 hc2 f hAbove hBelow
  have hid := lowerSum_insert_eq P k hkn c hc1 hc2 f α
  set M := upperStep P f k
  set m := lowerStep P f k
  set mL := lowerStep P' f k
  set mR := lowerStep P' f (k + 1)
  set dL := α c - α (P.pts k)
  set dR := α (P.pts (k + 1)) - α c
  have hsum : α (P.pts (k + 1)) - α (P.pts k) = dL + dR := by
    simp only [dL, dR]; ring
  rw [hsum]
  have hdiff : lowerSum P f α - lowerSum P' f α
      = m * (dL + dR) - (mL * dL + mR * dR) := by
    rw [hid]; ring
  rw [hdiff, abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hmL_le hdL,
      mul_le_mul_of_nonneg_right hmR_le hdR]
  · nlinarith [mul_le_mul_of_nonneg_right hmL_ge hdL,
      mul_le_mul_of_nonneg_right hmR_ge hdR]

/-! ### Mesh monotonicity under insertion. -/

include hkn hc1 hc2 in
lemma insert_gap_le_mesh {i : ℕ} (hi : i < (insertPoint P k hkn c hc1 hc2).n) :
    (insertPoint P k hkn c hc1 hc2).pts (i + 1) - (insertPoint P k hkn c hc1 hc2).pts i
      ≤ P.mesh := by
  have hgapk : P.pts (k + 1) - P.pts k ≤ P.mesh := partition_length_le_mesh P hkn
  rcases lt_trichotomy i k with hlt | heq | hgt
  · -- i < k
    rw [insert_pts_lt P k hkn c hc1 hc2 (by omega : i + 1 ≤ k),
       insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hlt)]
    exact partition_length_le_mesh P (lt_trans hlt hkn)
  · -- i = k : gap = c - P.pts k
    subst heq
    rw [insert_pts_lt P i hkn c hc1 hc2 (le_refl i), insertPoint_pts_seam P i hkn c hc1 hc2]
    have : P.pts i ≤ P.pts (i + 1) := le_of_lt (P.strict_mono i hkn)
    linarith [le_of_lt hc2]
  · -- i > k
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · omega
    · rcases Nat.eq_or_lt_of_le h with heq1 | hgt1
      · -- i = k + 1 : gap = P.pts (k+1) - c
        rw [← heq1, insertPoint_pts_seam P k hkn c hc1 hc2,
           show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + 1) = P.pts (k + 1) from by
             have := insert_pts_ge P k hkn c hc1 hc2 0
             simpa using this]
        have : P.pts k ≤ P.pts (k + 1) := le_of_lt (P.strict_mono k hkn)
        linarith [le_of_lt hc1]
      · -- i ≥ k + 2 : shifted P gap
        obtain ⟨j, rfl⟩ : ∃ j, i = k + 1 + (j + 1) := ⟨i - k - 2, by omega⟩
        rw [insert_pts_ge P k hkn c hc1 hc2 j,
           show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + (j + 1) + 1)
               = P.pts (k + (j + 1) + 1) from by
             have := insert_pts_ge P k hkn c hc1 hc2 (j + 1)
             rw [show k + 1 + (j + 1 + 1) = k + 1 + (j + 1) + 1 from by omega,
                show k + (j + 1 + 1) = k + (j + 1) + 1 from by omega] at this
             exact this]
        have hlt2 : k + (j + 1) < P.n := by
          have : (insertPoint P k hkn c hc1 hc2).n = P.n + 1 := rfl
          omega
        exact partition_length_le_mesh P hlt2

include hkn hc1 hc2 in
lemma mesh_insert_le :
    (insertPoint P k hkn c hc1 hc2).mesh ≤ P.mesh := by
  unfold Partition.mesh
  apply Finset.sup'_le
  intro i hi
  exact insert_gap_le_mesh P k hkn c hc1 hc2 (Finset.mem_range.mp hi)

/-! ### Tag transport is valid on the inserted partition. -/

include hkn hc1 hc2 in
lemma insTags_valid (tags : ℕ → ℝ) (htags : tagsInPartition P tags) :
    tagsInPartition (insertPoint P k hkn c hc1 hc2) (insTags tags k c) := by
  intro i hi
  have hin : (insertPoint P k hkn c hc1 hc2).n = P.n + 1 := rfl
  rw [hin] at hi
  rcases lt_trichotomy i k with hlt | heq | hgt
  · -- i < k
    rw [insTags_lt tags k c hlt, insert_subinterval_lt P k hkn c hc1 hc2 hlt]
    exact htags i (lt_trans hlt hkn)
  · -- i = k : tag d in [pts k, c]
    subst heq
    rw [insTags_seamL tags i c, insert_subinterval_seamL P i hkn c hc1 hc2]
    exact ⟨le_of_lt hc1, le_rfl⟩
  · rcases Nat.lt_or_ge i (k + 1) with h | h
    · omega
    · rcases Nat.eq_or_lt_of_le h with heq1 | hgt1
      · -- i = k + 1 : tag d in [c, pts (k+1)]
        rw [← heq1, insTags_seamR tags k c, insert_subinterval_seamR P k hkn c hc1 hc2]
        exact ⟨le_rfl, le_of_lt hc2⟩
      · -- i ≥ k + 2 : shifted tag in shifted cell
        obtain ⟨j, rfl⟩ : ∃ j, i = k + 1 + (j + 1) := ⟨i - k - 2, by omega⟩
        rw [insTags_gt tags k c (by omega : k + 1 < k + 1 + (j + 1)),
           insert_subinterval_gt P k hkn c hc1 hc2 j,
           show k + 1 + (j + 1) - 1 = k + (j + 1) from by omega]
        have hlt2 : k + (j + 1) < P.n := by omega
        exact htags (k + (j + 1)) hlt2

include hkn hc1 hc2 in
lemma taggedSum_insert_eq (tags : ℕ → ℝ) (f α : ℝ → ℝ) :
    taggedSum P tags f α =
      taggedSum (insertPoint P k hkn c hc1 hc2) (insTags tags k c) f α
        - (f c * (α c - α (P.pts k)) + f c * (α (P.pts (k + 1)) - α c))
        + f (tags k) * (α (P.pts (k + 1)) - α (P.pts k)) := by
  have key := sum_insert_diff P.n k hkn
    (fun i => f (tags i) * (α (P.pts (i + 1)) - α (P.pts i)))
    (fun i => f (insTags tags k c i)
      * (α ((insertPoint P k hkn c hc1 hc2).pts (i + 1))
          - α ((insertPoint P k hkn c hc1 hc2).pts i)))
    (f c * (α c - α (P.pts k)))
    (f c * (α (P.pts (k + 1)) - α c))
    ?hlt ?hkL ?hkR ?hgt
  · simpa [taggedSum] using key
  case hlt =>
    intro i hi
    simp only []
    rw [insTags_lt tags k c hi,
       insert_pts_lt P k hkn c hc1 hc2 (by omega : i + 1 ≤ k),
       insert_pts_lt P k hkn c hc1 hc2 (le_of_lt hi)]
  case hkL =>
    simp only []
    rw [insTags_seamL tags k c, insert_pts_lt P k hkn c hc1 hc2 (le_refl k),
       insertPoint_pts_seam P k hkn c hc1 hc2]
  case hkR =>
    simp only []
    rw [insTags_seamR tags k c, insertPoint_pts_seam P k hkn c hc1 hc2,
       show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + 1) = P.pts (k + 1) from by
         have := insert_pts_ge P k hkn c hc1 hc2 0
         simpa using this]
  case hgt =>
    intro j
    simp only []
    rw [insTags_gt tags k c (by omega : k + 1 < k + 1 + (j + 1)),
       show k + 1 + (j + 1) - 1 = k + (j + 1) from by omega,
       insert_pts_ge P k hkn c hc1 hc2 j,
       show (insertPoint P k hkn c hc1 hc2).pts (k + 1 + (j + 1) + 1)
           = P.pts (k + (j + 1) + 1) from by
         have := insert_pts_ge P k hkn c hc1 hc2 (j + 1)
         rw [show k + 1 + (j + 1 + 1) = k + 1 + (j + 1) + 1 from by omega,
            show k + (j + 1 + 1) = k + (j + 1) + 1 from by omega] at this
         exact this]

end InsertCells

/-! ## Gluing the source hypotheses on `[a,d]` and `[d,b]` into `[a,b]`. -/

lemma image_Icc_union {f : ℝ → ℝ} {a d b : ℝ} (had : a ≤ d) (hdb : d ≤ b) :
    f '' Icc a b = f '' Icc a d ∪ f '' Icc d b := by
  rw [← Set.image_union, Set.Icc_union_Icc_eq_Icc had hdb]

lemma sourceHypotheses_glue {a d b : ℝ} {f α : ℝ → ℝ}
    (h₁ : SourceHypotheses a d f α) (h₂ : SourceHypotheses d b f α) :
    SourceHypotheses a b f α := by
  rcases h₁ with ⟨had, hA₁, hB₁, hM₁⟩
  rcases h₂ with ⟨hdb, hA₂, hB₂, hM₂⟩
  have hadb : a ≤ b := le_of_lt (lt_trans had hdb)
  refine ⟨lt_trans had hdb, ?_, ?_, ?_⟩
  · rw [image_Icc_union (le_of_lt had) (le_of_lt hdb)]; exact hA₁.union hA₂
  · rw [image_Icc_union (le_of_lt had) (le_of_lt hdb)]; exact hB₁.union hB₂
  · -- glue monotonicity
    intro x hx y hy hxy
    have hd_ad : d ∈ Icc a d := ⟨le_of_lt had, le_rfl⟩
    have hd_db : d ∈ Icc d b := ⟨le_rfl, le_of_lt hdb⟩
    rcases le_or_gt x d with hxd | hdx
    · rcases le_or_gt y d with hyd | hdy
      · -- both in [a,d]
        exact hM₁ ⟨hx.1, hxd⟩ ⟨hy.1, hyd⟩ hxy
      · -- x ≤ d ≤ y
        have hx_ad : x ∈ Icc a d := ⟨hx.1, hxd⟩
        have hy_db : y ∈ Icc d b := ⟨le_of_lt hdy, hy.2⟩
        exact le_trans (hM₁ hx_ad hd_ad hxd) (hM₂ hd_db hy_db (le_of_lt hdy))
    · -- d < x ≤ y, both in [d,b]
      have hx_db : x ∈ Icc d b := ⟨le_of_lt hdx, hx.2⟩
      have hy_db : y ∈ Icc d b := ⟨le_of_lt (lt_of_lt_of_le hdx hxy), hy.2⟩
      exact hM₂ hx_db hy_db hxy

/-! ## Oscillation constant and cell-oscillation bound `M_k - m_k ≤ Ω`. -/

/-- The global oscillation of `f` on `[a,b]`. -/
def Omega (f : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (f '' Icc a b) - sInf (f '' Icc a b)

lemma omega_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    0 ≤ Omega f a b := by
  have hne : (f '' Icc a b).Nonempty := ⟨f a, a, ⟨le_rfl, le_of_lt hab⟩, rfl⟩
  obtain ⟨y, hy⟩ := hne
  have h1 : sInf (f '' Icc a b) ≤ y := csInf_le hBelow hy
  have h2 : y ≤ sSup (f '' Icc a b) := le_csSup hAbove hy
  unfold Omega; linarith

/-- Cell oscillation is bounded by the global oscillation. -/
lemma cell_osc_le_omega {a b : ℝ} (P : Partition a b) {k : ℕ} (hkn : k < P.n)
    {f : ℝ → ℝ}
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b)) :
    upperStep P f k - lowerStep P f k ≤ Omega f a b := by
  have hcellAbove : BddAbove (f '' subinterval P k) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P hkn)) hAbove
  have hcellBelow : BddBelow (f '' subinterval P k) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P hkn)) hBelow
  have hsub : f '' subinterval P k ⊆ f '' Icc a b :=
    Set.image_mono (subinterval_subset_Icc_core P hkn)
  have hne : (f '' subinterval P k).Nonempty :=
    ⟨f (P.pts k), P.pts k, ⟨le_rfl, le_of_lt (P.strict_mono k hkn)⟩, rfl⟩
  have hUp : upperStep P f k ≤ sSup (f '' Icc a b) := by
    unfold upperStep
    exact csSup_le_csSup hAbove hne hsub
  have hLow : sInf (f '' Icc a b) ≤ lowerStep P f k := by
    unfold lowerStep
    exact csInf_le_csInf hBelow hne hsub
  unfold Omega; linarith

/-- In a crossing cell, every point is within the mesh of the crossing point `d`. -/
lemma crossing_point_dist_le {a b d : ℝ} (P : Partition a b) {k : ℕ} (hkn : k < P.n)
    (hc1 : P.pts k < d) (hc2 : d < P.pts (k + 1)) {x : ℝ} (hx : x ∈ subinterval P k) :
    |x - d| ≤ P.mesh := by
  have hlen : P.pts (k + 1) - P.pts k ≤ P.mesh := partition_length_le_mesh P hkn
  have : |x - d| ≤ P.pts (k + 1) - P.pts k := by
    rw [abs_le]; constructor
    · nlinarith [hx.1, le_of_lt hc2]
    · nlinarith [hx.2, le_of_lt hc1]
  linarith

/-- Any cell increment is bounded by the total α-increment `α b - α a`. -/
lemma alpha_gap_le_total {a b : ℝ} (P : Partition a b) {k : ℕ} (hkn : k < P.n)
    {α : ℝ → ℝ} (hmono : MonotoneOn α (Icc a b)) :
    α (P.pts (k + 1)) - α (P.pts k) ≤ α b - α a := by
  have hkmem : P.pts k ∈ Icc a b := partition_pts_mem_Icc_core P (Nat.le_of_lt hkn)
  have hk1mem : P.pts (k + 1) ∈ Icc a b := partition_pts_mem_Icc_core P (Nat.succ_le_of_lt hkn)
  have hamem : a ∈ Icc a b := ⟨le_rfl, le_of_lt (lt_of_le_of_lt hkmem.1 (lt_of_lt_of_le
    (P.strict_mono k hkn) hk1mem.2))⟩
  have hbmem : b ∈ Icc a b := ⟨hamem.2, le_rfl⟩
  have h1 : α a ≤ α (P.pts k) := hmono hamem hkmem hkmem.1
  have h2 : α (P.pts (k + 1)) ≤ α b := hmono hk1mem hbmem hk1mem.2
  linarith

/-- Cell oscillation under f-closeness to a value `v`: if every point of the cell
maps within `η` of `v`, the cell oscillation is at most `2η`. -/
lemma cell_osc_le_of_close {a b : ℝ} (P : Partition a b) {k : ℕ} (hkn : k < P.n)
    {f : ℝ → ℝ} {v η : ℝ}
    (hclose : ∀ x ∈ subinterval P k, |f x - v| ≤ η) :
    upperStep P f k - lowerStep P f k ≤ 2 * η := by
  have hne : (f '' subinterval P k).Nonempty :=
    ⟨f (P.pts k), P.pts k, ⟨le_rfl, le_of_lt (P.strict_mono k hkn)⟩, rfl⟩
  have hAbove : BddAbove (f '' subinterval P k) := by
    refine ⟨v + η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx
    rw [abs_le] at this; linarith [this.2]
  have hBelow : BddBelow (f '' subinterval P k) := by
    refine ⟨v - η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx
    rw [abs_le] at this; linarith [this.1]
  have hUp : upperStep P f k ≤ v + η := by
    unfold upperStep
    refine csSup_le hne ?_
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx; rw [abs_le] at this; linarith [this.2]
  have hLow : v - η ≤ lowerStep P f k := by
    unfold lowerStep
    refine le_csInf hne ?_
    rintro y ⟨x, hx, rfl⟩
    have := hclose x hx; rw [abs_le] at this; linarith [this.1]
  linarith

/-- Seam comparison: `|f x - f y| ≤ Ω` for `x, y ∈ Icc a b`. -/
lemma abs_f_sub_le_omega {f : ℝ → ℝ} {a b : ℝ}
    (hAbove : BddAbove (f '' Icc a b)) (hBelow : BddBelow (f '' Icc a b))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ Omega f a b := by
  have hfx_le : f x ≤ sSup (f '' Icc a b) := le_csSup hAbove ⟨x, hx, rfl⟩
  have hfy_le : f y ≤ sSup (f '' Icc a b) := le_csSup hAbove ⟨y, hy, rfl⟩
  have hle_fx : sInf (f '' Icc a b) ≤ f x := csInf_le hBelow ⟨x, hx, rfl⟩
  have hle_fy : sInf (f '' Icc a b) ≤ f y := csInf_le hBelow ⟨y, hy, rfl⟩
  rw [abs_le]; unfold Omega; constructor <;> linarith

/-! ## Locating a point `d` in a partition of `[a,b]`. -/

open Classical in
/-- For `a < d < b` and any partition `P`, either `d` is an interior grid point,
or `d` falls strictly inside a unique cell. -/
lemma locate_point {a b : ℝ} (P : Partition a b) {d : ℝ}
    (had : a < d) (hdb : d < b) :
    (∃ k, 0 < k ∧ k < P.n ∧ P.pts k = d) ∨
      (∃ k, k < P.n ∧ P.pts k < d ∧ d < P.pts (k + 1)) := by
  set Q : ℕ → Prop := fun i => P.pts i ≤ d with hQ
  set k := Nat.findGreatest Q P.n with hk
  have hstart : Q 0 := by simp [hQ, P.pts_start, le_of_lt had]
  have hk_le : k ≤ P.n := Nat.findGreatest_le P.n
  have hk_spec : Q k := Nat.findGreatest_spec (Nat.zero_le P.n) hstart
  have hkltn : k < P.n := by
    rcases lt_or_eq_of_le hk_le with h | h
    · exact h
    · exfalso
      rw [h] at hk_spec
      simp only [hQ] at hk_spec
      rw [P.pts_end] at hk_spec
      linarith
  have hgt : ¬ Q (k + 1) := by
    apply Nat.findGreatest_is_greatest (by omega : k < k + 1) (by omega : k + 1 ≤ P.n)
  have hd_lt : d < P.pts (k + 1) := by
    simp only [hQ] at hgt; exact lt_of_not_ge hgt
  have hpk_le : P.pts k ≤ d := by simpa [hQ] using hk_spec
  rcases lt_or_eq_of_le hpk_le with hlt | heq
  · -- strictly inside cell k
    exact Or.inr ⟨k, hkltn, hlt, hd_lt⟩
  · -- d is grid point P.pts k, and k > 0 since a < d
    refine Or.inl ⟨k, ?_, hkltn, heq⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso; rw [hk0, P.pts_start] at heq; linarith
    · exact hkpos

/-! ## The tagged common limit glues across `d` (α-continuous branch). -/

theorem taggedCommonLimit_glue_alpha {a d b : ℝ} {f α : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a d f α L₁) (h₂ : TaggedCommonLimit d b f α L₂)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    TaggedCommonLimit a b f α (L₁ + L₂) := by
  obtain ⟨hs₁, hlim₁⟩ := h₁
  obtain ⟨hs₂, hlim₂⟩ := h₂
  have hs : SourceHypotheses a b f α := sourceHypotheses_glue ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
    ⟨hs₂.1, hs₂.2.1, hs₂.2.2.1, hs₂.2.2.2⟩
  obtain ⟨hab, hAbove, hBelow, hmono⟩ := hs
  refine ⟨⟨hab, hAbove, hBelow, hmono⟩, ?_⟩
  intro eps heps
  -- oscillation
  set Ω := Omega f a b with hΩ
  have hΩnn : 0 ≤ Ω := omega_nonneg hab hAbove hBelow
  -- tolerances
  have hquarter : 0 < eps / 4 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hlim₁ (eps / 4) hquarter
  obtain ⟨δ₂, hδ₂, H₂⟩ := hlim₂ (eps / 4) hquarter
  -- continuity tolerance
  set epsp : ℝ := eps / (4 * (Ω + 1)) with hepsp
  have hΩ1pos : 0 < Ω + 1 := by linarith
  have hepsp_pos : 0 < epsp := by rw [hepsp]; positivity
  obtain ⟨δ₃, hδ₃, Hδ₃⟩ := Metric.continuousAt_iff.mp hαd epsp hepsp_pos
  refine ⟨min (min δ₁ δ₂) δ₃, by positivity, ?_⟩
  intro P tags htags hmesh
  have hmesh₁ : P.mesh < δ₁ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmesh₂ : P.mesh < δ₂ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmesh₃ : P.mesh < δ₃ := lt_of_lt_of_le hmesh (min_le_right _ _)
  rcases locate_point P had hdb with ⟨k, hk0, hkn, hpk⟩ | ⟨k, hkn, hc1, hc2⟩
  · -- d is a grid point of P
    -- split P at k
    rw [taggedSum_split P k hk0 hkn d hpk tags f α]
    set P₁ := splitLeft P k hk0 (le_of_lt hkn) d hpk with hP₁
    set P₂ := splitRight P k hkn d hpk with hP₂
    have ht₁ : tagsInPartition P₁ tags :=
      tagsInPartition_splitLeft P k hk0 hkn d hpk tags htags
    have ht₂ : tagsInPartition P₂ (fun j => tags (k + j)) :=
      tagsInPartition_splitRight P k hkn d hpk tags htags
    have hm₁ : P₁.mesh < δ₁ := lt_of_le_of_lt (mesh_splitLeft_le P k hk0 hkn d hpk) hmesh₁
    have hm₂ : P₂.mesh < δ₂ := lt_of_le_of_lt (mesh_splitRight_le P k hk0 hkn d hpk) hmesh₂
    have hb₁ := H₁ P₁ tags ht₁ hm₁
    have hb₂ := H₂ P₂ (fun j => tags (k + j)) ht₂ hm₂
    have : taggedSum P₁ tags f α + taggedSum P₂ (fun j => tags (k + j)) f α - (L₁ + L₂)
        = (taggedSum P₁ tags f α - L₁) + (taggedSum P₂ (fun j => tags (k + j)) f α - L₂) := by
      ring
    rw [this]
    calc
      |(taggedSum P₁ tags f α - L₁) + (taggedSum P₂ (fun j => tags (k + j)) f α - L₂)|
          ≤ |taggedSum P₁ tags f α - L₁| + |taggedSum P₂ (fun j => tags (k + j)) f α - L₂| :=
        abs_add_le _ _
      _ < eps / 4 + eps / 4 := add_lt_add hb₁ hb₂
      _ < eps := by linarith
  · -- d falls strictly inside cell k; insert it
    set P' := insertPoint P k hkn d hc1 hc2 with hP'
    have hmeshP' : P'.mesh < min (min δ₁ δ₂) δ₃ :=
      lt_of_le_of_lt (mesh_insert_le P k hkn d hc1 hc2) hmesh
    have hmeshP'₁ : P'.mesh < δ₁ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_left _ _))
    have hmeshP'₂ : P'.mesh < δ₂ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_right _ _))
    -- transported tags
    set tags' := insTags tags k d with htags'
    have ht' : tagsInPartition P' tags' := insTags_valid P k hkn d hc1 hc2 tags htags
    -- seam-term difference bound
    have hseamid := taggedSum_insert_eq P k hkn d hc1 hc2 tags f α
    -- Δα_k < 2 epsp
    have hkmem : P.pts k ∈ Icc a b := cptk_mem P k hkn
    have hk1mem : P.pts (k + 1) ∈ Icc a b := cptk1_mem P k hkn
    have hdmem : d ∈ Icc a b := c_mem P k hkn d hc1 hc2
    have hgapk : P.pts (k + 1) - P.pts k ≤ P.mesh := partition_length_le_mesh P hkn
    have hdL_lt : α d - α (P.pts k) < epsp := by
      have hdist : dist (P.pts k) d < δ₃ := by
        rw [Real.dist_eq]
        have : |P.pts k - d| ≤ P.mesh := by
          rw [abs_le]; constructor <;> [nlinarith [le_of_lt hc2]; nlinarith [le_of_lt hc1]]
        exact lt_of_le_of_lt this hmesh₃
      have := Hδ₃ hdist
      rw [Real.dist_eq] at this
      have h := (abs_lt.mp this).1
      linarith
    have hdR_lt : α (P.pts (k + 1)) - α d < epsp := by
      have hdist : dist (P.pts (k + 1)) d < δ₃ := by
        rw [Real.dist_eq]
        have : |P.pts (k + 1) - d| ≤ P.mesh := by
          rw [abs_le]; constructor <;> [nlinarith [le_of_lt hc1]; nlinarith [le_of_lt hc2]]
        exact lt_of_le_of_lt this hmesh₃
      have := Hδ₃ hdist
      rw [Real.dist_eq] at this
      have h := (abs_lt.mp this).2
      linarith
    have hdL_nn : 0 ≤ α d - α (P.pts k) :=
      sub_nonneg.mpr (hmono hkmem hdmem (le_of_lt hc1))
    have hdR_nn : 0 ≤ α (P.pts (k + 1)) - α d :=
      sub_nonneg.mpr (hmono hdmem hk1mem (le_of_lt hc2))
    have hΔ_lt : α (P.pts (k + 1)) - α (P.pts k) < 2 * epsp := by linarith
    have hΔ_nn : 0 ≤ α (P.pts (k + 1)) - α (P.pts k) := by linarith
    -- seam difference in absolute value
    have htagk_mem : tags k ∈ Icc a b :=
      subinterval_subset_Icc_core P hkn (htags k hkn)
    have hfsub : |f (tags k) - f d| ≤ Ω := abs_f_sub_le_omega hAbove hBelow htagk_mem hdmem
    have hseam_diff : taggedSum P tags f α - taggedSum P' tags' f α
        = (f (tags k) - f d) * (α (P.pts (k + 1)) - α (P.pts k)) := by
      rw [hseamid]; ring
    have hseam_bound : |taggedSum P tags f α - taggedSum P' tags' f α| ≤ Ω * (2 * epsp) := by
      rw [hseam_diff, abs_mul, abs_of_nonneg hΔ_nn]
      calc
        |f (tags k) - f d| * (α (P.pts (k + 1)) - α (P.pts k))
            ≤ Ω * (α (P.pts (k + 1)) - α (P.pts k)) :=
          mul_le_mul_of_nonneg_right hfsub hΔ_nn
        _ ≤ Ω * (2 * epsp) := mul_le_mul_of_nonneg_left (le_of_lt hΔ_lt) hΩnn
    have hOmega2epsp : Ω * (2 * epsp) < eps / 2 := by
      rw [hepsp]
      rw [show Ω * (2 * (eps / (4 * (Ω + 1)))) = (Ω / (Ω + 1)) * (eps / 2) from by
        field_simp; ring]
      have hratio : Ω / (Ω + 1) < 1 := by
        rw [div_lt_one hΩ1pos]; linarith
      nlinarith [mul_pos (show (0:ℝ) < eps / 2 by positivity) (show (0:ℝ) < 1 by norm_num)]
    -- now split P' at k+1 (grid point d)
    have hdgrid : P'.pts (k + 1) = d := insertPoint_pts_seam P k hkn d hc1 hc2
    have hk1pos : 0 < k + 1 := by omega
    have hk1n : k + 1 < P'.n := by
      have : P'.n = P.n + 1 := rfl
      omega
    have hsplitP' := taggedSum_split P' (k + 1) hk1pos hk1n d hdgrid tags' f α
    set Q₁ := splitLeft P' (k + 1) hk1pos (le_of_lt hk1n) d hdgrid with hQ₁
    set Q₂ := splitRight P' (k + 1) hk1n d hdgrid with hQ₂
    have htQ₁ : tagsInPartition Q₁ tags' :=
      tagsInPartition_splitLeft P' (k + 1) hk1pos hk1n d hdgrid tags' ht'
    have htQ₂ : tagsInPartition Q₂ (fun j => tags' (k + 1 + j)) :=
      tagsInPartition_splitRight P' (k + 1) hk1n d hdgrid tags' ht'
    have hmQ₁ : Q₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₁
    have hmQ₂ : Q₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₂
    have hbQ₁ := H₁ Q₁ tags' htQ₁ hmQ₁
    have hbQ₂ := H₂ Q₂ (fun j => tags' (k + 1 + j)) htQ₂ hmQ₂
    have hP'split_bound : |taggedSum P' tags' f α - (L₁ + L₂)| < eps / 2 := by
      rw [hsplitP']
      have : taggedSum Q₁ tags' f α + taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - (L₁ + L₂)
          = (taggedSum Q₁ tags' f α - L₁)
            + (taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - L₂) := by ring
      rw [this]
      calc
        |(taggedSum Q₁ tags' f α - L₁)
          + (taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - L₂)|
            ≤ |taggedSum Q₁ tags' f α - L₁|
              + |taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hbQ₁ hbQ₂
        _ = eps / 2 := by ring
    -- triangle inequality
    have hfinal : |taggedSum P tags f α - (L₁ + L₂)| < eps := by
      have hsplit_eq : taggedSum P tags f α - (L₁ + L₂)
          = (taggedSum P tags f α - taggedSum P' tags' f α)
            + (taggedSum P' tags' f α - (L₁ + L₂)) := by ring
      rw [hsplit_eq]
      calc
        |(taggedSum P tags f α - taggedSum P' tags' f α)
          + (taggedSum P' tags' f α - (L₁ + L₂))|
            ≤ |taggedSum P tags f α - taggedSum P' tags' f α|
              + |taggedSum P' tags' f α - (L₁ + L₂)| := abs_add_le _ _
        _ < eps / 2 + eps / 2 := by
          apply add_lt_add_of_le_of_lt _ hP'split_bound
          exact le_of_lt (lt_of_le_of_lt hseam_bound hOmega2epsp)
        _ = eps := by ring
    exact hfinal

/-! ## The tagged common limit glues across `d` (f-continuous branch). -/

theorem taggedCommonLimit_glue_f {a d b : ℝ} {f α : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a d f α L₁) (h₂ : TaggedCommonLimit d b f α L₂)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    TaggedCommonLimit a b f α (L₁ + L₂) := by
  obtain ⟨hs₁, hlim₁⟩ := h₁
  obtain ⟨hs₂, hlim₂⟩ := h₂
  have hs : SourceHypotheses a b f α := sourceHypotheses_glue ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
    ⟨hs₂.1, hs₂.2.1, hs₂.2.2.1, hs₂.2.2.2⟩
  obtain ⟨hab, hAbove, hBelow, hmono⟩ := hs
  refine ⟨⟨hab, hAbove, hBelow, hmono⟩, ?_⟩
  intro eps heps
  -- total α-increment
  set A : ℝ := α b - α a with hA
  have hAnn : 0 ≤ A := by
    rw [hA]; have := hmono (⟨le_rfl, le_of_lt hab⟩ : a ∈ Icc a b)
      (⟨hab.le, le_rfl⟩ : b ∈ Icc a b) hab.le; linarith
  have hA1pos : 0 < A + 1 := by linarith
  have hquarter : 0 < eps / 4 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hlim₁ (eps / 4) hquarter
  obtain ⟨δ₂, hδ₂, H₂⟩ := hlim₂ (eps / 4) hquarter
  -- f-continuity tolerance
  set eta : ℝ := eps / (4 * (A + 1)) with heta
  have heta_pos : 0 < eta := by rw [heta]; positivity
  obtain ⟨δ₃, hδ₃, Hδ₃⟩ := Metric.continuousAt_iff.mp hfd eta heta_pos
  refine ⟨min (min δ₁ δ₂) δ₃, by positivity, ?_⟩
  intro P tags htags hmesh
  have hmesh₁ : P.mesh < δ₁ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmesh₂ : P.mesh < δ₂ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmesh₃ : P.mesh < δ₃ := lt_of_lt_of_le hmesh (min_le_right _ _)
  rcases locate_point P had hdb with ⟨k, hk0, hkn, hpk⟩ | ⟨k, hkn, hc1, hc2⟩
  · -- grid point: identical to α branch
    rw [taggedSum_split P k hk0 hkn d hpk tags f α]
    set P₁ := splitLeft P k hk0 (le_of_lt hkn) d hpk with hP₁
    set P₂ := splitRight P k hkn d hpk with hP₂
    have ht₁ : tagsInPartition P₁ tags :=
      tagsInPartition_splitLeft P k hk0 hkn d hpk tags htags
    have ht₂ : tagsInPartition P₂ (fun j => tags (k + j)) :=
      tagsInPartition_splitRight P k hkn d hpk tags htags
    have hm₁ : P₁.mesh < δ₁ := lt_of_le_of_lt (mesh_splitLeft_le P k hk0 hkn d hpk) hmesh₁
    have hm₂ : P₂.mesh < δ₂ := lt_of_le_of_lt (mesh_splitRight_le P k hk0 hkn d hpk) hmesh₂
    have hb₁ := H₁ P₁ tags ht₁ hm₁
    have hb₂ := H₂ P₂ (fun j => tags (k + j)) ht₂ hm₂
    have : taggedSum P₁ tags f α + taggedSum P₂ (fun j => tags (k + j)) f α - (L₁ + L₂)
        = (taggedSum P₁ tags f α - L₁) + (taggedSum P₂ (fun j => tags (k + j)) f α - L₂) := by
      ring
    rw [this]
    calc
      |(taggedSum P₁ tags f α - L₁) + (taggedSum P₂ (fun j => tags (k + j)) f α - L₂)|
          ≤ |taggedSum P₁ tags f α - L₁| + |taggedSum P₂ (fun j => tags (k + j)) f α - L₂| :=
        abs_add_le _ _
      _ < eps / 4 + eps / 4 := add_lt_add hb₁ hb₂
      _ < eps := by linarith
  · -- interior cell: insert d, seam bound via f-continuity
    set P' := insertPoint P k hkn d hc1 hc2 with hP'
    have hmeshP' : P'.mesh < min (min δ₁ δ₂) δ₃ :=
      lt_of_le_of_lt (mesh_insert_le P k hkn d hc1 hc2) hmesh
    have hmeshP'₁ : P'.mesh < δ₁ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_left _ _))
    have hmeshP'₂ : P'.mesh < δ₂ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_right _ _))
    set tags' := insTags tags k d with htags'
    have ht' : tagsInPartition P' tags' := insTags_valid P k hkn d hc1 hc2 tags htags
    have hseamid := taggedSum_insert_eq P k hkn d hc1 hc2 tags f α
    have hkmem : P.pts k ∈ Icc a b := cptk_mem P k hkn
    have hk1mem : P.pts (k + 1) ∈ Icc a b := cptk1_mem P k hkn
    have hdmem : d ∈ Icc a b := c_mem P k hkn d hc1 hc2
    have hΔ_nn : 0 ≤ α (P.pts (k + 1)) - α (P.pts k) :=
      sub_nonneg.mpr (hmono hkmem hk1mem (le_of_lt (lt_trans hc1 hc2)))
    have hΔ_le : α (P.pts (k + 1)) - α (P.pts k) ≤ A :=
      alpha_gap_le_total P hkn hmono
    -- |f(tags k) - f d| < eta via f-continuity
    have htagk_mem : tags k ∈ subinterval P k := htags k hkn
    have htagk_dist : |tags k - d| ≤ P.mesh :=
      crossing_point_dist_le P hkn hc1 hc2 htagk_mem
    have hfclose : |f (tags k) - f d| < eta := by
      have hdist : dist (tags k) d < δ₃ := by
        rw [Real.dist_eq]; exact lt_of_le_of_lt htagk_dist hmesh₃
      have hh := Hδ₃ hdist
      rw [Real.dist_eq] at hh; exact hh
    have hseam_diff : taggedSum P tags f α - taggedSum P' tags' f α
        = (f (tags k) - f d) * (α (P.pts (k + 1)) - α (P.pts k)) := by
      rw [hseamid]; ring
    have hseam_bound : |taggedSum P tags f α - taggedSum P' tags' f α| ≤ eta * A := by
      rw [hseam_diff, abs_mul, abs_of_nonneg hΔ_nn]
      calc
        |f (tags k) - f d| * (α (P.pts (k + 1)) - α (P.pts k))
            ≤ eta * (α (P.pts (k + 1)) - α (P.pts k)) :=
          mul_le_mul_of_nonneg_right (le_of_lt hfclose) hΔ_nn
        _ ≤ eta * A := mul_le_mul_of_nonneg_left hΔ_le (le_of_lt heta_pos)
    have hetaA : eta * A < eps / 2 := by
      rw [heta]
      rw [show eps / (4 * (A + 1)) * A = (A / (A + 1)) * (eps / 4) from by
        rw [div_mul_eq_mul_div, div_mul_div_comm]; ring_nf]
      have hratio : A / (A + 1) < 1 := by rw [div_lt_one hA1pos]; linarith
      have hq : 0 < eps / 4 := by positivity
      nlinarith [mul_lt_mul_of_pos_right hratio hq]
    -- split P' at k+1
    have hdgrid : P'.pts (k + 1) = d := insertPoint_pts_seam P k hkn d hc1 hc2
    have hk1pos : 0 < k + 1 := by omega
    have hk1n : k + 1 < P'.n := by have : P'.n = P.n + 1 := rfl; omega
    have hsplitP' := taggedSum_split P' (k + 1) hk1pos hk1n d hdgrid tags' f α
    set Q₁ := splitLeft P' (k + 1) hk1pos (le_of_lt hk1n) d hdgrid with hQ₁
    set Q₂ := splitRight P' (k + 1) hk1n d hdgrid with hQ₂
    have htQ₁ : tagsInPartition Q₁ tags' :=
      tagsInPartition_splitLeft P' (k + 1) hk1pos hk1n d hdgrid tags' ht'
    have htQ₂ : tagsInPartition Q₂ (fun j => tags' (k + 1 + j)) :=
      tagsInPartition_splitRight P' (k + 1) hk1n d hdgrid tags' ht'
    have hmQ₁ : Q₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₁
    have hmQ₂ : Q₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₂
    have hbQ₁ := H₁ Q₁ tags' htQ₁ hmQ₁
    have hbQ₂ := H₂ Q₂ (fun j => tags' (k + 1 + j)) htQ₂ hmQ₂
    have hP'split_bound : |taggedSum P' tags' f α - (L₁ + L₂)| < eps / 2 := by
      rw [hsplitP']
      have : taggedSum Q₁ tags' f α + taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - (L₁ + L₂)
          = (taggedSum Q₁ tags' f α - L₁)
            + (taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - L₂) := by ring
      rw [this]
      calc
        |(taggedSum Q₁ tags' f α - L₁)
          + (taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - L₂)|
            ≤ |taggedSum Q₁ tags' f α - L₁|
              + |taggedSum Q₂ (fun j => tags' (k + 1 + j)) f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hbQ₁ hbQ₂
        _ = eps / 2 := by ring
    have hfinal : |taggedSum P tags f α - (L₁ + L₂)| < eps := by
      have hsplit_eq : taggedSum P tags f α - (L₁ + L₂)
          = (taggedSum P tags f α - taggedSum P' tags' f α)
            + (taggedSum P' tags' f α - (L₁ + L₂)) := by ring
      rw [hsplit_eq]
      calc
        |(taggedSum P tags f α - taggedSum P' tags' f α)
          + (taggedSum P' tags' f α - (L₁ + L₂))|
            ≤ |taggedSum P tags f α - taggedSum P' tags' f α|
              + |taggedSum P' tags' f α - (L₁ + L₂)| := abs_add_le _ _
        _ < eps / 2 + eps / 2 := by
          apply add_lt_add_of_le_of_lt _ hP'split_bound
          exact le_of_lt (lt_of_le_of_lt hseam_bound hetaA)
        _ = eps := by ring
    exact hfinal

/-! ## The upper/lower common limit glues across `d` (α-continuous branch). -/

theorem upperLowerCommonLimit_glue_alpha {a d b : ℝ} {f α : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a d f α L₁) (h₂ : UpperLowerCommonLimit d b f α L₂)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    UpperLowerCommonLimit a b f α (L₁ + L₂) := by
  obtain ⟨hs₁, hlim₁⟩ := h₁
  obtain ⟨hs₂, hlim₂⟩ := h₂
  have hs : SourceHypotheses a b f α := sourceHypotheses_glue ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
    ⟨hs₂.1, hs₂.2.1, hs₂.2.2.1, hs₂.2.2.2⟩
  obtain ⟨hab, hAbove, hBelow, hmono⟩ := hs
  refine ⟨⟨hab, hAbove, hBelow, hmono⟩, ?_⟩
  intro eps heps
  set Ω := Omega f a b with hΩ
  have hΩnn : 0 ≤ Ω := omega_nonneg hab hAbove hBelow
  have hquarter : 0 < eps / 4 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hlim₁ (eps / 4) hquarter
  obtain ⟨δ₂, hδ₂, H₂⟩ := hlim₂ (eps / 4) hquarter
  set epsp : ℝ := eps / (4 * (Ω + 1)) with hepsp
  have hΩ1pos : 0 < Ω + 1 := by linarith
  have hepsp_pos : 0 < epsp := by rw [hepsp]; positivity
  obtain ⟨δ₃, hδ₃, Hδ₃⟩ := Metric.continuousAt_iff.mp hαd epsp hepsp_pos
  refine ⟨min (min δ₁ δ₂) δ₃, by positivity, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmesh₂ : P.mesh < δ₂ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmesh₃ : P.mesh < δ₃ := lt_of_lt_of_le hmesh (min_le_right _ _)
  rcases locate_point P had hdb with ⟨k, hk0, hkn, hpk⟩ | ⟨k, hkn, hc1, hc2⟩
  · -- d is a grid point
    set P₁ := splitLeft P k hk0 (le_of_lt hkn) d hpk with hP₁
    set P₂ := splitRight P k hkn d hpk with hP₂
    have hm₁ : P₁.mesh < δ₁ := lt_of_le_of_lt (mesh_splitLeft_le P k hk0 hkn d hpk) hmesh₁
    have hm₂ : P₂.mesh < δ₂ := lt_of_le_of_lt (mesh_splitRight_le P k hk0 hkn d hpk) hmesh₂
    have hb₁ := H₁ P₁ hm₁
    have hb₂ := H₂ P₂ hm₂
    constructor
    · rw [upperSum_split P k hk0 hkn d hpk f α]
      have heq : upperSum P₁ f α + upperSum P₂ f α - (L₁ + L₂)
          = (upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂)|
            ≤ |upperSum P₁ f α - L₁| + |upperSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.1 hb₂.1
        _ < eps := by linarith
    · rw [lowerSum_split P k hk0 hkn d hpk f α]
      have heq : lowerSum P₁ f α + lowerSum P₂ f α - (L₁ + L₂)
          = (lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂)|
            ≤ |lowerSum P₁ f α - L₁| + |lowerSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.2 hb₂.2
        _ < eps := by linarith
  · -- interior cell: insert d
    set P' := insertPoint P k hkn d hc1 hc2 with hP'
    have hmeshP' : P'.mesh < min (min δ₁ δ₂) δ₃ :=
      lt_of_le_of_lt (mesh_insert_le P k hkn d hc1 hc2) hmesh
    have hmeshP'₁ : P'.mesh < δ₁ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_left _ _))
    have hmeshP'₂ : P'.mesh < δ₂ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_right _ _))
    -- Δα bound
    have hkmem : P.pts k ∈ Icc a b := cptk_mem P k hkn
    have hk1mem : P.pts (k + 1) ∈ Icc a b := cptk1_mem P k hkn
    have hdmem : d ∈ Icc a b := c_mem P k hkn d hc1 hc2
    have hgapk : P.pts (k + 1) - P.pts k ≤ P.mesh := partition_length_le_mesh P hkn
    have hdL_lt : α d - α (P.pts k) < epsp := by
      have hdist : dist (P.pts k) d < δ₃ := by
        rw [Real.dist_eq]
        have : |P.pts k - d| ≤ P.mesh := by
          rw [abs_le]; constructor <;> [nlinarith [le_of_lt hc2]; nlinarith [le_of_lt hc1]]
        exact lt_of_le_of_lt this hmesh₃
      have hh := Hδ₃ hdist
      rw [Real.dist_eq] at hh
      have h := (abs_lt.mp hh).1
      linarith
    have hdR_lt : α (P.pts (k + 1)) - α d < epsp := by
      have hdist : dist (P.pts (k + 1)) d < δ₃ := by
        rw [Real.dist_eq]
        have : |P.pts (k + 1) - d| ≤ P.mesh := by
          rw [abs_le]; constructor <;> [nlinarith [le_of_lt hc1]; nlinarith [le_of_lt hc2]]
        exact lt_of_le_of_lt this hmesh₃
      have hh := Hδ₃ hdist
      rw [Real.dist_eq] at hh
      have h := (abs_lt.mp hh).2
      linarith
    have hdL_nn : 0 ≤ α d - α (P.pts k) :=
      sub_nonneg.mpr (hmono hkmem hdmem (le_of_lt hc1))
    have hdR_nn : 0 ≤ α (P.pts (k + 1)) - α d :=
      sub_nonneg.mpr (hmono hdmem hk1mem (le_of_lt hc2))
    have hΔ_lt : α (P.pts (k + 1)) - α (P.pts k) < 2 * epsp := by linarith
    have hΔ_nn : 0 ≤ α (P.pts (k + 1)) - α (P.pts k) := by linarith
    -- oscillation bound M_k - m_k ≤ Ω
    have hosc : upperStep P f k - lowerStep P f k ≤ Ω :=
      cell_osc_le_omega P hkn hAbove hBelow
    have hOmega2epsp : Ω * (2 * epsp) < eps / 2 := by
      rw [hepsp]
      rw [show Ω * (2 * (eps / (4 * (Ω + 1)))) = (Ω / (Ω + 1)) * (eps / 2) from by
        field_simp; ring]
      have hratio : Ω / (Ω + 1) < 1 := by rw [div_lt_one hΩ1pos]; linarith
      nlinarith [mul_pos (show (0:ℝ) < eps / 2 by positivity) (show (0:ℝ) < 1 by norm_num)]
    -- change-bound → Ω·2εp
    have hchU : |upperSum P f α - upperSum P' f α| < eps / 2 := by
      have hb := abs_upperSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
          ≤ Ω * (2 * epsp) := by
        calc
          (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
              ≤ Ω * (α (P.pts (k + 1)) - α (P.pts k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ Ω * (2 * epsp) := mul_le_mul_of_nonneg_left (le_of_lt hΔ_lt) hΩnn
      exact lt_of_le_of_lt (le_trans hb hchain) hOmega2epsp
    have hchL : |lowerSum P f α - lowerSum P' f α| < eps / 2 := by
      have hb := abs_lowerSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
          ≤ Ω * (2 * epsp) := by
        calc
          (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
              ≤ Ω * (α (P.pts (k + 1)) - α (P.pts k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ Ω * (2 * epsp) := mul_le_mul_of_nonneg_left (le_of_lt hΔ_lt) hΩnn
      exact lt_of_le_of_lt (le_trans hb hchain) hOmega2epsp
    -- split P' at k+1 (grid point d)
    have hdgrid : P'.pts (k + 1) = d := insertPoint_pts_seam P k hkn d hc1 hc2
    have hk1pos : 0 < k + 1 := by omega
    have hk1n : k + 1 < P'.n := by have : P'.n = P.n + 1 := rfl; omega
    set Q₁ := splitLeft P' (k + 1) hk1pos (le_of_lt hk1n) d hdgrid with hQ₁
    set Q₂ := splitRight P' (k + 1) hk1n d hdgrid with hQ₂
    have hmQ₁ : Q₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₁
    have hmQ₂ : Q₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₂
    have hbQ₁ := H₁ Q₁ hmQ₁
    have hbQ₂ := H₂ Q₂ hmQ₂
    constructor
    · -- upper
      have hP'bound : |upperSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [upperSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : upperSum Q₁ f α + upperSum Q₂ f α - (L₁ + L₂)
            = (upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂)|
              ≤ |upperSum Q₁ f α - L₁| + |upperSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.1 hbQ₂.1
          _ = eps / 2 := by ring
      have heq : upperSum P f α - (L₁ + L₂)
          = (upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂))|
            ≤ |upperSum P f α - upperSum P' f α| + |upperSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchU hP'bound
        _ = eps := by ring
    · -- lower
      have hP'bound : |lowerSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [lowerSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : lowerSum Q₁ f α + lowerSum Q₂ f α - (L₁ + L₂)
            = (lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂)|
              ≤ |lowerSum Q₁ f α - L₁| + |lowerSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.2 hbQ₂.2
          _ = eps / 2 := by ring
      have heq : lowerSum P f α - (L₁ + L₂)
          = (lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂))|
            ≤ |lowerSum P f α - lowerSum P' f α| + |lowerSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchL hP'bound
        _ = eps := by ring

/-! ## The upper/lower common limit glues across `d` (f-continuous branch). -/

theorem upperLowerCommonLimit_glue_f {a d b : ℝ} {f α : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a d f α L₁) (h₂ : UpperLowerCommonLimit d b f α L₂)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    UpperLowerCommonLimit a b f α (L₁ + L₂) := by
  obtain ⟨hs₁, hlim₁⟩ := h₁
  obtain ⟨hs₂, hlim₂⟩ := h₂
  have hs : SourceHypotheses a b f α := sourceHypotheses_glue ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
    ⟨hs₂.1, hs₂.2.1, hs₂.2.2.1, hs₂.2.2.2⟩
  obtain ⟨hab, hAbove, hBelow, hmono⟩ := hs
  refine ⟨⟨hab, hAbove, hBelow, hmono⟩, ?_⟩
  intro eps heps
  set A : ℝ := α b - α a with hA
  have hAnn : 0 ≤ A := by
    rw [hA]; have := hmono (⟨le_rfl, le_of_lt hab⟩ : a ∈ Icc a b)
      (⟨hab.le, le_rfl⟩ : b ∈ Icc a b) hab.le; linarith
  have hA1pos : 0 < A + 1 := by linarith
  have hquarter : 0 < eps / 4 := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hlim₁ (eps / 4) hquarter
  obtain ⟨δ₂, hδ₂, H₂⟩ := hlim₂ (eps / 4) hquarter
  set eta : ℝ := eps / (4 * (A + 1)) with heta
  have heta_pos : 0 < eta := by rw [heta]; positivity
  obtain ⟨δ₃, hδ₃, Hδ₃⟩ := Metric.continuousAt_iff.mp hfd eta heta_pos
  refine ⟨min (min δ₁ δ₂) δ₃, by positivity, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmesh₂ : P.mesh < δ₂ :=
    lt_of_lt_of_le hmesh (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmesh₃ : P.mesh < δ₃ := lt_of_lt_of_le hmesh (min_le_right _ _)
  rcases locate_point P had hdb with ⟨k, hk0, hkn, hpk⟩ | ⟨k, hkn, hc1, hc2⟩
  · -- grid point
    set P₁ := splitLeft P k hk0 (le_of_lt hkn) d hpk with hP₁
    set P₂ := splitRight P k hkn d hpk with hP₂
    have hm₁ : P₁.mesh < δ₁ := lt_of_le_of_lt (mesh_splitLeft_le P k hk0 hkn d hpk) hmesh₁
    have hm₂ : P₂.mesh < δ₂ := lt_of_le_of_lt (mesh_splitRight_le P k hk0 hkn d hpk) hmesh₂
    have hb₁ := H₁ P₁ hm₁
    have hb₂ := H₂ P₂ hm₂
    constructor
    · rw [upperSum_split P k hk0 hkn d hpk f α]
      have heq : upperSum P₁ f α + upperSum P₂ f α - (L₁ + L₂)
          = (upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(upperSum P₁ f α - L₁) + (upperSum P₂ f α - L₂)|
            ≤ |upperSum P₁ f α - L₁| + |upperSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.1 hb₂.1
        _ < eps := by linarith
    · rw [lowerSum_split P k hk0 hkn d hpk f α]
      have heq : lowerSum P₁ f α + lowerSum P₂ f α - (L₁ + L₂)
          = (lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂) := by ring
      rw [heq]
      calc
        |(lowerSum P₁ f α - L₁) + (lowerSum P₂ f α - L₂)|
            ≤ |lowerSum P₁ f α - L₁| + |lowerSum P₂ f α - L₂| := abs_add_le _ _
        _ < eps / 4 + eps / 4 := add_lt_add hb₁.2 hb₂.2
        _ < eps := by linarith
  · -- interior cell
    set P' := insertPoint P k hkn d hc1 hc2 with hP'
    have hmeshP' : P'.mesh < min (min δ₁ δ₂) δ₃ :=
      lt_of_le_of_lt (mesh_insert_le P k hkn d hc1 hc2) hmesh
    have hmeshP'₁ : P'.mesh < δ₁ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_left _ _))
    have hmeshP'₂ : P'.mesh < δ₂ :=
      lt_of_lt_of_le hmeshP' (le_trans (min_le_left _ _) (min_le_right _ _))
    have hΔ_nn : 0 ≤ α (P.pts (k + 1)) - α (P.pts k) :=
      sub_nonneg.mpr (hmono (cptk_mem P k hkn) (cptk1_mem P k hkn)
        (le_of_lt (lt_trans hc1 hc2)))
    have hΔ_le : α (P.pts (k + 1)) - α (P.pts k) ≤ A := alpha_gap_le_total P hkn hmono
    -- crossing-cell f-closeness ⇒ M_k - m_k ≤ 2η
    have hclose : ∀ x ∈ subinterval P k, |f x - f d| ≤ eta := by
      intro x hx
      have hxdist : |x - d| ≤ P.mesh := crossing_point_dist_le P hkn hc1 hc2 hx
      have hdist : dist x d < δ₃ := by
        rw [Real.dist_eq]; exact lt_of_le_of_lt hxdist hmesh₃
      have hh := Hδ₃ hdist
      rw [Real.dist_eq] at hh; exact le_of_lt hh
    have hosc : upperStep P f k - lowerStep P f k ≤ 2 * eta :=
      cell_osc_le_of_close P hkn hclose
    have h2etaA : (2 * eta) * A < eps / 2 := by
      rw [heta]
      have hne : (A + 1) ≠ 0 := by positivity
      have hid : 2 * (eps / (4 * (A + 1))) * A = (A / (A + 1)) * (eps / 2) := by
        field_simp
        ring
      rw [hid]
      have hratio : A / (A + 1) < 1 := by rw [div_lt_one hA1pos]; linarith
      have hq : 0 < eps / 2 := by positivity
      nlinarith [mul_lt_mul_of_pos_right hratio hq]
    have hchU : |upperSum P f α - upperSum P' f α| < eps / 2 := by
      have hb := abs_upperSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
          ≤ (2 * eta) * A := by
        calc
          (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
              ≤ (2 * eta) * (α (P.pts (k + 1)) - α (P.pts k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ (2 * eta) * A := mul_le_mul_of_nonneg_left hΔ_le (by positivity)
      exact lt_of_le_of_lt (le_trans hb hchain) h2etaA
    have hchL : |lowerSum P f α - lowerSum P' f α| < eps / 2 := by
      have hb := abs_lowerSum_insert_le P k hkn d hc1 hc2 f α hAbove hBelow hmono
      have hchain : (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
          ≤ (2 * eta) * A := by
        calc
          (upperStep P f k - lowerStep P f k) * (α (P.pts (k + 1)) - α (P.pts k))
              ≤ (2 * eta) * (α (P.pts (k + 1)) - α (P.pts k)) :=
            mul_le_mul_of_nonneg_right hosc hΔ_nn
          _ ≤ (2 * eta) * A := mul_le_mul_of_nonneg_left hΔ_le (by positivity)
      exact lt_of_le_of_lt (le_trans hb hchain) h2etaA
    have hdgrid : P'.pts (k + 1) = d := insertPoint_pts_seam P k hkn d hc1 hc2
    have hk1pos : 0 < k + 1 := by omega
    have hk1n : k + 1 < P'.n := by have : P'.n = P.n + 1 := rfl; omega
    set Q₁ := splitLeft P' (k + 1) hk1pos (le_of_lt hk1n) d hdgrid with hQ₁
    set Q₂ := splitRight P' (k + 1) hk1n d hdgrid with hQ₂
    have hmQ₁ : Q₁.mesh < δ₁ :=
      lt_of_le_of_lt (mesh_splitLeft_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₁
    have hmQ₂ : Q₂.mesh < δ₂ :=
      lt_of_le_of_lt (mesh_splitRight_le P' (k + 1) hk1pos hk1n d hdgrid) hmeshP'₂
    have hbQ₁ := H₁ Q₁ hmQ₁
    have hbQ₂ := H₂ Q₂ hmQ₂
    constructor
    · have hP'bound : |upperSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [upperSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : upperSum Q₁ f α + upperSum Q₂ f α - (L₁ + L₂)
            = (upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(upperSum Q₁ f α - L₁) + (upperSum Q₂ f α - L₂)|
              ≤ |upperSum Q₁ f α - L₁| + |upperSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.1 hbQ₂.1
          _ = eps / 2 := by ring
      have heq : upperSum P f α - (L₁ + L₂)
          = (upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(upperSum P f α - upperSum P' f α) + (upperSum P' f α - (L₁ + L₂))|
            ≤ |upperSum P f α - upperSum P' f α| + |upperSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchU hP'bound
        _ = eps := by ring
    · have hP'bound : |lowerSum P' f α - (L₁ + L₂)| < eps / 2 := by
        rw [lowerSum_split P' (k + 1) hk1pos hk1n d hdgrid f α]
        have heq : lowerSum Q₁ f α + lowerSum Q₂ f α - (L₁ + L₂)
            = (lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂) := by ring
        rw [heq]
        calc
          |(lowerSum Q₁ f α - L₁) + (lowerSum Q₂ f α - L₂)|
              ≤ |lowerSum Q₁ f α - L₁| + |lowerSum Q₂ f α - L₂| := abs_add_le _ _
          _ < eps / 4 + eps / 4 := add_lt_add hbQ₁.2 hbQ₂.2
          _ = eps / 2 := by ring
      have heq : lowerSum P f α - (L₁ + L₂)
          = (lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂)) := by ring
      rw [heq]
      calc
        |(lowerSum P f α - lowerSum P' f α) + (lowerSum P' f α - (L₁ + L₂))|
            ≤ |lowerSum P f α - lowerSum P' f α| + |lowerSum P' f α - (L₁ + L₂)| :=
          abs_add_le _ _
        _ < eps / 2 + eps / 2 := add_lt_add hchL hP'bound
        _ = eps := by ring

/-! ## Final assembly: integrability and the value identity. -/

/-- The witness gluing two RS integrals across `d` (α-continuous branch). -/
noncomputable def rsIntegralWitness_glue_alpha {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    RSIntegralWitness f α a b where
  value := rsIntegral f α a d hac + rsIntegral f α d b hcb
  source_limit :=
    upperLowerCommonLimit_glue_alpha (rsIntegral_source_spec hac)
      (rsIntegral_source_spec hcb) hαd had hdb
  tagged_limit :=
    taggedCommonLimit_glue_alpha (rsIntegral_spec hac)
      (rsIntegral_spec hcb) hαd had hdb

noncomputable def rsIntegrable_glue_alpha {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    RSIntegrable f α a b :=
  ⟨rsIntegralWitness_glue_alpha hac hcb hαd had hdb⟩

theorem rsIntegral_glue_alpha {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hαd : ContinuousAt α d) (had : a < d) (hdb : d < b) :
    rsIntegral f α a b (rsIntegrable_glue_alpha hac hcb hαd had hdb)
      = rsIntegral f α a d hac + rsIntegral f α d b hcb :=
  DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_glue_alpha hac hcb hαd had hdb))
    (taggedCommonLimit_glue_alpha (rsIntegral_spec hac) (rsIntegral_spec hcb) hαd had hdb)

/-- The witness gluing two RS integrals across `d` (f-continuous branch). -/
noncomputable def rsIntegralWitness_glue_f {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    RSIntegralWitness f α a b where
  value := rsIntegral f α a d hac + rsIntegral f α d b hcb
  source_limit :=
    upperLowerCommonLimit_glue_f (rsIntegral_source_spec hac)
      (rsIntegral_source_spec hcb) hfd had hdb
  tagged_limit :=
    taggedCommonLimit_glue_f (rsIntegral_spec hac)
      (rsIntegral_spec hcb) hfd had hdb

noncomputable def rsIntegrable_glue_f {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    RSIntegrable f α a b :=
  ⟨rsIntegralWitness_glue_f hac hcb hfd had hdb⟩

theorem rsIntegral_glue_f {f α : ℝ → ℝ} {a d b : ℝ}
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hfd : ContinuousAt f d) (had : a < d) (hdb : d < b) :
    rsIntegral f α a b (rsIntegrable_glue_f hac hcb hfd had hdb)
      = rsIntegral f α a d hac + rsIntegral f α d b hcb :=
  DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_glue_f hac hcb hfd had hdb))
    (taggedCommonLimit_glue_f (rsIntegral_spec hac) (rsIntegral_spec hcb) hfd had hdb)

/-- Item 4 of Theorem 1.2: integrability and additivity across an interior split
point `d`, under continuity of `α` or `f` at `d`. -/
theorem rsIntegral_glue {f α : ℝ → ℝ} {a d b : ℝ}
    (had : a < d) (hdb : d < b)
    (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b)
    (hcont : ContinuousAt α d ∨ ContinuousAt f d) :
    ∃ hab : RSIntegrable f α a b,
      rsIntegral f α a b hab = rsIntegral f α a d hac + rsIntegral f α d b hcb := by
  rcases hcont with hαd | hfd
  · exact ⟨rsIntegrable_glue_alpha hac hcb hαd had hdb,
      rsIntegral_glue_alpha hac hcb hαd had hdb⟩
  · exact ⟨rsIntegrable_glue_f hac hcb hfd had hdb,
      rsIntegral_glue_f hac hcb hfd had hdb⟩

end Thm12Item4

/-- The standard algebraic laws for the finite-interval Riemann--Stieltjes
integral from Theorem 1.2, stated for the partition-based definition exported
by `def_1_2`. Item 4 (interval additivity across an interior split point `d`)
is proved under continuity of the integrator `α` or the integrand `f` at `d`,
following the certified Darboux/tagged skeleton. -/
theorem thm_1_2 {f g α : ℝ → ℝ} {c a b : ℝ} :
    (∀ (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b),
      ∃ hfg : RSIntegrable (fun x => f x + g x) α a b,
        rsIntegral (fun x => f x + g x) α a b hfg =
          rsIntegral f α a b hf + rsIntegral g α a b hg) ∧
    (∀ (hf : RSIntegrable f α a b),
      ∃ hcf : RSIntegrable (fun x => c * f x) α a b,
        rsIntegral (fun x => c * f x) α a b hcf =
          c * rsIntegral f α a b hf) ∧
    (∀ (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b),
      (∀ x ∈ Icc a b, f x ≤ g x) →
        rsIntegral f α a b hf ≤ rsIntegral g α a b hg) ∧
    (∀ (d : ℝ), a < d → d < b →
      ∀ (hac : RSIntegrable f α a d) (hcb : RSIntegrable f α d b),
        (ContinuousAt α d ∨ ContinuousAt f d) →
        ∃ hab : RSIntegrable f α a b,
          rsIntegral f α a b hab = rsIntegral f α a d hac + rsIntegral f α d b hcb) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf hg
    exact ⟨rsIntegrable_integrand_add hf hg, rsIntegral_integrand_add hf hg⟩
  · intro hf
    exact ⟨rsIntegrable_integrand_const_mul (c := c) hf,
      rsIntegral_integrand_const_mul (c := c) hf⟩
  · intro hf hg hfg
    exact rsIntegral_integrand_mono hf hg hfg
  · intro d had hdb hac hcb hcont
    exact Thm12Item4.rsIntegral_glue had hdb hac hcb hcont
