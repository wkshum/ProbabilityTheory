import Mathlib.Analysis.InnerProductSpace.Basic

open Finset BigOperators

open Set
open scoped Pointwise
open scoped Classical


noncomputable section

/-
  # Riemann-Stielgjes integral ∫ f dα
-/

/--
The function `f` is called the *integrand*, and the function
`alpha` is called the *integrator*.

The standing textbook hypotheses on `f` and `alpha`
from the paragraphs preceding Definition 1.2:

We assume that
* `a` is less than `b`.
* Function `f` is bounded from above in the interval [a,b]
* Function `f` is bounded from below in the interval [a,b]
* Function `alpha` is monotonically increasing in [a,b]

-/
def SourceHypotheses (a b : ℝ) (f alpha : ℝ → ℝ) : Prop :=
  a < b ∧
  BddAbove (f '' Set.Icc a b) ∧
  BddBelow (f '' Set.Icc a b) ∧
  MonotoneOn alpha (Set.Icc a b)


/-- A partition is a list of increasing numbers
`a = x_0 < x_1 < ... < x_n = b`.

We represent a partition by a structure.
`n` is the number of points
`hn` is an evidence that `n` is larger than 0
`pts` is the list of points
`pts_start` is the first point
`pts_end` is the last point
`strict_mono` is the hypothesis that the points are strictly increasing
-/
structure Partition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : Fin (n + 1) → ℝ
  pts_start : pts 0 = a
  pts_end : pts (Fin.last n) = b
  strict_mono : StrictMono pts


/-- The mesh  of a partition is the larges gap between
consecutive points in a partition.

We define it as `max_i (x_{i+1} - x_i)`, for i = 0,1,...,n-1.
-/
def Partition.mesh {a b : ℝ} (P : Partition a b) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin P.n))
    ⟨⟨0, P.hn⟩, Finset.mem_univ _⟩
    fun i => P.pts i.succ - P.pts i.castSucc

/-- The i-th closed subinterval `[x_i, x_{i+1}]` in a partition `P`

We note that the points in a partitioned are indexed by Fin (n+1),
the sub-intervals in a partitioned are indexed by Fin n.

There are n+1 points in a partition, but there are n sub-intervals.
-/
def Partition.subinterval {a b : ℝ} (P : Partition a b) (i : Fin P.n)
  : Set ℝ :=
  Set.Icc (P.pts i.castSucc) (P.pts i.succ)

/--
The value `M_i = sup { f x : x_i <= x <= x_{i+1} }`
is the supremum of function `f` in the i-th subinterval
-/
def upperStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sSup (f '' Partition.subinterval P i)

/--
The value `m_i = inf { f x : x_i <= x <= x_{i+1} }`.
is the infimum of function `f` in the i-th subinterval
 -/
def lowerStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sInf (f '' Partition.subinterval P i)


open scoped BigOperators

/-- A *tagged* Riemann-Stieltjes sum over a partition is a sum
\sum_i f(t_i) ( alpha(x_{i+1}) - alpha(x_{i}) )

where t_i is a number in the range of f.

A tagged sum will be represented by `taggedSum P tags f alpha`.
-/
def taggedSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    f (tags i) * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

/-- The condition that tags are chosen in the corresponding partition subintervals. -/
def tagsInPartition {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.n, tags i ∈ Partition.subinterval P i

/-- Tags chosen in the corresponding partition subintervals.
  This is how we can use this definition in the future.
-/
example {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) :
  tagsInPartition P tags ↔ ∀ i : Fin P.n, tags i ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ)
  := by rfl


/-- The upper Riemann-Stieltjes sum `U(P,f,alpha)`.
-/
def upperSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    upperStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

/-- The lower Riemann-Stieltjes sum `L(P,f,alpha)`.
-/
def lowerSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    lowerStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))


/-- The condition that upper and lower sums converge to the same
limit as mesh goes to zero. -/
def UpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b,
      P.mesh < delta →
        |upperSum P f alpha - L| < eps ∧ |lowerSum P f alpha - L| < eps

/-- Riemann-Stieltjes integrability on `[a,b]` with respect to `alpha`.

  RS integral of `f` with respect to `alpha` exists if the upper
  and lower limit coincide.
-/
def RSIntegrableOnInterval (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, UpperLowerCommonLimit a b f alpha L





/- Tagged-sum convergence over the same source partition interface.
This is the local tagged formulation of the Riemann--Stieltjes sum
introduced just before Definition 1.2.

This condition says that, provided the tags are chosen in the respective
intevals and the mesh converge to zero, then the tagged sum converges to L
-/
def TaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b, ∀ tags : Fin P.n → ℝ,
      tagsInPartition P tags →
      P.mesh < delta →
      |taggedSum P tags f alpha - L| < eps


/-- Common upper/lower-sum limit semantics from Definition 1.2. -/
def rsUpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  UpperLowerCommonLimit a b f alpha L

/-- Tagged-sum semantics exposed by the existing finite-interval RS core. -/
def rsTaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  TaggedCommonLimit a b f alpha L



/--  Package for the Definition 1.2 integral value.

The textbook definition is the Darboux upper/lower common-limit criterion. We call it
the `source_limit`.

The same section also introduces another Riemann-Stieltjes sum S(P, f, alpha),
called `tagged_limit`.

A *witness* of RS integral is the common `value` of the Darboux limit and tagged limit.
-/
structure RSIntegralWitness (f alpha : ℝ → ℝ) (a b : ℝ) where
  value : ℝ
  source_limit : rsUpperLowerCommonLimit a b f alpha value
  tagged_limit : rsTaggedCommonLimit a b f alpha value


/-- `f` is Riemann-Stieltjes integrable on `[a,b]` with respect to `alpha`
  if the type `RSIntegralWitness f alpha a b` is nonempty
-/
def RSIntegrable (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  Nonempty (RSIntegralWitness f alpha a b)

/-- The value of the finite-interval Riemann-Stieltjes integral
  after integrability is known. -/
noncomputable def rsIntegral (f alpha : ℝ → ℝ) (a b : ℝ)
    (h : RSIntegrable f alpha a b) : ℝ :=
  (Classical.choice h).value

/-- The chosen integral value satisfies the source upper/lower common-limit criterion. -/
theorem rsIntegral_source_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).source_limit

/-- The chosen integral value also satisfies the existing tagged-sum criterion. -/
theorem rsIntegral_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).tagged_limit

/-- We pack the previous two theorems together as a single theorem -/
theorem rsIntegral_source_and_tagged_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) ∧
      rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  ⟨rsIntegral_source_spec h, rsIntegral_spec h⟩


/-- # Definition 1.2 Riemann-Stieltjes integrable function
Exported statement of Definition 1.2. -/
def def_1_2 (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  RSIntegrable f alpha a b


/-- The family `R(alpha)` of functions integrable with respect to
  `alpha` on `[a,b]`. -/
def rsIntegrableFamily (alpha : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrable f alpha a b}





namespace DarbouxRS

/-
 Some helper lemmas
-/

/-
 If α₁ and α₂ are monotonic, then α₁ + α₂ is also monotonic
-/
theorem sourceHypotheses_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    (h₁ : SourceHypotheses a b f α₁)
    (h₂ : SourceHypotheses a b f α₂) :
    SourceHypotheses a b f (fun x => α₁ x + α₂ x) := by
  rcases h₁ with ⟨hab, hAbove, hBelow, hmono₁⟩
  rcases h₂ with ⟨_hab₂, _hAbove₂, _hBelow₂, hmono₂⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  exact add_le_add (hmono₁ hx hy hxy) (hmono₂ hx hy hxy)

/-
Additivity of upper sum when α can be decomposed as α₁ + α₂
-/
theorem upperSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    upperSum P f (fun x => α₁ x + α₂ x) =
      upperSum P f α₁ + upperSum P f α₂ := by
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-
Additivity of lower sum when α can be decomposed as α₁ + α₂
-/
theorem lowerSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    lowerSum P f (fun x => α₁ x + α₂ x) =
      lowerSum P f α₁ + lowerSum P f α₂ := by
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-
Additivity of tagged sum when α can be decomposed as α₁ + α₂
-/
theorem taggedSum_integrator_add {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f α₁ α₂ : ℝ → ℝ) :
    taggedSum P tags f (fun x => α₁ x + α₂ x) =
      taggedSum P tags f α₁ + taggedSum P tags f α₂ := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring


/-- Uniform partitions of `[a,b]`.

This provides arbitrarily small mesh partitions for the limit in
Definition 1.2 -/
def uniformPartition (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Partition a b where
  n := n
  hn := hn
  pts := fun i => a + ((i : ℝ) / (n : ℝ)) * (b - a)
  pts_start := by simp
  pts_end := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    -- Explicitly change the Fin coercion to expose its integer value
    change a + ((Fin.last n).val : ℝ) / (n : ℝ) * (b - a) = b
    rw [Fin.val_last]
    field_simp [hn0]
    ring
  strict_mono := by
    -- StrictMono means ∀ i j, i < j → pts i < pts j
    intro i j hij
    dsimp
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hba : 0 < b - a := sub_pos.mpr hab
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij

    -- Step 1: i < j  ==>  i / n < j / n
    have h1 : (i : ℝ) / (n : ℝ) < (j : ℝ) / (n : ℝ) := by
      exact mul_lt_mul_of_pos_right hijR (inv_pos.mpr hnR)

    -- Step 2: i / n * (b - a) < j / n * (b - a)
    have h2 : ((i : ℝ) / (n : ℝ)) * (b - a) < ((j : ℝ) / (n : ℝ)) * (b - a) :=
      mul_lt_mul_of_pos_right h1 hba

    -- Step 3: a + ... < a + ...
    linarith [h2]


/-
 The sub-intervals in a uniform partition have length (b-a)/n.
-/
theorem uniformPartition_mesh_eq (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    (uniformPartition a b hab n hn).mesh = (b - a) / (n : ℝ) := by
  unfold Partition.mesh uniformPartition
  apply Finset.sup'_eq_of_forall
  intro i hi
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hnR]
  ring


/-
 Using the uniform partition, we can show that for any delta > 0,
 there is a partition with mesh less than delta.
-/
theorem exists_partition_mesh_lt {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : Partition a b, P.mesh < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  let N := n + 1
  have hNpos : 0 < N := Nat.succ_pos n
  refine ⟨uniformPartition a b hab N hNpos, ?_⟩
  rw [uniformPartition_mesh_eq]
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hltN : (b - a) / δ < (N : ℝ) := by
    have hnle : (n : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self n
    exact lt_trans hn hnle
  have hmul : b - a < (N : ℝ) * δ := by
    rwa [div_lt_iff₀ hδ] at hltN
  rw [div_lt_iff₀ hNposR]
  nlinarith

/-
 We can take the left boundary of a sub-interval as the tag of the
 interval. We just check that it is within the sub-interval.
-/
theorem leftTagsInPartition {a b : ℝ} (P : Partition a b) :
    tagsInPartition P (fun i => P.pts i.castSucc) := by
  intro i
  constructor
  · exact le_rfl
  · simp only
    apply le_of_lt
    exact P.strict_mono (Fin.castSucc_lt_succ)


/-
 If i ≤ j, the the i-th point in a partition is less than
 the j-th point.

 We call a function from Mathlib directly to prove this lemma.
-/
lemma partition_pts_monotone_core {a b : ℝ} (P : Partition a b)
    {i j : Fin (P.n + 1)} (hij : i ≤ j) :
  P.pts i ≤ P.pts j := by
  exact P.strict_mono.monotone hij

/--
Every point in a partition `P` of `[a, b]` lies within the closed interval `[a, b]`.

This lemma uses the monotonicity of the partition points to demonstrate that
`a = P.pts 0 ≤ P.pts i ≤ P.pts (last) = b` for any valid index `i`.
-/
lemma partition_pts_mem_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin (P.n + 1)} :
    P.pts i ∈ Set.Icc a b := by
  constructor
  · calc
      a = P.pts 0 := P.pts_start.symm
      _ ≤ P.pts i := partition_pts_monotone_core P (Fin.zero_le i)
  · calc
      P.pts i ≤ P.pts (Fin.last P.n) := partition_pts_monotone_core P (Fin.le_last i)
      _ = b := P.pts_end


/--
Every subinterval `[x_i, x_{i+1}]` of a partition `P` of `[a, b]` is a subset of
the entire interval `[a, b]`.

This lemma proves that if a point `x` belongs to the `i`-th subinterval, it naturally
inherits the global bounds `a ≤ x ≤ b` from the partition's endpoints.
-/
lemma subinterval_subset_Icc_core {a b : ℝ} (P : Partition a b) {i : Fin P.n} :
    Partition.subinterval P i ⊆ Set.Icc a b := by
  intro x hx
  constructor
  · -- a ≤ P.pts i.castSucc ≤ x
    exact le_trans (partition_pts_mem_Icc_core P).1 hx.1
  · -- x ≤ P.pts i.succ ≤ b
    exact le_trans hx.2 (partition_pts_mem_Icc_core P).2


theorem taggedCommonLimit_unique {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨_hs₂, hlim₂⟩
  rcases hs₁ with ⟨hab, _⟩
  refine eq_of_forall_dist_le ?_
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  rcases exists_partition_mesh_lt hab (lt_min hδ₁ hδ₂) with ⟨P, hPmesh⟩

  -- Define `tags` to precisely match the size `Fin P.n`
  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- `leftTagsInPartition P` provides exactly this proof.
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hPmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hPmesh (min_le_right δ₁ δ₂)

  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hdecomp :
      L₁ - L₂ = -(taggedSum P tags f alpha - L₁) +
        (taggedSum P tags f alpha - L₂) := by
    ring
  have hlt : |L₁ - L₂| < eps := by
    calc
      |L₁ - L₂| =
          |-(taggedSum P tags f alpha - L₁) +
            (taggedSum P tags f alpha - L₂)| := by rw [hdecomp]
      _ ≤ |-(taggedSum P tags f alpha - L₁)| +
            |taggedSum P tags f alpha - L₂| := abs_add_le _ _
      _ = |taggedSum P tags f alpha - L₁| +
            |taggedSum P tags f alpha - L₂| := by rw [abs_neg]
      _ < eps := by
        have hsum :
            |taggedSum P tags f alpha - L₁| +
                |taggedSum P tags f alpha - L₂| < eps / 2 + eps / 2 :=
          add_lt_add hP₁ hP₂
        simpa using hsum
  have hdist : dist L₁ L₂ < eps := by
    simpa [Real.dist_eq, abs_sub_comm] using hlt
  exact le_of_lt hdist

/-
  Additivity of integrator for the common value of upper and lower limit
-/
theorem upperLowerCommonLimit_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : UpperLowerCommonLimit a b f α₁ L₁)
    (h₂ : UpperLowerCommonLimit a b f α₂ L₂) :
    UpperLowerCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P hmesh₁
  have hP₂ := H₂ P hmesh₂
  constructor
  · have hadd :
        upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂) := by
      rw [upperSum_integrator_add]
      ring
    calc
      |upperSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(upperSum P f α₁ - L₁) + (upperSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |upperSum P f α₁ - L₁| + |upperSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.1 hP₂.1
        simpa using hlt
  · have hadd :
        lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
          (lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂) := by
      rw [lowerSum_integrator_add]
      ring
    calc
      |lowerSum P f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
          |(lowerSum P f α₁ - L₁) + (lowerSum P f α₂ - L₂)| := by rw [hadd]
      _ ≤ |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| := abs_add_le _ _
      _ < eps := by
        have hlt :
            |lowerSum P f α₁ - L₁| + |lowerSum P f α₂ - L₂| <
              eps / 2 + eps / 2 := add_lt_add hP₁.2 hP₂.2
        simpa using hlt

/-
  Additivity of integrator for the tagged common limit
-/
theorem taggedCommonLimit_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f α₁ L₁)
    (h₂ : TaggedCommonLimit a b f α₂ L₂) :
    TaggedCommonLimit a b f (fun x => α₁ x + α₂ x) (L₁ + L₂) := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨hs₂, hlim₂⟩
  refine ⟨sourceHypotheses_integrator_add hs₁ hs₂, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P tags htags hmesh
  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hmesh (min_le_right δ₁ δ₂)
  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hadd :
      taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂) =
        (taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂) := by
    rw [taggedSum_integrator_add]
    ring
  calc
    |taggedSum P tags f (fun x => α₁ x + α₂ x) - (L₁ + L₂)| =
        |(taggedSum P tags f α₁ - L₁) + (taggedSum P tags f α₂ - L₂)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| :=
      abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f α₁ - L₁| + |taggedSum P tags f α₂ - L₂| <
            eps / 2 + eps / 2 := add_lt_add hP₁ hP₂
      simpa using hlt

theorem taggedSum_integrand_add {a b : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (f g alpha : ℝ → ℝ) :
  taggedSum P tags (fun x => f x + g x) alpha =
      taggedSum P tags f alpha + taggedSum P tags g alpha := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem sourceHypotheses_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    (hf : SourceHypotheses a b f alpha)
    (hg : SourceHypotheses a b g alpha) :
    SourceHypotheses a b (fun x => f x + g x) alpha := by
  rcases hf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hg with ⟨_habg, hgAbove, hgBelow, _hmonog⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · refine BddAbove.mono ?_ (hfAbove.add hgAbove)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩
  · refine BddBelow.mono ?_ (hfBelow.add hgBelow)
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, g x, ⟨x, hx, rfl⟩, rfl⟩


theorem taggedCommonLimit_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg) :
    TaggedCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P tags htags hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg
  have hadd :
      taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg) =
        (taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg) := by
    rw [taggedSum_integrand_add]
    ring
  calc
    |taggedSum P tags (fun x => f x + g x) alpha - (Lf + Lg)| =
        |(taggedSum P tags f alpha - Lf) +
          (taggedSum P tags g alpha - Lg)| := by
      rw [hadd]
    _ ≤ |taggedSum P tags f alpha - Lf| +
        |taggedSum P tags g alpha - Lg| := abs_add_le _ _
    _ < eps := by
      have hlt :
          |taggedSum P tags f alpha - Lf| +
            |taggedSum P tags g alpha - Lg| < eps / 2 + eps / 2 :=
        add_lt_add hPf hPg
      simpa using hlt


/--
The supremum of the sum of two functions on a partition subinterval is less than or
equal to the sum of their individual supremums on that subinterval.

Mathematically, this states that for the `i`-th subinterval `I_i = [x_i, x_{i+1}]`:
`sup { f(x) + g(x) | x ∈ I_i } ≤ sup { f(x) | x ∈ I_i } + sup { g(x) | x ∈ I_i }`

This is a core foundational lemma for proving the subadditivity of
upper Riemann-Stieltjes sums.

The hypotheses `hfAbove` and `hgAbove` ensure that the functions are bounded above
on the entire interval `[a, b]`, which guarantees the supremums are mathematically
well-defined real numbers.
-/
lemma upperStep_integrand_add_le_core {a b : ℝ}
    {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    (hgAbove : BddAbove (g '' Set.Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfAbove

  have hgCellAbove : BddAbove (g '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgAbove

  unfold upperStep
  refine csSup_le hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : f x ≤ sSup (f '' Partition.subinterval P i) :=
    le_csSup hfCellAbove ⟨x, hx, rfl⟩

  have hgx : g x ≤ sSup (g '' Partition.subinterval P i) :=
    le_csSup hgCellAbove ⟨x, hx, rfl⟩

  linarith



/--
The sum of the infimums of two functions on a partition subinterval is less than or
equal to the infimum of their sum on that subinterval.

Mathematically, this states that for the `i`-th subinterval `I_i = [x_i, x_{i+1}]`:
`inf { f(x) | x ∈ I_i } + inf { g(x) | x ∈ I_i } ≤ inf { f(x) + g(x) | x ∈ I_i }`

This is a core foundational lemma for proving the superadditivity of lower Riemann-Stieltjes sums.
The hypotheses `hfBelow` and `hgBelow` ensure that the functions are bounded below on the
entire interval `[a, b]`, which guarantees the infimums are mathematically well-defined real numbers.
-/
lemma lowerStep_integrand_add_le_core {a b : ℝ} {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    (hgBelow : BddBelow (g '' Set.Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfBelow

  have hgCellBelow : BddBelow (g '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgBelow

  unfold lowerStep
  refine le_csInf hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : sInf (f '' Partition.subinterval P i) ≤ f x :=
    csInf_le hfCellBelow ⟨x, hx, rfl⟩

  have hgx : sInf (g '' Partition.subinterval P i) ≤ g x :=
    csInf_le hgCellBelow ⟨x, hx, rfl⟩

  linarith



/-
  Image of a constant c times a function f is the same as first taking
  the image of f, and then multiply all numbers in the image set by c.
-/
lemma image_const_mul_Icc_eq_smul_core {a b c : ℝ} (f : ℝ → ℝ) :
    (fun x => c * f x) '' Icc a b = c • (f '' Icc a b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩


/-
  If f satisfies the basic assumptions of integrand in the textbook,
  i.e., f is bounded from above and below,
  then c f also satisfies the assumptions.
-/
theorem sourceHypotheses_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    (h : SourceHypotheses a b f alpha) :
    SourceHypotheses a b (fun x => c * f x) alpha := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hAbove.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddBelow.smul_of_nonpos hc' hBelow
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hBelow.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddAbove.smul_of_nonpos hc' hAbove


/--
The integrator function `alpha` does not decrease across any subinterval of the partition.

Because `alpha` is assumed to be monotonic on `[a, b]` (via `SourceHypotheses`), and the
partition points strictly increase (`x_i < x_{i+1}`), the difference `alpha(x_{i+1}) - alpha(x_i)`
is always non-negative. This guarantees that the width/weights in the Riemann-Stieltjes sum
are non-negative.
-/
lemma partition_increment_nonneg_of_source_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
  -- Unpack the SourceHypotheses to get the monotonicity of alpha
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩

  -- The endpoints of the subinterval are in [a, b]
  have hleft : P.pts i.castSucc ∈ Set.Icc a b := partition_pts_mem_Icc_core P
  have hright : P.pts i.succ ∈ Set.Icc a b := partition_pts_mem_Icc_core P

  -- Because x_i < x_{i+1}, monotonicity implies alpha(x_i) ≤ alpha(x_{i+1})
  have h_pts_lt : P.pts i.castSucc < P.pts i.succ :=
    P.strict_mono (Fin.castSucc_lt_succ)

  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt h_pts_lt))



/--
The upper Riemann-Stieltjes sum of the sum of two functions is subadditive:
`U(P, f + g, α) ≤ U(P, f, α) + U(P, g, α)`
-/
theorem upperSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by
  rcases hsf with ⟨_hab, hfAbove, _hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, hgAbove, _hgBelow, _hmonog⟩
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- `i` is explicitly passed
  have hstep := upperStep_integrand_add_le_core P i hfAbove hgAbove

  -- Reconstruct the SourceHypotheses on the fly using the pieces in your context!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P ⟨_hab, hfAbove, _hfBelow, _hmono⟩

  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith


theorem lowerSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  -- For lower sums, we need the `BddBelow` pieces!
  rcases hsf with ⟨_hab, _hfAbove, hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, _hgAbove, hgBelow, _hmonog⟩
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- Apply the lowerStep lemma we fixed earlier
  have hstep := lowerStep_integrand_add_le_core P i hfBelow hgBelow

  -- Reconstruct the SourceHypotheses for the increment proof
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨_hab, _hfAbove, hfBelow, _hmono⟩

  -- Multiply the step inequality by the non-negative increment width
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

/--
For any subinterval in a partition, the infimum of a function is less than
or equal to its supremum.

Mathematically: `m_i ≤ M_i`.
This relies on the fact that the subinterval is non-empty (it contains at least
its left endpoint), and that the function is bounded both below and above.
-/
lemma lowerStep_le_upperStep_core {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Set.Icc a b))
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  have hcell_nonempty : (f '' Partition.subinterval P i).Nonempty := by
    -- We show the image is non-empty by plugging in the left endpoint
    refine ⟨f (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow

  have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove

  rcases hcell_nonempty with ⟨y, hy⟩
  unfold lowerStep upperStep

  -- inf(f) ≤ y and y ≤ sup(f), therefore inf(f) ≤ sup(f)
  exact le_trans (csInf_le hcellBelow hy) (le_csSup hcellAbove hy)


/--
For any partition, the lower Riemann-Stieltjes sum is always less than
or equal to the upper Riemann-Stieltjes sum.
-/
theorem lowerSum_le_upperSum_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by
  -- Keep a copy of `hs` so we can extract bounds without destroying the original
  have hs_copy := hs
  rcases hs_copy with ⟨_hab, hAbove, hBelow, _hmono⟩

  unfold lowerSum upperSum
  refine Finset.sum_le_sum ?_
  intro i _hi  -- _hi is `i ∈ Finset.univ`, which we ignore

  -- 1. Prove the step inequality: m_i ≤ M_i
  have hstep := lowerStep_le_upperStep_core P i hBelow hAbove

  -- 2. Prove the increment is non-negative: 0 ≤ Δα_i
  -- We can just pass the intact `hs` directly!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 3. Multiply them together: m_i * Δα_i ≤ M_i * Δα_i
  exact mul_le_mul_of_nonneg_right hstep hinc


/--
Additivity of the Riemann-Stieltjes integral with respect to the integrand.

If both `f` and `g` are Riemann-Stieltjes integrable with respect to `alpha`
(having upper/lower limits `Lf` and `Lg` respectively), then their sum `f + g`
is also integrable, and its limit is `Lf + Lg`.

Proof Idea:
This proof is a classic textbook `ε/2` argument, combined with the subadditivity
and superadditivity of partition sums:

1. *Common Refinement:* For a given `eps > 0`, we find `δf` and `δg` corresponding
   to `eps / 2` for `f` and `g`. We require the partition mesh to be less than
   `min(δf, δg)` so both conditions hold simultaneously.

2. *Algebraic Bounds:* We utilize the previously proven subadditivity of upper sums
   (`U(f+g) ≤ U(f) + U(g)`) and superadditivity of lower sums (`L(f) + L(g) ≤ L(f+g)`).

3. *Squeeze:* Because `U(f)` and `L(f)` are tightly squeezed around `Lf` (and similarly
   for `g` around `Lg`), the algebraic bounds force `U(f+g)` and `L(f+g)` to be strictly
   squeezed within an `eps` radius of `Lf + Lg`. The tactic `linarith` handles the
   heavy lifting of unfolding the absolute values and chaining the inequalities.
-/
theorem upperLowerCommonLimit_integrand_add_core {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P hmeshf
  have hPg := Hg P hmeshg
  have hsumUpper :
      upperSum P (fun x => f x + g x) alpha ≤
        upperSum P f alpha + upperSum P g alpha :=
    upperSum_integrand_add_le_core P hsf hsg
  have hsumLower :
      lowerSum P f alpha + lowerSum P g alpha ≤
        lowerSum P (fun x => f x + g x) alpha :=
    lowerSum_integrand_add_le_core P hsf hsg
  have hlowerUpper :
      lowerSum P (fun x => f x + g x) alpha ≤
        upperSum P (fun x => f x + g x) alpha :=
    lowerSum_le_upperSum_core P (sourceHypotheses_integrand_add hsf hsg)
  constructor
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt



lemma abs_const_mul_error_lt_core {c old L eps : ℝ}
    (heps : 0 < eps) (hold : |old - L| < eps / (|c| + 1)) :
    |c * (old - L)| < eps := by
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rw [abs_mul]
  have hmul₁ : |c| * |old - L| ≤ |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt (by simpa [C] using hold)) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)


/--
Multiplying a function by a constant `c` scales its image on any subinterval by `c`.

Mathematically, this states that `{ c * f(x) | x ∈ I_i } = c • { f(x) | x ∈ I_i }`.
This is a key algebraic step for proving that `U(P, c * f, α) = c * U(P, f, α)`.
-/
lemma image_const_mul_subinterval_eq_smul_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) :
    (fun x => c * f x) '' Partition.subinterval P i = c • (f '' Partition.subinterval P i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

/--
Multiplying a function by a non-negative constant `c` scales its supremum
on any partition subinterval by `c`.

Mathematically: `sup { c * f(x) | x ∈ I_i } = c * sup { f(x) | x ∈ I_i }` for `c ≥ 0`.
This relies on the fact that scaling by a non-negative number preserves the ordering
of the real numbers.
-/
lemma upperStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    upperStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sSup_smul_of_nonneg` proves sup(c • S) = c • sup(S) when c ≥ 0
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonneg hc (f '' Partition.subinterval P i)


/--
The upper Riemann-Stieltjes sum scales linearly with respect to multiplication
by a non-negative constant.

Mathematically: `U(P, c * f, α) = c * U(P, f, α)` when `c ≥ 0`.

The requirement that `c` is non-negative is crucial. If `c` were negative,
multiplying the function by `c` would flip the ordering of the reals. The supremum
of `c * f` would then be determined by the *infimum* of `f`, which would transform
the upper sum into a scaled lower sum instead.
-/
theorem upperSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    upperSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonneg_core P f i hc]
  ring


/--
Multiplying a function by a non-negative constant `c` scales its infimum
on any partition subinterval by `c`.

Mathematically: `inf { c * f(x) | x ∈ I_i } = c * inf { f(x) | x ∈ I_i }` for `c ≥ 0`.
This relies on the fact that scaling by a non-negative number preserves the ordering
of the real numbers.
-/
lemma lowerStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : 0 ≤ c) :
    lowerStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sInf_smul_of_nonneg` proves inf(c • S) = c • inf(S) when c ≥ 0
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonneg hc (f '' Partition.subinterval P i)

/--
The lower Riemann-Stieltjes sum scales linearly with respect to multiplication
by a non-negative constant.

Mathematically: `L(P, c * f, α) = c * L(P, f, α)` when `c ≥ 0`.

The requirement that `c` is non-negative is crucial. If `c` were negative,
multiplying the function by `c` would flip the ordering of the reals. The infimum
of `c * f` would then be determined by the *supremum* of `f`, transforming
the lower sum into a scaled upper sum.
-/
theorem lowerSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    lowerSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonneg_core P f i hc]
  ring

/--
Multiplying a function by a non-positive constant `c` transforms its scaled infimum
into a supremum on any partition subinterval.

Mathematically: `sup { c * f(x) | x ∈ I_i } = c * inf { f(x) | x ∈ I_i }` for `c ≤ 0`.
This occurs because multiplying by a negative number reverses the ordering of the reals,
turning the lowest points into the highest points.
-/
lemma upperStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    upperStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold upperStep lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sSup_smul_of_nonpos` proves sup(c • S) = c • inf(S) when c ≤ 0
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonpos hc (f '' Partition.subinterval P i)

theorem upperSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    upperSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold upperSum lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonpos_core P f i hc]
  ring

/--
Multiplying a function by a non-positive constant `c` transforms its scaled supremum
into an infimum on any partition subinterval.

Mathematically: `inf { c * f(x) | x ∈ I_i } = c * sup { f(x) | x ∈ I_i }` for `c ≤ 0`.
Because multiplying by a non-positive number reverses the ordering of the reals,
the highest points of `f` become the lowest points of `c * f`.
-/
lemma lowerStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : Fin P.n) (hc : c ≤ 0) :
    lowerStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold lowerStep upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  -- `Real.sInf_smul_of_nonpos` proves inf(c • S) = c • sup(S) when c ≤ 0
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonpos hc (f '' Partition.subinterval P i)


/--
The lower Riemann-Stieltjes sum of a function multiplied by a non-positive constant
`c` is equal to `c` times the *upper* sum of the original function.

Mathematically: `L(P, c * f, α) = c * U(P, f, α)` when `c ≤ 0`.

Since `c ≤ 0`, the infimum of the scaled function is determined by the supremum
of the original function, thereby transforming the lower sum into a scaled upper sum.
-/
theorem lowerSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    lowerSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold lowerSum upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonpos_core P f i hc]
  ring


/--
Linearity of the Riemann-Stieltjes integral with respect to scalar multiplication.

If a function `f` is Riemann-Stieltjes integrable with respect to `alpha`
(with limit `L`), then `c * f` is also integrable, and its limit is `c * L`.

Proof Idea:
This proof relies on bounding the scaled error by choosing a sufficiently small `eps`.

1. *Scaling Factor `C`:* We define an artificial bounding constant `C = |c| + 1`.
   The `+ 1` is a standard analytic trick to ensure `C > 0` even when `c = 0`,
   preventing division-by-zero errors when we request an initial error of `eps / C`.

2. *Case Split on `c`:* The proof branches depending on whether `c` is non-negative
   or negative:

   - *Case `0 ≤ c`:* Scalar multiplication preserves the order of bounds.
     The error `|U(c*f) - c*L|` cleanly factors into `|c| * |U(f) - L|`, which is
     strictly less than `|c| * (eps / C) < eps`. The lower sum behaves identically.

   - *Case `c < 0`:* Scalar multiplication flips the supremum and infimum.
     Therefore, the upper sum error `|U(c*f) - c*L|` factors into `|c| * |L(f) - L|`
     (using the lower sum of `f`). Because both the upper and lower sums of `f`
     converge to `L`, the error is still bounded by `eps`.
-/
theorem upperLowerCommonLimit_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    UpperLowerCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  by_cases hc : 0 ≤ c
  · constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [upperSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [upperSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)

/--
The tagged Riemann-Stieltjes sum scales linearly with respect to multiplication
by a constant.

Mathematically: `S(P, tags, c * f, α) = c * S(P, tags, f, α)`.

Unlike upper and lower sums, tagged sums evaluate the function at specific points
rather than taking supremums or infimums. Because of this, pulling a constant `c`
out of the sum is purely distributive algebra, and holds for *any* real number `c`
(no `c ≥ 0` or `c ≤ 0` cases are required).
-/
theorem taggedSum_const_mul_core {a b c : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) :
    taggedSum P tags (fun x => c * f x) alpha = c * taggedSum P tags f alpha := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring


/--
Linearity of the tagged Riemann-Stieltjes limit with respect to scalar multiplication.

If the tagged sums of `f` converge to `L`, then the tagged sums of `c * f`
converge to `c * L`.

*Proof Idea:*
This is the tagged-sum equivalent of `upperLowerCommonLimit_const_mul_core`.
However, because tagged sums evaluate the function at specific points rather than
taking supremums or infimums, the proof is actually much simpler! We do not need
to split into `c ≥ 0` and `c < 0` cases.

The proof uses a standard epsilon-delta scaling argument:

1. *Safety Constant:* We define `C = |c| + 1 > 0` to prevent division-by-zero
   when `c = 0`.

2. *Tolerance Scaling:* We ask the original limit `h` for a `δ` that guarantees
   the error of `f`'s sum is strictly less than `eps / C`.

3. *Algebraic Factoring:* Using `taggedSum_const_mul_core`, we factor `c` out
   of the sum algebraically, transforming the target error into
   `|c| * |taggedSum(f) - L|`.

4. *Squeeze:* Because `|taggedSum(f) - L| < eps / C`, the total error is bounded
   by `|c| * (eps / C)`. Since `|c| < |c| + 1 = C`, this strictly bounds the total
   error below `C * (eps / C) = eps`, completing the proof.
-/
theorem taggedCommonLimit_const_mul_core {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f alpha L) :
    TaggedCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  have hEq :
      taggedSum P tags (fun x => c * f x) alpha - c * L =
        c * (taggedSum P tags f alpha - L) := by
    rw [taggedSum_const_mul_core]
    ring
  rw [hEq, abs_mul]
  have hmul₁ : |c| * |taggedSum P tags f alpha - L| ≤
      |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt hP) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)


/--
If tags are chosen within their respective partition subintervals,
then every tag natively belongs to the overall interval `[a, b]`.

This acts as a bridge between local bounds (the tag is in `[x_i, x_{i+1}]`)
and global bounds (the tag is in `[a, b]`).
-/
lemma tag_mem_Icc_of_tagsInPartition_core {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags)
    (i : Fin P.n) :
    tags i ∈ Set.Icc a b :=
  -- `htags i` proves the tag is in the subinterval.
  -- `subinterval_subset_Icc_core` applies the subset property.
  subinterval_subset_Icc_core P (htags i)


/--
Monotonicity of the tagged Riemann-Stieltjes sum.

If `f(x) ≤ g(x)` everywhere on the interval `[a, b]`, then for any partition
and any valid choice of tags, the tagged sum of `f` is less than or equal to
the tagged sum of `g`.

Mathematically: `S(P, tags, f, α) ≤ S(P, tags, g, α)`.
This relies on the integrator `α` being monotonically increasing, ensuring that
the width/weight `Δα_i` is non-negative, preserving the inequality `f(t_i) ≤ g(t_i)`.
-/
theorem taggedSum_mono_core {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha := by
  unfold taggedSum
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- 1. Prove the tag is inside [a, b]
  have htag : tags i ∈ Set.Icc a b := tag_mem_Icc_of_tagsInPartition_core P htags i

  -- 2. Evaluate the function inequality at the tag
  have hstep : f (tags i) ≤ g (tags i) := hfg (tags i) htag

  -- 3. The increment is non-negative (pass `hs` directly!)
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 4. Multiply the step inequality by the non-negative increment
  exact mul_le_mul_of_nonneg_right hstep hinc


/--
Monotonicity of the Riemann-Stieltjes limit.

If `f(x) ≤ g(x)` everywhere on the interval `[a, b]`, and both functions are
integrable with respect to `alpha`, then the integral limit of `f` is less than
or equal to the integral limit of `g` (`Lf ≤ Lg`).

**Proof Idea:**
This proof relies on the algebraic fact that `A ≤ B` is equivalent to proving
that `A < B + eps` for any `eps > 0`.
By picking a partition `P` whose mesh is small enough to simultaneously satisfy
the limit convergence for both `f` and `g`, we can bound `Lf` close to `S(P, f)`,
and `Lg` close to `S(P, g)`. Since the sum of `f` is strictly bounded by the
sum of `g` (proven in `taggedSum_mono_core`), `linarith` easily squeezes the
limits to prove `Lf ≤ Lg`.
-/
theorem taggedCommonLimit_mono_core {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    Lf ≤ Lg := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨_hsg, hlimg⟩

  -- Create a copy of `hsf` so we can extract `hab` without destroying `hsf`
  have hsf_copy := hsf
  rcases hsf_copy with ⟨hab, _hAbove, _hBelow, _hmono⟩

  rw [le_iff_forall_pos_lt_add]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  rcases exists_partition_mesh_lt hab (lt_min hδf hδg) with ⟨P, hPmesh⟩

  -- FIX: Define `tags` to exactly match `Fin P.n → ℝ` using left endpoints
  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- We already proved this earlier!
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmeshf : P.mesh < δf := lt_of_lt_of_le hPmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hPmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg

  -- Pass `hsf` cleanly without rebuilding it!
  have hsum : taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
    taggedSum_mono_core P tags hsf htags hfg

  have hf_bound : Lf < taggedSum P tags f alpha + eps / 2 := by
    have hleft := (abs_lt.mp hPf).1
    linarith
  have hg_bound : taggedSum P tags g alpha < Lg + eps / 2 := by
    have hright := (abs_lt.mp hPg).2
    linarith
  linarith


end DarbouxRS







/-
 # Theorem 1.2 part 1
-/
noncomputable def rsIntegralWitness_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegralWitness (fun x => f x + g x) alpha a b where
  value := rsIntegral f alpha a b hf + rsIntegral g alpha a b hg
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_integrand_add_core
      (rsIntegral_source_spec hf) (rsIntegral_source_spec hg)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_integrand_add
      (rsIntegral_spec hf) (rsIntegral_spec hg)

noncomputable def rsIntegrable_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegrable (fun x => f x + g x) alpha a b :=
  ⟨rsIntegralWitness_integrand_add hf hg⟩

theorem rsIntegral_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    rsIntegral (fun x => f x + g x) alpha a b
        (rsIntegrable_integrand_add hf hg) =
      rsIntegral f alpha a b hf + rsIntegral g alpha a b hg := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrand_add hf hg))
    (DarbouxRS.taggedCommonLimit_integrand_add (rsIntegral_spec hf) (rsIntegral_spec hg))



noncomputable def rsIntegralWitness_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegralWitness (fun x => c * f x) alpha a b where
  value := c * rsIntegral f alpha a b hf
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_const_mul_core
      (c := c) (rsIntegral_source_spec hf)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_const_mul_core
      (c := c) (rsIntegral_spec hf)

noncomputable def rsIntegrable_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegrable (fun x => c * f x) alpha a b :=
  ⟨rsIntegralWitness_integrand_const_mul (c := c) hf⟩

/-
 # Theorem 1.2 part 2
-/
theorem rsIntegral_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    rsIntegral (fun x => c * f x) alpha a b
        (rsIntegrable_integrand_const_mul (c := c) hf) =
      c * rsIntegral f alpha a b hf := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrand_const_mul (c := c) hf))
    (DarbouxRS.taggedCommonLimit_const_mul_core (c := c) (rsIntegral_spec hf))

theorem rsIntegral_integrand_mono {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    rsIntegral f alpha a b hf ≤ rsIntegral g alpha a b hg :=
  DarbouxRS.taggedCommonLimit_mono_core (rsIntegral_spec hf) (rsIntegral_spec hg) hfg





/- # Theorem 1.3 (Existence of witness)
  If f is RS integrable w.r.t. α₁ and α₂ on the interval [a,b],
  then f is RS integral w.r.t. α₁ + α₂.
-/

/-
  show that we have a witness of the integral of f w.r.t. α₁ + α₂
-/
noncomputable def rsIntegralWitness_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegralWitness f (fun x => α₁ x + α₂ x) a b where
  value := rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_integrator_add
      (rsIntegral_source_spec h₁) (rsIntegral_source_spec h₂)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_integrator_add
      (rsIntegral_spec h₁) (rsIntegral_spec h₂)

noncomputable def rsIntegrable_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    RSIntegrable f (fun x => α₁ x + α₂ x) a b :=
  ⟨rsIntegralWitness_integrator_add h₁ h₂⟩


/-
 # Theorem 1.3. (additivity)
 ∫ f d(α₁ + α_2) = ∫ f dα₁ + ∫ f dα₂
-/
theorem rsIntegral_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    rsIntegral f (fun x => α₁ x + α₂ x) a b (rsIntegrable_integrator_add h₁ h₂) =
      rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_add h₁ h₂))
    (DarbouxRS.taggedCommonLimit_integrator_add (rsIntegral_spec h₁) (rsIntegral_spec h₂))
