import Mathlib.Tactic

--import Mathlib.Topology.MetricSpace.Basic
-- ℝ as a metric space: `dist`, `Real.dist_eq`, `eq_of_forall_dist_le`
--import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- ℝ ordered field, `sSup`/`sInf`, `exists_nat_gt`
--import Mathlib.Data.Fintype.Basic
-- `Fintype (Fin n)`, `Finset.univ`, `Finset.mem_univ`
--import Mathlib.Data.Finset.Lattice.Fold
-- `Finset.sup'`, `Finset.sup'_eq_of_forall`
--import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- `∑` (`Finset.sum`) notation

open scoped BigOperators Pointwise

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



/-  Package for the Definition 1.2 integral value.

The textbook definition is the Darboux upper/lower common-limit criterion. We call it
the `source_limit`.

The same section also introduces another Riemann-Stieltjes sum S(P, f, alpha),
called `tagged_limit`.

A *witness* of RS integral is the common `value` of the Darboux limit and tagged limit.
-/

/-
  # Design choice for structure `RSIntegralWitness`

  The field

      tagged_limit : rsTaggedCommonLimit a b f alpha value

  is logically redundant under our current hypotheses.  Indeed, since
  `SourceHypotheses` assumes that `alpha` is monotone increasing on `[a,b]`,
  every Stieltjes increment

      alpha xᵢ₊₁ - alpha xᵢ

  is nonnegative.  Therefore every tagged sum is squeezed between the lower and
  upper Darboux--Stieltjes sums over the same partition:

      lowerSum P f alpha ≤ taggedSum P tags f alpha ≤ upperSum P f alpha.

  Consequently, if the upper and lower sums converge to the same limit, then the
  tagged sums also converge to that same limit:

      rsUpperLowerCommonLimit a b f alpha L →
      rsTaggedCommonLimit a b f alpha L.

  Thus, in principle, `RSIntegralWitness` could store only the upper/lower
  common-limit field and derive the tagged formulation as a theorem.

  Nevertheless, we deliberately keep the tagged limit as part of the witness.
  The reason is practical rather than logical.  In later arguments it is often
  more convenient to access the tagged-sum formulation directly, without first
  invoking the conversion theorem from upper/lower sums.  This is especially
  useful in proofs where the integral is naturally characterized by arbitrary
  tagged sums rather than by Darboux upper and lower sums.

  Examples include:

  * uniqueness of the Riemann-Stieltjes integral value, where one compares two
    candidate limits by evaluating the same tagged sums with sufficiently small
    mesh;

  * arguments based on tagged sums and pointwise choices of tags, such as
    applications of mean value type results, where the tagged formulation matches
    the mathematical proof more directly;

  * later estimates where one chooses tags with special properties and compares
    the resulting tagged sums to the integral.

  Therefore the structure records both viewpoints:

      source_limit : rsUpperLowerCommonLimit a b f alpha value
      tagged_limit : rsTaggedCommonLimit a b f alpha value

  even though the second one follows from the first.  This makes the witness a
  convenient interface for both Darboux-style and tagged-sum-style arguments.


  The reverse direction

      rsTaggedCommonLimit a b f alpha L →  rsUpperLowerCommonLimit a b f alpha L

  should also hold under the present hypotheses, because
  the tagged condition quantifies over all choices of tags, and upper/lower sums
  can be approximated by tags chosen near the local suprema/infima.  However,
  that proof requires additional ε-approximation lemmas for `sSup` and `sInf`,
  finite choice of near-extremizing tags, and several estimates comparing the
  resulting tagged sums with the Darboux sums.

  Since the reverse implication is not needed in the subsequent logical
  development, we omit it.  The forward direction is sufficient for our purposes:
  it allows every witness of the upper/lower common limit to provide the tagged
  formulation as well.
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




section RS_integral_uniqueness
/-
  In this section we prove that the limit of tagged sums
  is unique, if the limit exists.
-/


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

/--
  The limit of tagged sums is unique, provided the tags are chosen
  in the corresponding sub-intervals and the mesh goes to zero.
-/
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

end RS_integral_uniqueness


/-
The following API can be reused

exists_common_refinement
lowerSum_le_of_refinement
upperSum_le_of_refinement
lowerSum_le_upperSum_any

-/
