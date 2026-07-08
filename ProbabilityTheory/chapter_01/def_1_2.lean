import Mathlib

open Finset BigOperators
open Set
open scoped Pointwise
open scoped Classical

noncomputable section

/-
  # Riemann-Stielgjes integral
-/


namespace DarbouxRS

/-- A textbook partition `a = x_0 < x_1 < ... < x_n = b`. -/
structure Partition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : ℕ → ℝ
  pts_start : pts 0 = a
  pts_end : pts n = b
  strict_mono : ∀ i, i < n → pts i < pts (i + 1)

/-- The mesh `max_i (x_{i+1} - x_i)` of a partition. -/
def Partition.mesh {a b : ℝ} (P : Partition a b) : ℝ :=
  Finset.sup' (Finset.range P.n) (⟨0, Finset.mem_range.mpr P.hn⟩)
    fun i => P.pts (i + 1) - P.pts i

/-- The i-th closed subinterval `[x_i, x_{i+1}]`
 in a partition `P`
-/
def subinterval {a b : ℝ} (P : Partition a b) (i : ℕ) : Set ℝ :=
  Set.Icc (P.pts i) (P.pts (i + 1))

/-- The textbook upper step `M_i = sup { f x : x_i <= x <= x_{i+1} }`. -/
def upperStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  sSup (f '' subinterval P i)

/-- The textbook lower step `m_i = inf { f x : x_i <= x <= x_{i+1} }`. -/
def lowerStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : ℕ) : ℝ :=
  sInf (f '' subinterval P i)

/-- The upper Riemann-Stieltjes sum `U(P,f,alpha)`. -/
def upperSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    upperStep P f i * (alpha (P.pts (i + 1)) - alpha (P.pts i))

/-- The lower Riemann-Stieltjes sum `L(P,f,alpha)`. -/
def lowerSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    lowerStep P f i * (alpha (P.pts (i + 1)) - alpha (P.pts i))

/-- A tagged Riemann-Stieltjes sum over the same partition shape. -/
def taggedSum {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n,
    f (tags i) * (alpha (P.pts (i + 1)) - alpha (P.pts i))

/-- Tags chosen in the corresponding partition subintervals. -/
def tagsInPartition {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ) : Prop :=
  ∀ i, i < P.n → tags i ∈ subinterval P i

/-- The standing textbook hypotheses from the paragraphs preceding Definition 1.2. -/
def SourceHypotheses (a b : ℝ) (f alpha : ℝ → ℝ) : Prop :=
  a < b ∧ BddAbove (f '' Set.Icc a b) ∧ BddBelow (f '' Set.Icc a b) ∧
    MonotoneOn alpha (Set.Icc a b)

/-- The source criterion: upper and lower sums converge to the same limit as mesh goes to zero. -/
def UpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b,
      P.mesh < delta →
        |upperSum P f alpha - L| < eps ∧ |lowerSum P f alpha - L| < eps

/-- Riemann-Stieltjes integrability on `[a,b]` with respect to `alpha`. -/
def RSIntegrableOnInterval (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, UpperLowerCommonLimit a b f alpha L

/- Tagged-sum convergence over the same source partition interface.
This is the local tagged formulation of the Riemann--Stieltjes sum
introduced just before Definition 1.2. -/
def TaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b, ∀ tags : ℕ → ℝ,
      tagsInPartition P tags →
        P.mesh < delta →
          |taggedSum P tags f alpha - L| < eps

end DarbouxRS


/-- Textbook partition interface for Definition 1.2. -/
abbrev RSPartition := DarbouxRS.Partition

/-- Mesh of a textbook partition. -/
def rsPartitionMesh {a b : ℝ} (P : RSPartition a b) : ℝ :=
  DarbouxRS.Partition.mesh P

/-- Upper Riemann-Stieltjes sum `U(P,f,alpha)`. -/
def rsUpperSum {a b : ℝ} (P : RSPartition a b) (f alpha : ℝ → ℝ) : ℝ :=
  DarbouxRS.upperSum P f alpha

/-- Lower Riemann-Stieltjes sum `L(P,f,alpha)`. -/
def rsLowerSum {a b : ℝ} (P : RSPartition a b) (f alpha : ℝ → ℝ) : ℝ :=
  DarbouxRS.lowerSum P f alpha

/-- Common upper/lower-sum limit semantics from Definition 1.2. -/
def rsUpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  DarbouxRS.UpperLowerCommonLimit a b f alpha L

/-- Tagged-sum semantics exposed by the existing finite-interval RS core. -/
def rsTaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  DarbouxRS.TaggedCommonLimit a b f alpha L

/--  # Definition 1.2 Riemann-Stieltjes integral

Source-faithful bridge package for the Definition 1.2 integral value.

The source definition is the Darboux upper/lower common-limit criterion. The
same source section also introduces tagged Riemann--Stieltjes sums. A valid
finite-interval integral value carries both pieces of evidence for the same
real number, so the bridge is part of the public definition interface rather
than an unproved public axiom. -/
structure RSIntegralWitness (f alpha : ℝ → ℝ) (a b : ℝ) where
  value : ℝ
  source_limit : rsUpperLowerCommonLimit a b f alpha value
  tagged_limit : rsTaggedCommonLimit a b f alpha value

/-- `f` is Riemann-Stieltjes integrable on `[a,b]` with respect to `alpha`. -/
def RSIntegrable (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  Nonempty (RSIntegralWitness f alpha a b)

/-- The value of the finite-interval Riemann-Stieltjes integral after integrability is known. -/
noncomputable def rsIntegral (f alpha : ℝ → ℝ) (a b : ℝ)
    (h : RSIntegrable f alpha a b) : ℝ :=
  (Classical.choice h).value

/-- The chosen integral value satisfies the source upper/lower common-limit criterion. -/
theorem rsIntegral_source_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).source_limit

/-- The chosen integral value also satisfies the existing tagged-sum core interface. -/
theorem rsIntegral_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).tagged_limit

/-- The guarded integral value is the common value of the source and tagged interfaces. -/
theorem rsIntegral_source_and_tagged_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) ∧
      rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  ⟨rsIntegral_source_spec h, rsIntegral_spec h⟩

namespace DarbouxRS

/-- Uniform source partitions of `[a,b]`. These provide arbitrarily small
mesh partitions for uniqueness of Definition 1.2 limits. -/
def uniformPartition (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Partition a b where
  n := n
  hn := hn
  pts := fun i => a + ((i : ℝ) / (n : ℝ)) * (b - a)
  pts_start := by simp
  pts_end := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    field_simp [hn0]
    ring
  strict_mono := by
    intro i hi
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hba : 0 < b - a := sub_pos.mpr hab
    have hstep : 0 < (b - a) / (n : ℝ) := div_pos hba hnR
    have hdiff :
        a + (((i + 1 : ℕ) : ℝ) / (n : ℝ)) * (b - a) -
          (a + ((i : ℝ) / (n : ℝ)) * (b - a)) = (b - a) / (n : ℝ) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hnR]
      ring
    have hpos : 0 <
        a + (((i + 1 : ℕ) : ℝ) / (n : ℝ)) * (b - a) -
          (a + ((i : ℝ) / (n : ℝ)) * (b - a)) := by
      rw [hdiff]
      exact hstep
    linarith

theorem uniformPartition_mesh_eq (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    (uniformPartition a b hab n hn).mesh = (b - a) / (n : ℝ) := by
  unfold Partition.mesh uniformPartition
  apply Finset.sup'_eq_of_forall
  intro i hi
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hnR]
  ring

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

theorem leftTagsInPartition {a b : ℝ} (P : Partition a b) :
    tagsInPartition P P.pts := by
  intro i hi
  exact ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩

lemma partition_pts_monotone_core {a b : ℝ} (P : Partition a b) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.n) : P.pts i ≤ P.pts j := by
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi0
      rfl
  | succ j ih =>
      by_cases htop : i = j + 1
      · subst htop
        rfl
      · have hij' : i ≤ j := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hij htop)
        have hjle : j ≤ P.n := Nat.le_trans (Nat.le_succ j) hj
        have hlt : j < P.n := Nat.lt_of_succ_le hj
        exact le_trans (ih hij' hjle) (le_of_lt (P.strict_mono j hlt))

lemma partition_pts_mem_Icc_core {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i ≤ P.n) :
    P.pts i ∈ Icc a b := by
  constructor
  · calc
      a = P.pts 0 := P.pts_start.symm
      _ ≤ P.pts i := partition_pts_monotone_core P (Nat.zero_le i) hi
  · calc
      P.pts i ≤ P.pts P.n := partition_pts_monotone_core P hi le_rfl
      _ = b := P.pts_end

lemma subinterval_subset_Icc_core {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i < P.n) :
    subinterval P i ⊆ Icc a b := by
  intro x hx
  constructor
  · exact le_trans (partition_pts_mem_Icc_core P (Nat.le_of_lt hi)).1 hx.1
  · exact le_trans hx.2 (partition_pts_mem_Icc_core P (Nat.succ_le_of_lt hi)).2

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
  let tags := P.pts
  have htags : tagsInPartition P tags := by
    dsimp [tags]
    exact leftTagsInPartition P
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

theorem upperSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    upperSum P f (fun x => α₁ x + α₂ x) =
      upperSum P f α₁ + upperSum P f α₂ := by
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem lowerSum_integrator_add {a b : ℝ} (P : Partition a b)
    (f α₁ α₂ : ℝ → ℝ) :
    lowerSum P f (fun x => α₁ x + α₂ x) =
      lowerSum P f α₁ + lowerSum P f α₂ := by
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem taggedSum_integrator_add {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
    (f α₁ α₂ : ℝ → ℝ) :
    taggedSum P tags f (fun x => α₁ x + α₂ x) =
      taggedSum P tags f α₁ + taggedSum P tags f α₂ := by
  unfold taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem sourceHypotheses_integrator_add {a b : ℝ} {f α₁ α₂ : ℝ → ℝ}
    (h₁ : SourceHypotheses a b f α₁)
    (h₂ : SourceHypotheses a b f α₂) :
    SourceHypotheses a b f (fun x => α₁ x + α₂ x) := by
  rcases h₁ with ⟨hab, hAbove, hBelow, hmono₁⟩
  rcases h₂ with ⟨_hab₂, _hAbove₂, _hBelow₂, hmono₂⟩
  refine ⟨hab, hAbove, hBelow, ?_⟩
  intro x hx y hy hxy
  exact add_le_add (hmono₁ hx hy hxy) (hmono₂ hx hy hxy)

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

theorem taggedSum_integrand_add {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
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

lemma upperStep_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hfAbove : BddAbove (f '' Icc a b))
    (hgAbove : BddAbove (g '' Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i := by
  have hcell_nonempty : ((fun x => f x + g x) '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i) + g (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hfCellAbove : BddAbove (f '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P hi)) hfAbove
  have hgCellAbove : BddAbove (g '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P hi)) hgAbove
  unfold upperStep
  refine csSup_le hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩
  have hfx : f x ≤ sSup (f '' subinterval P i) :=
    le_csSup hfCellAbove ⟨x, hx, rfl⟩
  have hgx : g x ≤ sSup (g '' subinterval P i) :=
    le_csSup hgCellAbove ⟨x, hx, rfl⟩
  linarith

lemma lowerStep_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hfBelow : BddBelow (f '' Icc a b))
    (hgBelow : BddBelow (g '' Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i := by
  have hcell_nonempty : ((fun x => f x + g x) '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i) + g (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hfCellBelow : BddBelow (f '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P hi)) hfBelow
  have hgCellBelow : BddBelow (g '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P hi)) hgBelow
  unfold lowerStep
  refine le_csInf hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩
  have hfx : sInf (f '' subinterval P i) ≤ f x :=
    csInf_le hfCellBelow ⟨x, hx, rfl⟩
  have hgx : sInf (g '' subinterval P i) ≤ g x :=
    csInf_le hgCellBelow ⟨x, hx, rfl⟩
  linarith

lemma partition_increment_nonneg_of_source_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : ℕ}
    (hi : i < P.n) :
    0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩
  have hleft : P.pts i ∈ Icc a b := partition_pts_mem_Icc_core P (Nat.le_of_lt hi)
  have hright : P.pts (i + 1) ∈ Icc a b :=
    partition_pts_mem_Icc_core P (Nat.succ_le_of_lt hi)
  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt (P.strict_mono i hi)))

theorem upperSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by
  rcases hsf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hsg with ⟨_habg, hgAbove, _hgBelow, _hmonog⟩
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hstep := upperStep_integrand_add_le_core (P := P) (i := i) hi_lt hfAbove hgAbove
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨hab, hfAbove, hfBelow, hmono⟩ hi_lt
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

theorem lowerSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  rcases hsf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hsg with ⟨_habg, _hgAbove, hgBelow, _hmonog⟩
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hstep := lowerStep_integrand_add_le_core (P := P) (i := i) hi_lt hfBelow hgBelow
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨hab, hfAbove, hfBelow, hmono⟩ hi_lt
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

lemma lowerStep_le_upperStep_core {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hBelow : BddBelow (f '' Icc a b))
    (hAbove : BddAbove (f '' Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  have hcell_nonempty : (f '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hcellBelow : BddBelow (f '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P hi)) hBelow
  have hcellAbove : BddAbove (f '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P hi)) hAbove
  rcases hcell_nonempty with ⟨y, hy⟩
  unfold lowerStep upperStep
  exact le_trans (csInf_le hcellBelow hy) (le_csSup hcellAbove hy)

theorem lowerSum_le_upperSum_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold lowerSum upperSum
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hstep := lowerStep_le_upperStep_core (P := P) (i := i) hi_lt hBelow hAbove
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨hab, hAbove, hBelow, hmono⟩ hi_lt
  exact mul_le_mul_of_nonneg_right hstep hinc

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

lemma tag_mem_Icc_of_tagsInPartition_core {a b : ℝ} (P : Partition a b)
    {tags : ℕ → ℝ} (htags : tagsInPartition P tags)
    {i : ℕ} (hi : i < P.n) :
    tags i ∈ Icc a b :=
  subinterval_subset_Icc_core P hi (htags i hi)

theorem taggedSum_mono_core {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold taggedSum
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have htag : tags i ∈ Icc a b := tag_mem_Icc_of_tagsInPartition_core P htags hi_lt
  have hstep : f (tags i) ≤ g (tags i) := hfg (tags i) htag
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source_core P
      ⟨hab, hAbove, hBelow, hmono⟩ hi_lt
  exact mul_le_mul_of_nonneg_right hstep hinc

theorem taggedCommonLimit_mono_core {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    Lf ≤ Lg := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨_hsg, hlimg⟩
  rcases hsf with ⟨hab, hAbove, hBelow, hmono⟩
  rw [le_iff_forall_pos_lt_add]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  rcases exists_partition_mesh_lt hab (lt_min hδf hδg) with ⟨P, hPmesh⟩
  let tags := P.pts
  have htags : tagsInPartition P tags := by
    dsimp [tags]
    exact leftTagsInPartition P
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hPmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hPmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg
  have hsum : taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
    taggedSum_mono_core P tags ⟨hab, hAbove, hBelow, hmono⟩ htags hfg
  have hf_bound : Lf < taggedSum P tags f alpha + eps / 2 := by
    have hleft := (abs_lt.mp hPf).1
    linarith
  have hg_bound : taggedSum P tags g alpha < Lg + eps / 2 := by
    have hright := (abs_lt.mp hPg).2
    linarith
  linarith

lemma image_const_mul_subinterval_eq_smul_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) :
    (fun x => c * f x) '' subinterval P i = c • (f '' subinterval P i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

lemma upperStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : 0 ≤ c) :
    upperStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonneg hc (f '' subinterval P i)

lemma lowerStep_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : 0 ≤ c) :
    lowerStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonneg hc (f '' subinterval P i)

lemma upperStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : c ≤ 0) :
    upperStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold upperStep lowerStep
  rw [image_const_mul_subinterval_eq_smul_core]
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonpos hc (f '' subinterval P i)

lemma lowerStep_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : c ≤ 0) :
    lowerStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold lowerStep upperStep
  rw [image_const_mul_subinterval_eq_smul_core]
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonpos hc (f '' subinterval P i)

lemma image_const_mul_Icc_eq_smul_core {a b c : ℝ} (f : ℝ → ℝ) :
    (fun x => c * f x) '' Icc a b = c • (f '' Icc a b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

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

theorem taggedSum_const_mul_core {a b c : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
    (f alpha : ℝ → ℝ) :
    taggedSum P tags (fun x => c * f x) alpha = c * taggedSum P tags f alpha := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

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

theorem upperSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    upperSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonneg_core P f i hc]
  ring

theorem lowerSum_const_mul_nonneg_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    lowerSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonneg_core P f i hc]
  ring

theorem upperSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    upperSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold upperSum lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonpos_core P f i hc]
  ring

theorem lowerSum_const_mul_nonpos_core {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    lowerSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold lowerSum upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonpos_core P f i hc]
  ring

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

end DarbouxRS

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

theorem rsIntegral_integrator_add {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    rsIntegral f (fun x => α₁ x + α₂ x) a b (rsIntegrable_integrator_add h₁ h₂) =
      rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact DarbouxRS.taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_add h₁ h₂))
    (DarbouxRS.taggedCommonLimit_integrator_add (rsIntegral_spec h₁) (rsIntegral_spec h₂))

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

/-- The family `R(alpha)` of functions integrable with respect to `alpha` on `[a,b]`. -/
def rsIntegrableFamily (alpha : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrable f alpha a b}

/-- Exported statement of Definition 1.2. -/
def def_1_2 (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  RSIntegrable f alpha a b
