import Mathlib.Tactic
import ProbabilityTheory.chapter_02.def_2_6
import Mathlib.MeasureTheory.Measure.MeasureSpace


/-

 Theorem 2.4 Lower semi-continuity of measure

-/

/-
\begin{thmbox}{2.4 (Lower Semi-Continuity)}
Suppose $A_1\subseteq A_2\subseteq A_3\subseteq \cdots$ is a sequence of increasing sets in $\mathcal{F}$ and $(\Omega,\mathcal{F},\mu)$ is a measure space. Then
\[
\lim_{k\to\infty} \mu(A_k)=\mu\left(\bigcup_{i=1}^{\infty} A_i\right).
\]
\end{thmbox}

\textit{Proof} Let $B_1=A_1$ and $B_i=A_i\setminus A_{i-1}$ for $i\ge 2$. The sets $B_i$'s are mutually disjoint by construction. Moreover, we have $\biguplus_{i=1}^{\infty} B_i=\cup_{i=1}^{\infty} A_i$. This gives
\[
\lim_{k\to\infty} \mu(A_k)
=
\lim_{k\to\infty} \mu(B_1 \uplus B_2 \uplus \cdots \uplus B_k)
\]
\[
=
\lim_{k\to\infty} \sum_{i=1}^{k} \mu(B_i)
\triangleq
\sum_{i=1}^{\infty} \mu(B_i)
=
\mu\left(\biguplus_{i=1}^{\infty} B_i\right)
=
\mu\left(\bigcup_{i=1}^{\infty} A_i\right),
\]
where the second last equality follows from the countable additivity of measure $\mu$. \hfill $\square$
-/


open MeasureTheory Set
open scoped BigOperators

/-- Source proof increments: `B₀ = A₀` and `B_{n+1} = A_{n+1} \ A_n`. -/
def thm_2_4_increment {Ω : Type*} (A : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => A 0
  | n + 1 => A (n + 1) \ A n

theorem thm_2_4_increment_subset {Ω : Type*} (A : ℕ → Set Ω) (n : ℕ) :
    thm_2_4_increment A n ⊆ A n := by
  cases n with
  | zero =>
      intro x hx
      simpa [thm_2_4_increment] using hx
  | succ n =>
      intro x hx
      exact hx.1

theorem thm_2_4_increment_pairwise_disjoint {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    Pairwise (fun i j => Disjoint (thm_2_4_increment A i) (thm_2_4_increment A j)) := by
  change Monotone A at hA
  have hlt_disjoint :
      ∀ {i j : ℕ}, i < j → Disjoint (thm_2_4_increment A i) (thm_2_4_increment A j) := by
    intro i j hlt
    cases j with
    | zero =>
        omega
    | succ k =>
        have hi_le_k : i ≤ k := Nat.lt_succ_iff.mp hlt
        rw [disjoint_left]
        intro x hxi hxj
        have hxAi : x ∈ A i := thm_2_4_increment_subset A i hxi
        have hxAk : x ∈ A k := hA hi_le_k hxAi
        exact hxj.2 hxAk
  intro i j hij
  by_cases hlt : i < j
  · exact hlt_disjoint hlt
  · have hji : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hij)
    exact (hlt_disjoint hji).symm

theorem thm_2_4_increment_measurable {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hAmeas : ∀ n, MeasurableSet (A n)) :
    ∀ n, MeasurableSet (thm_2_4_increment A n)
  | 0 => by
      simpa [thm_2_4_increment] using hAmeas 0
  | n + 1 => by
      simpa [thm_2_4_increment] using (hAmeas (n + 1)).diff (hAmeas n)

theorem thm_2_4_partial_increment_union_eq {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    ∀ n : ℕ, (⋃ i ∈ Set.Iic n, thm_2_4_increment A i) = A n := by
  change Monotone A at hA
  intro n
  induction n with
  | zero =>
      ext x
      constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨hi_le, hxB⟩
        have hi0 : i = 0 := le_antisymm hi_le (Nat.zero_le i)
        subst i
        simpa [thm_2_4_increment] using hxB
      · intro hx
        refine mem_iUnion.mpr ⟨0, ?_⟩
        exact mem_iUnion.mpr ⟨(by simp : 0 ∈ Set.Iic 0), by simpa [thm_2_4_increment] using hx⟩
  | succ n ih =>
      ext x
      constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨hi_le, hxB⟩
        by_cases hi_prev : i ≤ n
        · have hx_partial_n : x ∈ ⋃ i ∈ Set.Iic n, thm_2_4_increment A i :=
            mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨(by simpa using hi_prev), hxB⟩⟩
          have hxAn : x ∈ A n := by
            rw [ih] at hx_partial_n
            exact hx_partial_n
          exact hA (Nat.le_succ n) hxAn
        · have hi_le_nat : i ≤ n + 1 := by simpa using hi_le
          have hi_eq : i = n + 1 := by omega
          subst i
          exact thm_2_4_increment_subset A (n + 1) hxB
      · intro hx
        by_cases hxAn : x ∈ A n
        · have hx_partial_n : x ∈ ⋃ i ∈ Set.Iic n, thm_2_4_increment A i := by
            rw [ih]
            exact hxAn
          rcases mem_iUnion.mp hx_partial_n with ⟨i, hi⟩
          rcases mem_iUnion.mp hi with ⟨hi_le, hxB⟩
          refine mem_iUnion.mpr ⟨i, ?_⟩
          have hi_le_nat : i ≤ n := by simpa using hi_le
          exact mem_iUnion.mpr ⟨(by simpa using Nat.le_trans hi_le_nat (Nat.le_succ n)), hxB⟩
        · refine mem_iUnion.mpr ⟨n + 1, ?_⟩
          exact mem_iUnion.mpr ⟨(by simp : n + 1 ∈ Set.Iic (n + 1)), by exact ⟨hx, hxAn⟩⟩

theorem thm_2_4_increment_iUnion_eq {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) :
    (⋃ i, thm_2_4_increment A i) = ⋃ i, A i := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    exact mem_iUnion.mpr ⟨i, thm_2_4_increment_subset A i hxi⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨n, hxAn⟩
    have hx_partial : x ∈ ⋃ i ∈ Set.Iic n, thm_2_4_increment A i := by
      rw [thm_2_4_partial_increment_union_eq hA n]
      exact hxAn
    rcases mem_iUnion.mp hx_partial with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨_hi_le, hxB⟩
    exact mem_iUnion.mpr ⟨i, hxB⟩

/-- Finite partial increment unions, indexed by `Finset.range`, recover `A n`. -/
theorem thm_2_4_partial_increment_range_union_eq {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqIncreasing A) (n : ℕ) :
    (⋃ i ∈ Finset.range (n + 1), thm_2_4_increment A i) = A n := by
  rw [← thm_2_4_partial_increment_union_eq hA n]
  ext x
  simp [Finset.mem_range]

/-- Source finite-additivity step: each `A n` is the finite disjoint union of its increments. -/
theorem thm_2_4_partial_measure_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    μ (A n) = ∑ i ∈ Finset.range (n + 1), μ (thm_2_4_increment A i) := by
  rw [← thm_2_4_partial_increment_range_union_eq hA n]
  exact measure_biUnion_finset
    (fun i _hi j _hj hij => thm_2_4_increment_pairwise_disjoint hA hij)
    (fun i _hi => thm_2_4_increment_measurable hAmeas i)

/-- Extended nonnegative series as the supremum of nonempty initial partial sums. -/
theorem thm_2_4_tsum_eq_iSup_sum_range_succ (f : ℕ → ENNReal) :
    ∑' i, f i = ⨆ n, ∑ i ∈ Finset.range (n + 1), f i := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le n
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
        (fun i _hi _hnot => by
          simp only [zero_le] ))
  · refine iSup_le fun n => ?_
    exact le_iSup_of_le (n + 1) le_rfl


/-- Source countable-additivity landing for the disjoint increment construction. -/
theorem thm_2_4_countable_additivity_spine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    μ (⋃ i, A i) = ∑' i, μ (thm_2_4_increment A i) := by
  rw [← thm_2_4_increment_iUnion_eq hA]
  exact measure_iUnion (thm_2_4_increment_pairwise_disjoint hA)
    (thm_2_4_increment_measurable hAmeas)

/-- Exported statement for Theorem 2.4. -/
theorem thm_2_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    μ (⋃ i, A i) = ⨆ i, μ (A i) := by
  have hseries :
      μ (⋃ i, A i) = ∑' i, μ (thm_2_4_increment A i) :=
    thm_2_4_countable_additivity_spine μ A hA hAmeas
  have hpartial :
      ∀ n, μ (A n) = ∑ i ∈ Finset.range (n + 1), μ (thm_2_4_increment A i) :=
    thm_2_4_partial_measure_eq_sum μ A hA hAmeas
  calc
    μ (⋃ i, A i) = ∑' i, μ (thm_2_4_increment A i) := hseries
    _ = ⨆ n, ∑ i ∈ Finset.range (n + 1), μ (thm_2_4_increment A i) := by
      rw [thm_2_4_tsum_eq_iSup_sum_range_succ]
    _ = ⨆ n, μ (A n) := by
      exact iSup_congr fun n => (hpartial n).symm


/--  # Theorem 2.4 Measure function is continuous from below

Explicit filter-limit form of Theorem 2.4. -/
theorem thm_2_4_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    Filter.Tendsto (fun i => μ (A i)) Filter.atTop (nhds (μ (⋃ i, A i))) := by
  have hmono : Monotone fun i => μ (A i) := fun i j hij => measure_mono (hA hij)
  have hsup : μ (⋃ i, A i) = ⨆ i, μ (A i) := thm_2_4 μ A hA hAmeas
  rw [hsup]
  exact tendsto_atTop_iSup hmono
