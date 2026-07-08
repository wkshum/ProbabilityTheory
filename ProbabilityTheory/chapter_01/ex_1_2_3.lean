import Mathlib
import ToyApollo.Output.def_1_1

/-
TASK ID: ex_1_2_3
TYPE: Example_Proof
SOURCE PLAN: 37_chap1_mixed_singular
TASK CONTENT:
\textbf{Example 1.2.3 (Cantor Distribution)} \\
Consider the infinite series
\[
U=\sum_{i=1}^{\infty} \frac{R_i}{3^i},
\]
where $R_i$ for $i=1,2,3,\dots$ are independent discrete random variables that take value $0$ or $2$, each with probability $1/2$. A realization of $U$ is a number between $0$ and $1$. If we expand $U$ as a $3$-ary number, the digits are all equal to $0$ or $2$, with probability $1$.

If the first digit $R_1$ is zero, the value of $U$ is restricted to the interval $[0,1/3]$, because the largest possible value given $R_1=0$ is $0.02222\ldots$ in base $3$, which is equal to $1/3$. If $R_1=2$, then the value of $U$ is larger than $2/3$. We thus have
\[
\Pr(0\le U\le 1/3)=\Pr(2/3\le U\le 1)=1/2,\qquad \text{and} \qquad \Pr(1/3<U<2/3)=0.
\]

The cdf $F_U(u)\triangleq \Pr(U\le u)$ is equal to $1/2$ for $u\in (1/3,2/3)$.

By repeating the argument in the previous paragraph and considering the event $R_1=0$ and $R_2=0$ and the event $R_1=0$ and $R_2=2$, we can show that $F_U(u)$ is equal to $1/4$ for $u\in (1/9,2/9)$. Similar analysis shows that $F_U(u)$ is equal to $3/4$ for $u\in (7/9,8/9)$. The cdf of $U$ is flat on the intervals
\[
(1/3,2/3),\ (1/9,2/9),\ (7/9,8/9),
\]
\[
(1/27,2/27),\ (7/27,8/27),\ (19/27,20/27),\ (25/27,26/27),\ldots
\]

The lengths of these intervals sum to $1$. Let $T$ be the union of all these intervals. Then, we have $\Pr(U\in T)=0$. The set $C\triangleq [0,1]\setminus T$ is called the \textit{Cantor set}. This set has zero length, and we have $\Pr(U\in C)=1$.

One can prove that the Cantor set $C$ is uncountable. In fact, each point in the Cantor set is uniquely associated with a $3$-ary number such as $0.0202202\ldots$. If we divide this number by $2$, we obtain an infinite binary sequence. Conversely, an infinite binary sequence is associated with a point in the Cantor set. Because the set of all infinite binary sequences is uncountable, so is the Cantor set. The cdf of the Cantor distribution has zero slope almost everywhere, except at the uncountably many points in the Cantor set.

\noindent$\blacktriangleright$ \textbf{Notes on the Definition of Singular Distribution} According to the definition given earlier, a real-valued random variable whose range $S$ is finite or countably infinite is classified as a singular random variable. In some textbooks, a singular distribution is further required to have zero probability at each point in the set $S$. With this additional requirement, a discrete random variable is not regarded as singular, but the Cantor distribution is truly singular.

In the rest of this book, however, we will not require that each point in the set $S$ in Definition 1.1 has zero probability. Therefore, a discrete random variable is regarded as a singular random variable in this book.

The concept of singular distribution allows us to express the distribution of any real-valued random variable as the sum of a continuous part and a singular part. This result is known as the Lebesgue decomposition theorem. In practical applications, the singular part of the decomposition is often a discrete probability distribution concentrated on a set of at most countably many points.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal BigOperators

noncomputable section

abbrev ex123Ω := ℕ → Bool

/-- The fair Bernoulli law on one binary digit. -/
def ex123FairCoin : Measure Bool :=
  (1 / 2 : ENNReal) • Measure.dirac false + (1 / 2 : ENNReal) • Measure.dirac true

@[simp] theorem ex123FairCoin_apply_singleton (b : Bool) :
    ex123FairCoin {b} = (1 / 2 : ENNReal) := by
  cases b <;> simp [ex123FairCoin]

instance ex123FairCoin_isProbability : IsProbabilityMeasure ex123FairCoin := by
  refine ⟨by simpa [ex123FairCoin] using ENNReal.inv_two_add_inv_two⟩

/-- Product fair-coin law on the binary sequence space. -/
def ex123P : Measure ex123Ω :=
  Measure.infinitePi fun _ : ℕ => ex123FairCoin

instance ex123P_isProbability : IsProbabilityMeasure ex123P := by
  dsimp [ex123P]
  infer_instance

/-- The binary digit process. -/
def ex123B (n : ℕ) (ω : ex123Ω) : Bool :=
  ω n

lemma ex123B_measurable (n : ℕ) : Measurable (ex123B n) := by
  simpa [ex123B] using measurable_pi_apply n

theorem ex123B_independent : ProbabilityTheory.iIndepFun ex123B ex123P := by
  simpa [ex123B, ex123P] using
    (ProbabilityTheory.iIndepFun_infinitePi (ι := ℕ) (𝓧 := fun _ => Bool)
      (Ω := fun _ => Bool) (P := fun _ : ℕ => ex123FairCoin)
      (fun _ : ℕ => measurable_id))

/-- Ternary digit `0` or `2` generated from the binary digit. -/
def ex123R (n : ℕ) (ω : ex123Ω) : ℝ :=
  if ex123B n ω then (2 : ℝ) else 0

theorem ex123R_def (n : ℕ) :
    ex123R n = fun ω => if ex123B n ω then (2 : ℝ) else 0 :=
  rfl

theorem ex123R_zero_or_two (n : ℕ) (ω : ex123Ω) :
    ex123R n ω = 0 ∨ ex123R n ω = 2 := by
  by_cases h : ex123B n ω <;> simp [ex123R, h]

def ex123Digits (ω : ex123Ω) : ℕ → Fin 3 :=
  fun i => cond (ω i) (2 : Fin 3) 0

/-- The Cantor random variable, represented by its ternary `0/2` expansion. -/
def ex123U (ω : ex123Ω) : ℝ :=
  Real.ofDigits (ex123Digits ω)

def ex123CDF (u : ℝ) : ENNReal :=
  ex123P (ex123U ⁻¹' Set.Iic u)

theorem ex123CDF_def (u : ℝ) :
    ex123CDF u = ex123P (ex123U ⁻¹' Set.Iic u) :=
  rfl

theorem ex123U_series (ω : ex123Ω) :
    HasSum (fun n : ℕ => ex123R n ω / (3 : ℝ) ^ (n + 1)) (ex123U ω) := by
  convert (@summable_ofDigitsTerm 3 (ex123Digits ω)).hasSum using 1
  ext n
  by_cases h : ω n <;> simp [ex123R, ex123B, ex123Digits, Real.ofDigitsTerm, h, div_eq_mul_inv]

lemma ex123U_mem_cantorSet (ω : ex123Ω) : ex123U ω ∈ cantorSet := by
  simpa [ex123U, ex123Digits] using ofDigits_bool_to_fin_three_mem_cantorSet ω

theorem ex123U_mem_unit (ω : ex123Ω) : ex123U ω ∈ Set.Icc (0 : ℝ) 1 :=
  cantorSet_subset_unitInterval (ex123U_mem_cantorSet ω)

lemma ex123U_tail (ω : ex123Ω) :
    ex123U ω =
      (if ω 0 then (2 : ℝ) else 0) / 3 + (1 / 3 : ℝ) * ex123U (fun n => ω (n + 1)) := by
  rw [ex123U, Real.ofDigits_eq_sum_add_ofDigits (ex123Digits ω) 1]
  have htail : (fun i => ex123Digits ω (i + 1)) = ex123Digits (fun n => ω (n + 1)) := by
    funext i
    simp [ex123Digits]
  rw [htail]
  simp [ex123Digits, ex123U, Real.ofDigitsTerm, mul_comm]
  by_cases h : ω 0 <;> simp [h]
  all_goals ring_nf

lemma ex123U_left_of_false {ω : ex123Ω} (hω : ω 0 = false) :
    ex123U ω ∈ Set.Icc (0 : ℝ) (1 / 3 : ℝ) := by
  rw [ex123U_tail, hω]
  simp
  have htail := ex123U_mem_unit (fun n => ω (n + 1))
  constructor <;> nlinarith [htail.1, htail.2]

lemma ex123U_right_of_true {ω : ex123Ω} (hω : ω 0 = true) :
    ex123U ω ∈ Set.Icc (2 / 3 : ℝ) 1 := by
  rw [ex123U_tail, hω]
  simp
  have htail := ex123U_mem_unit (fun n => ω (n + 1))
  constructor <;> nlinarith [htail.1, htail.2]

lemma ex123U_not_middle (ω : ex123Ω) :
    ex123U ω ∉ Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) := by
  by_cases hω : ω 0 = false
  · have hleft := ex123U_left_of_false hω
    intro hmid
    nlinarith [hleft.2, hmid.1]
  · have htrue : ω 0 = true := by cases h : ω 0 <;> simp [h] at hω ⊢
    have hright := ex123U_right_of_true htrue
    intro hmid
    nlinarith [hright.1, hmid.2]

lemma ex123U_preimage_left :
    ex123U ⁻¹' Set.Icc (0 : ℝ) (1 / 3 : ℝ) = {ω : ex123Ω | ω 0 = false} := by
  ext ω
  constructor
  · intro hleft
    by_cases hω : ω 0 = false
    · exact hω
    · have htrue : ω 0 = true := by cases h : ω 0 <;> simp [h] at hω ⊢
      have hright := ex123U_right_of_true htrue
      nlinarith [hleft.2, hright.1]
  · intro hω
    exact ex123U_left_of_false hω

lemma ex123U_preimage_right :
    ex123U ⁻¹' Set.Icc (2 / 3 : ℝ) 1 = {ω : ex123Ω | ω 0 = true} := by
  ext ω
  constructor
  · intro hright
    by_cases hω : ω 0 = true
    · exact hω
    · have hfalse : ω 0 = false := by cases h : ω 0 <;> simp [h] at hω ⊢
      have hleft := ex123U_left_of_false hfalse
      nlinarith [hright.1, hleft.2]
  · intro hω
    exact ex123U_right_of_true hω

lemma ex123P_first_bit_false : ex123P {ω : ex123Ω | ω 0 = false} = (1 / 2 : ENNReal) := by
  rw [show {ω : ex123Ω | ω 0 = false} =
    (fun ω : ex123Ω => ω 0) ⁻¹' ({false} : Set Bool) by rfl]
  rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton false)]
  rw [ex123P, Measure.infinitePi_map_eval]
  simp

lemma ex123P_first_bit_true : ex123P {ω : ex123Ω | ω 0 = true} = (1 / 2 : ENNReal) := by
  rw [show {ω : ex123Ω | ω 0 = true} =
    (fun ω : ex123Ω => ω 0) ⁻¹' ({true} : Set Bool) by rfl]
  rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton true)]
  rw [ex123P, Measure.infinitePi_map_eval]
  simp

lemma ex123P_first_two_bits (b0 b1 : Bool) :
    ex123P {ω : ex123Ω | ω 0 = b0 ∧ ω 1 = b1} = (1 / 4 : ENNReal) := by
  let t : ℕ → Set Bool := fun i =>
    if i = 0 then {b0} else if i = 1 then {b1} else Set.univ
  have hset :
      {ω : ex123Ω | ω 0 = b0 ∧ ω 1 = b1} =
        Set.pi ({0, 1} : Finset ℕ) t := by
    ext ω
    simp [t]
  rw [hset, ex123P]
  rw [Measure.infinitePi_pi]
  · simp [t]
    rw [← ENNReal.mul_inv (a := (2 : ENNReal)) (b := (2 : ENNReal)) (by simp) (by simp)]
    norm_num
  · intro i hi
    fin_cases hi <;> simp [t]

lemma ex123U_left_left_of_false_false {ω : ex123Ω} (h0 : ω 0 = false) (h1 : ω 1 = false) :
    ex123U ω ∈ Set.Icc (0 : ℝ) (1 / 9 : ℝ) := by
  rw [ex123U_tail, h0]
  simp
  have htail := ex123U_left_of_false (ω := fun n => ω (n + 1)) h1
  constructor <;> nlinarith [htail.1, htail.2]

lemma ex123U_left_right_of_false_true {ω : ex123Ω} (h0 : ω 0 = false) (h1 : ω 1 = true) :
    ex123U ω ∈ Set.Icc (2 / 9 : ℝ) (1 / 3 : ℝ) := by
  rw [ex123U_tail, h0]
  simp
  have htail := ex123U_right_of_true (ω := fun n => ω (n + 1)) h1
  constructor <;> nlinarith [htail.1, htail.2]

lemma ex123U_right_left_of_true_false {ω : ex123Ω} (h0 : ω 0 = true) (h1 : ω 1 = false) :
    ex123U ω ∈ Set.Icc (2 / 3 : ℝ) (7 / 9 : ℝ) := by
  rw [ex123U_tail, h0]
  simp
  have htail := ex123U_left_of_false (ω := fun n => ω (n + 1)) h1
  constructor <;> nlinarith [htail.1, htail.2]

lemma ex123U_right_right_of_true_true {ω : ex123Ω} (h0 : ω 0 = true) (h1 : ω 1 = true) :
    ex123U ω ∈ Set.Icc (8 / 9 : ℝ) 1 := by
  rw [ex123U_tail, h0]
  simp
  have htail := ex123U_right_of_true (ω := fun n => ω (n + 1)) h1
  constructor <;> nlinarith [htail.1, htail.2]

theorem ex123_left_third_probability :
    ex123P (ex123U ⁻¹' Set.Icc (0 : ℝ) (1 / 3 : ℝ)) = ((1 : ENNReal) / 2) := by
  rw [ex123U_preimage_left, ex123P_first_bit_false]

theorem ex123_middle_third_probability :
    ex123P (ex123U ⁻¹' Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) = 0 := by
  have hpre : ex123U ⁻¹' Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) = ∅ := by
    ext ω
    constructor
    · intro hω
      exact False.elim ((ex123U_not_middle ω) hω)
    · intro hω
      exact False.elim hω
  rw [hpre, measure_empty]

theorem ex123_right_third_probability :
    ex123P (ex123U ⁻¹' Set.Icc (2 / 3 : ℝ) 1) = ((1 : ENNReal) / 2) := by
  rw [ex123U_preimage_right, ex123P_first_bit_true]

lemma ex123U_preimage_Iic_middle {u : ℝ} (hu : u ∈ Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) :
    ex123U ⁻¹' Set.Iic u = ex123U ⁻¹' Set.Icc (0 : ℝ) (1 / 3 : ℝ) := by
  ext ω
  constructor
  · intro hle
    have hunit := ex123U_mem_unit ω
    refine ⟨hunit.1, ?_⟩
    by_contra hnot
    have hgt : (1 / 3 : ℝ) < ex123U ω := lt_of_not_ge hnot
    have hlt : ex123U ω < (2 / 3 : ℝ) := lt_of_le_of_lt hle hu.2
    exact (ex123U_not_middle ω) ⟨hgt, hlt⟩
  · intro hleft
    exact le_trans hleft.2 hu.1.le

theorem ex123CDF_flat_middle (u : ℝ) (hu : u ∈ Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) :
    ex123CDF u = ((1 : ENNReal) / 2) := by
  rw [ex123CDF, ex123U_preimage_Iic_middle hu, ex123_left_third_probability]

lemma ex123U_preimage_Iic_left_gap {u : ℝ}
    (hu : u ∈ Set.Ioo (1 / 9 : ℝ) (2 / 9 : ℝ)) :
    ex123U ⁻¹' Set.Iic u = {ω : ex123Ω | ω 0 = false ∧ ω 1 = false} := by
  ext ω
  constructor
  · intro hle
    by_cases h0 : ω 0 = false
    · by_cases h1 : ω 1 = false
      · exact ⟨h0, h1⟩
      · have h1true : ω 1 = true := by cases h : ω 1 <;> simp [h] at h1 ⊢
        have hright := ex123U_left_right_of_false_true h0 h1true
        have hle' : ex123U ω ≤ u := hle
        nlinarith [hle', hright.1, hu.2]
    · have h0true : ω 0 = true := by cases h : ω 0 <;> simp [h] at h0 ⊢
      have hright := ex123U_right_of_true h0true
      have hle' : ex123U ω ≤ u := hle
      nlinarith [hle', hright.1, hu.2]
  · intro hprefix
    have hleft := ex123U_left_left_of_false_false hprefix.1 hprefix.2
    exact le_trans hleft.2 hu.1.le

theorem ex123CDF_flat_left_gap (u : ℝ)
    (hu : u ∈ Set.Ioo (1 / 9 : ℝ) (2 / 9 : ℝ)) :
    ex123CDF u = (1 / 4 : ENNReal) := by
  rw [ex123CDF, ex123U_preimage_Iic_left_gap hu, ex123P_first_two_bits false false]

lemma ex123_first_two_bits_measurable (b0 b1 : Bool) :
    MeasurableSet {ω : ex123Ω | ω 0 = b0 ∧ ω 1 = b1} := by
  have h0 : MeasurableSet {ω : ex123Ω | ω 0 = b0} := by
    rw [show {ω : ex123Ω | ω 0 = b0} =
      (fun ω : ex123Ω => ω 0) ⁻¹' ({b0} : Set Bool) by rfl]
    exact (measurable_pi_apply 0) (measurableSet_singleton b0)
  have h1 : MeasurableSet {ω : ex123Ω | ω 1 = b1} := by
    rw [show {ω : ex123Ω | ω 1 = b1} =
      (fun ω : ex123Ω => ω 1) ⁻¹' ({b1} : Set Bool) by rfl]
    exact (measurable_pi_apply 1) (measurableSet_singleton b1)
  rw [show {ω : ex123Ω | ω 0 = b0 ∧ ω 1 = b1} =
    {ω : ex123Ω | ω 0 = b0} ∩ {ω : ex123Ω | ω 1 = b1} by
      ext ω
      simp]
  exact h0.inter h1

lemma ex123U_preimage_Iic_right_gap {u : ℝ}
    (hu : u ∈ Set.Ioo (7 / 9 : ℝ) (8 / 9 : ℝ)) :
    ex123U ⁻¹' Set.Iic u = ({ω : ex123Ω | ω 0 = true ∧ ω 1 = true})ᶜ := by
  ext ω
  constructor
  · intro hle hprefix
    have hright := ex123U_right_right_of_true_true hprefix.1 hprefix.2
    have hle' : ex123U ω ≤ u := hle
    nlinarith [hle', hright.1, hu.2]
  · intro hnot
    by_cases h0 : ω 0 = true
    · by_cases h1 : ω 1 = true
      · exact False.elim (hnot ⟨h0, h1⟩)
      · have h1false : ω 1 = false := by cases h : ω 1 <;> simp [h] at h1 ⊢
        have hleft := ex123U_right_left_of_true_false h0 h1false
        exact le_trans hleft.2 hu.1.le
    · have h0false : ω 0 = false := by cases h : ω 0 <;> simp [h] at h0 ⊢
      have hleft := ex123U_left_of_false h0false
      have hle : ex123U ω ≤ (7 / 9 : ℝ) := by nlinarith [hleft.2]
      exact le_trans hle hu.1.le

lemma ex123_ennreal_one_sub_quarter :
    (1 : ENNReal) - (1 / 4 : ENNReal) = (3 / 4 : ENNReal) := by
  have h14 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have h34 : (3 / 4 : ENNReal) = ENNReal.ofReal (3 / 4 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  exact ENNReal.sub_eq_of_eq_add (by norm_num) (by
    rw [h14, h34, ← ENNReal.ofReal_add] <;> norm_num)

theorem ex123CDF_flat_right_gap (u : ℝ)
    (hu : u ∈ Set.Ioo (7 / 9 : ℝ) (8 / 9 : ℝ)) :
    ex123CDF u = (3 / 4 : ENNReal) := by
  rw [ex123CDF, ex123U_preimage_Iic_right_gap hu]
  rw [measure_compl (ex123_first_two_bits_measurable true true) (measure_ne_top _ _)]
  rw [measure_univ, ex123P_first_two_bits true true, ex123_ennreal_one_sub_quarter]

lemma ex123_volume_image_div3 (S : Set ℝ) :
    volume ((· / 3) '' S) = ENNReal.ofReal (1 / 3) * volume S := by
  convert Real.volume_preimage_mul_left (show (3 : ℝ) ≠ 0 by norm_num) S using 1 <;> ring_nf
  congr with x
  aesop

lemma ex123_image_add2_div3_eq_preimage (S : Set ℝ) :
    (fun x => (2 + x) / 3) '' S = (fun y => y * 3 - 2) ⁻¹' S := by
  grind

lemma ex123_volume_image_add2_div3_of_measurable (S : Set ℝ) (hS : MeasurableSet S) :
    volume ((fun x => (2 + x) / 3) '' S) = ENNReal.ofReal (1 / 3) * volume S := by
  rw [ex123_image_add2_div3_eq_preimage S]
  have hfun : (fun y : ℝ => y * 3 - 2) = fun y : ℝ => (3 : ℝ) * y + (-2) := by
    funext y
    ring
  rw [hfun]
  change volume ((fun y : ℝ => (3 : ℝ) * y) ⁻¹'
      ((fun z : ℝ => z + (-2)) ⁻¹' S)) =
    ENNReal.ofReal (1 / 3) * volume S
  rw [Real.volume_preimage_mul_left (show (3 : ℝ) ≠ 0 by norm_num)]
  rw [(measurePreserving_add_right volume (-2 : ℝ)).measure_preimage hS.nullMeasurableSet]
  norm_num

lemma ex123_volume_preCantorSet_le (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
  induction n with
  | zero =>
    erw [Real.volume_Icc]
    norm_num
  | succ n ih =>
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    rw [ex123_volume_image_div3,
      ex123_volume_image_add2_div3_of_measurable (preCantorSet n)
        (isClosed_preCantorSet n).measurableSet]
    convert mul_le_mul_right ih (ENNReal.ofReal (1 / 3) + ENNReal.ofReal (1 / 3)) using 1
    · ring
    rw [← ENNReal.ofReal_add] <;> norm_num
    ring

theorem ex123_volume_cantorSet_eq_zero : volume cantorSet = 0 := by
  have h_cantor_subset : ∀ n, volume (preCantorSet n) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) :=
    fun n => ex123_volume_preCantorSet_le n
  have h_cantor_le : ∀ n, volume cantorSet ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
    exact fun n =>
      le_trans (MeasureTheory.measure_mono <| Set.iInter_subset _ _) (h_cantor_subset n)
  have h_cantor_zero :
      Filter.Tendsto (fun n => ENNReal.ofReal ((2 / 3 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (2 : ℝ) / 3 < 1))
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds h_cantor_zero h_cantor_le) bot_le

theorem ex123_cantor_set_probability_one :
    ex123P (ex123U ⁻¹' cantorSet) = 1 := by
  have hpre : ex123U ⁻¹' cantorSet = Set.univ := by
    ext ω
    constructor
    · intro _; trivial
    · intro _; exact ex123U_mem_cantorSet ω
  rw [hpre, measure_univ]

/-- The gaps removed when passing from level `n` to level `n + 1`. -/
def ex123RemovedGapLayer (n : ℕ) : Set ℝ :=
  preCantorSet n \ preCantorSet (n + 1)

/-- The source text's set `T`: the union of all removed middle-third gaps. -/
def ex123T : Set ℝ :=
  ⋃ n, ex123RemovedGapLayer n

theorem ex123_removed_gaps_def :
    ex123T = ⋃ n, ex123RemovedGapLayer n :=
  rfl

theorem ex123_removed_gaps_union :
    ex123T = Set.Icc (0 : ℝ) 1 \ cantorSet := by
  classical
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    constructor
    · exact preCantorSet_subset_unitInterval hn.1
    · intro hC
      exact hn.2 (Set.mem_iInter.mp hC (n + 1))
  · intro hx
    have hx0 : x ∈ preCantorSet 0 := by
      simpa using hx.1
    have hnot_all : ¬ ∀ n, x ∈ preCantorSet n := by
      intro hall
      exact hx.2 (Set.mem_iInter.mpr hall)
    have hbad : ∃ n, x ∉ preCantorSet n := not_forall.mp hnot_all
    let k := Nat.find hbad
    have hk_not : x ∉ preCantorSet k := Nat.find_spec hbad
    have hk_pos : 0 < k := by
      by_contra hpos
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hpos
      exact hk_not (by simpa [hk0] using hx0)
    obtain ⟨n, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk_pos)
    have hn_lt : n < k := by
      rw [hk]
      exact Nat.lt_succ_self n
    have hn_mem : x ∈ preCantorSet n := by
      by_contra hn
      exact (Nat.find_min hbad (by simpa [k] using hn_lt)) hn
    have hn_not : x ∉ preCantorSet (n + 1) := by
      simpa [k, hk] using hk_not
    exact Set.mem_iUnion.mpr
      ⟨n, ⟨hn_mem, hn_not⟩⟩

theorem ex123_removed_gaps_probability_zero :
    ex123P (ex123U ⁻¹' ex123T) = 0 := by
  have hpre : ex123U ⁻¹' ex123T = ∅ := by
    ext ω
    constructor
    · intro hω
      have hT : ex123U ω ∈ Set.Icc (0 : ℝ) 1 \ cantorSet := by
        simpa [ex123_removed_gaps_union] using hω
      exact False.elim (hT.2 (ex123U_mem_cantorSet ω))
    · intro hω
      exact False.elim hω
  rw [hpre, measure_empty]

theorem ex123_singular : IsSingularRealRandomVariable ex123P ex123U :=
  ⟨cantorSet, ex123_volume_cantorSet_eq_zero, ex123_cantor_set_probability_one⟩

/-- Proof-bodied package for the currently closed part of Example 1.2.3. -/
structure CantorDistributionExample where
  Ω : Type
  mΩ : MeasurableSpace Ω
  P : Measure Ω
  isProbability : IsProbabilityMeasure P
  B : ℕ → Ω → Bool
  binary_digits_measurable : ∀ n, Measurable (B n)
  binary_digits_independent : ProbabilityTheory.iIndepFun B P
  R : ℕ → Ω → ℝ
  ternary_digit_def : ∀ n, R n = fun ω => if B n ω then (2 : ℝ) else 0
  ternary_digits_zero_or_two : ∀ n ω, R n ω = 0 ∨ R n ω = 2
  U : Ω → ℝ
  series_representation : ∀ ω, HasSum (fun n : ℕ => R n ω / (3 : ℝ) ^ (n + 1)) (U ω)
  values_in_unit_interval : ∀ ω, U ω ∈ Set.Icc (0 : ℝ) 1
  left_third_probability :
    P (U ⁻¹' Set.Icc (0 : ℝ) (1 / 3 : ℝ)) = ((1 : ENNReal) / 2)
  middle_third_probability :
    P (U ⁻¹' Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ)) = 0
  right_third_probability :
    P (U ⁻¹' Set.Icc (2 / 3 : ℝ) 1) = ((1 : ENNReal) / 2)
  cdf : ℝ → ENNReal
  cdf_def : ∀ u, cdf u = P (U ⁻¹' Set.Iic u)
  cdf_flat_on_middle_third :
    ∀ u, u ∈ Set.Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) → cdf u = ((1 : ENNReal) / 2)
  cdf_flat_on_left_gap :
    ∀ u, u ∈ Set.Ioo (1 / 9 : ℝ) (2 / 9 : ℝ) → cdf u = (1 / 4 : ENNReal)
  cdf_flat_on_right_gap :
    ∀ u, u ∈ Set.Ioo (7 / 9 : ℝ) (8 / 9 : ℝ) → cdf u = (3 / 4 : ENNReal)
  removed_gap_layer : ℕ → Set ℝ
  removed_gaps : Set ℝ
  removed_gaps_def : removed_gaps = ⋃ n, removed_gap_layer n
  removed_gaps_union : removed_gaps = Set.Icc (0 : ℝ) 1 \ cantorSet
  removed_gaps_probability_zero : P (U ⁻¹' removed_gaps) = 0
  cantor_set_probability_one : P (U ⁻¹' cantorSet) = 1
  cantor_set_volume_zero : volume cantorSet = 0
  singular : IsSingularRealRandomVariable P U
  cantor_binary_equiv : cantorSet ≃ (ℕ → Bool)

/-- The instantiated Cantor distribution construction with proof-bodied first-gap facts. -/
def ex_1_2_3 : CantorDistributionExample where
  Ω := ex123Ω
  mΩ := inferInstance
  P := ex123P
  isProbability := ex123P_isProbability
  B := ex123B
  binary_digits_measurable := ex123B_measurable
  binary_digits_independent := ex123B_independent
  R := ex123R
  ternary_digit_def := ex123R_def
  ternary_digits_zero_or_two := ex123R_zero_or_two
  U := ex123U
  series_representation := ex123U_series
  values_in_unit_interval := ex123U_mem_unit
  left_third_probability := ex123_left_third_probability
  middle_third_probability := ex123_middle_third_probability
  right_third_probability := ex123_right_third_probability
  cdf := ex123CDF
  cdf_def := ex123CDF_def
  cdf_flat_on_middle_third := ex123CDF_flat_middle
  cdf_flat_on_left_gap := ex123CDF_flat_left_gap
  cdf_flat_on_right_gap := ex123CDF_flat_right_gap
  removed_gap_layer := ex123RemovedGapLayer
  removed_gaps := ex123T
  removed_gaps_def := ex123_removed_gaps_def
  removed_gaps_union := ex123_removed_gaps_union
  removed_gaps_probability_zero := ex123_removed_gaps_probability_zero
  cantor_set_probability_one := ex123_cantor_set_probability_one
  cantor_set_volume_zero := ex123_volume_cantorSet_eq_zero
  singular := ex123_singular
  cantor_binary_equiv := cantorSetEquivNatToBool

/-- The Cantor set corresponds to infinite binary sequences. -/
theorem ex_1_2_3_cantor_binary_equiv : Nonempty (cantorSet ≃ (ℕ → Bool)) := by
  exact ⟨ex_1_2_3.cantor_binary_equiv⟩

/-- The constructed Cantor random variable is singular in the sense of Definition 1.1. -/
theorem ex_1_2_3_singular : IsSingularRealRandomVariable ex123P ex123U :=
  ex_1_2_3.singular

/-- The Cantor-distributed random variable gives probability zero to the union of all removed
gaps. -/
theorem ex_1_2_3_removed_gaps_probability_zero :
    ex123P (ex123U ⁻¹' ex123T) = 0 :=
  ex_1_2_3.removed_gaps_probability_zero
