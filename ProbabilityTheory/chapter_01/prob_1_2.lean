import Mathlib

/-!
# Problem 1.2: Compound Poisson-Bernoulli Distribution

We show that if X ~ Poisson(Λ) and Y_1, ..., Y_X are iid Bernoulli(p),
then Y_1 + ... + Y_X ~ Poisson(pΛ).
-/

open Finset Real BigOperators Nat MeasureTheory

noncomputable section

/-- Poisson PMF with parameter μ. -/
def PoissonDistribution (μ : ℝ) : ℕ → ℝ :=
  fun n => μ ^ n / (n.factorial : ℝ) * exp (-μ)

/-- Bernoulli PMF with parameter p on ℕ (p(0)=1-p, p(1)=p, p(k)=0 for k≥2). -/
def BernoulliDistribution (p : ℝ) : ℕ → ℝ :=
  fun n => if n = 0 then 1 - p else if n = 1 then p else 0

/-- n-fold discrete convolution power of a PMF g on ℕ. -/
def convPower (g : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => ∑ j ∈ Finset.range (k + 1), convPower g n j * g (k - j)

/-- Compound (random-sum) distribution: if X ~ f and Y_i iid ~ g,
    then the distribution of Y_1 + ... + Y_X is RandomSumDistribution f g. -/
def RandomSumDistribution (f g : ℕ → ℝ) : ℕ → ℝ :=
  fun k => ∑' n, f n * convPower g n k

/-- The finite random sum from the source statement, `Y_1 + ... + Y_X`.  We index
the Bernoulli family from `0`; this is only a Lean convention and gives the
same `X`-term finite sum. -/
def poissonBernoulliRandomSum {Ω : Type*} (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) : Ω → ℕ :=
  fun ω => ∑ i ∈ Finset.range (X ω), Y i ω

/-- Atom probability for a natural-valued random variable. -/
def naturalAtomProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℕ) (k : ℕ) : ℝ :=
  (P {ω | Z ω = k}).toReal

/-- `X` has the Poisson law with parameter `Λ`, at the atom/pmf level used by
the source problem. -/
def HasPoissonLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (Λ : ℝ) : Prop :=
  ∀ n : ℕ, naturalAtomProbability P X n = PoissonDistribution Λ n

/-- Distributional form of the source construction step: after conditioning on
`X = n`, the generated Bernoulli indicators contribute the `n`-fold Bernoulli
convolution, and the finite random sum marginalizes over the law of `X`. -/
def BernoulliThinningRandomSumLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (p : ℝ) : Prop :=
  ∀ k : ℕ,
    naturalAtomProbability P (poissonBernoulliRandomSum X Y) k =
      RandomSumDistribution
        (fun n : ℕ => naturalAtomProbability P X n)
        (BernoulliDistribution p) k

/-- Atom set of the actual finite Bernoulli random sum. -/
def randomSumAtomSet {Ω : Type*} (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (k : ℕ) : Set Ω :=
  {ω | poissonBernoulliRandomSum X Y ω = k}

/-- Joint atom set of the Poisson count and the actual finite Bernoulli random sum. -/
def countRandomSumJointAtomSet {Ω : Type*}
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (n k : ℕ) : Set Ω :=
  {ω | X ω = n} ∩ randomSumAtomSet X Y k

/-- Joint atom probability of the Poisson count and the actual finite Bernoulli random sum. -/
def countRandomSumJointAtomProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (n k : ℕ) : ℝ :=
  (P (countRandomSumJointAtomSet X Y n k)).toReal

/-- Joint atom set for the finite Bernoulli vector generated after `X = n`.
The source-level conditional iid law is naturally stated on these vector atoms. -/
def finiteVectorBernoulliAtomSet {Ω : Type*}
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (n : ℕ) (z : Fin n → ℕ) : Set Ω :=
  {ω | X ω = n} ∩ (Set.iInter fun i : Fin n => {ω | Y (i : ℕ) ω = z i})

/-- Probability of a finite-vector joint atom. -/
def finiteVectorBernoulliAtomProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (n : ℕ) (z : Fin n → ℕ) : ℝ :=
  (P (finiteVectorBernoulliAtomSet X Y n z)).toReal

/-- Finite index set of length-`n` natural vectors whose coordinates sum to `k`. -/
def randomSumVectorIndex (n k : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.univ : Finset (Fin n)).piAntidiag k

lemma sum_antidiagonal_swap {M : Type*} [AddCommMonoid M]
    (f : ℕ × ℕ → M) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, f p.swap =
      ∑ p ∈ Finset.antidiagonal n, f p := by
  conv_rhs => rw [← Finset.map_swap_antidiagonal, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _hp
  rfl

lemma sum_piAntidiag_prod_eq_convPower_card {α : Type*} [DecidableEq α]
    (s : Finset α) (g : ℕ → ℝ) (k : ℕ) :
    (∑ z ∈ s.piAntidiag k, ∏ i ∈ s, g (z i)) = convPower g s.card k := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
      cases k <;> simp [convPower]
  | cons a s ha ih =>
      rw [Finset.piAntidiag_cons ha k]
      rw [Finset.sum_disjiUnion]
      simp_rw [Finset.sum_map]
      simp only [Finset.card_cons, Finset.prod_cons ha, addRightEmbedding_apply, Pi.add_apply,
        if_true]
      rw [show s.card + 1 = s.card.succ by rfl]
      rw [show convPower g s.card.succ k =
          ∑ j ∈ Finset.range (k + 1), convPower g s.card j * g (k - j) by rfl]
      calc
        (∑ p ∈ Finset.antidiagonal k,
            ∑ z ∈ s.piAntidiag p.2,
              g (z a + p.1) * ∏ i ∈ s, g (z i + if i = a then p.1 else 0))
            = ∑ p ∈ Finset.antidiagonal k, g p.1 * convPower g s.card p.2 := by
                apply Finset.sum_congr rfl
                intro p _hp
                calc
                  (∑ z ∈ s.piAntidiag p.2,
                    g (z a + p.1) * ∏ i ∈ s, g (z i + if i = a then p.1 else 0))
                      = ∑ z ∈ s.piAntidiag p.2, g p.1 * ∏ i ∈ s, g (z i) := by
                          apply Finset.sum_congr rfl
                          intro z hz
                          have hza : z a = 0 := by
                            by_contra hza
                            exact ha ((Finset.mem_piAntidiag.mp hz).2 a hza)
                          have hprod :
                              (∏ i ∈ s, g (z i + if i = a then p.1 else 0)) =
                                ∏ i ∈ s, g (z i) := by
                            apply Finset.prod_congr rfl
                            intro i hi
                            have hia : i ≠ a := fun h => ha (h ▸ hi)
                            simp [hia]
                          rw [hza, zero_add, hprod]
                    _ = g p.1 * ∑ z ∈ s.piAntidiag p.2, ∏ i ∈ s, g (z i) := by
                          rw [Finset.mul_sum]
                    _ = g p.1 * convPower g s.card p.2 := by
                          rw [ih]
        _ = ∑ p ∈ Finset.antidiagonal k, convPower g s.card p.1 * g p.2 := by
              rw [← sum_antidiagonal_swap
                (fun p : ℕ × ℕ => convPower g s.card p.1 * g p.2) k]
              apply Finset.sum_congr rfl
              intro p _hp
              simp [mul_comm]
        _ = ∑ j ∈ Finset.range (k + 1), convPower g s.card j * g (k - j) := by
              rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun j r => convPower g s.card j * g r) k]

lemma sum_randomSumVectorIndex_prod_eq_convPower (g : ℕ → ℝ) (n k : ℕ) :
    (∑ z ∈ randomSumVectorIndex n k, ∏ i : Fin n, g (z i)) = convPower g n k := by
  simpa [randomSumVectorIndex] using
    (sum_piAntidiag_prod_eq_convPower_card (s := (Finset.univ : Finset (Fin n))) g k)

/-- Source-level conditional iid Bernoulli finite-vector joint law:
on `{X = n}`, every concrete vector `z` has the product Bernoulli mass. -/
def ConditionallyIIDBernoulliFiniteVector {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (p : ℝ) : Prop :=
  ∀ n : ℕ, ∀ z : Fin n → ℕ,
    finiteVectorBernoulliAtomProbability P X Y n z =
      naturalAtomProbability P X n * ∏ i : Fin n, BernoulliDistribution p (z i)

/-- Atom-level source assumption for the conditional iid Bernoulli generation:
on the event `X = n`, the actual `n`-term sum has the `n`-fold Bernoulli
convolution law.  This is the conditional contribution before marginalizing
over the Poisson count, not the final random-sum PMF identity. -/
def ConditionallyIIDBernoulliRandomSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (p : ℝ) : Prop :=
  ∀ n k : ℕ,
    countRandomSumJointAtomProbability P X Y n k =
      naturalAtomProbability P X n * convPower (BernoulliDistribution p) n k

lemma finiteVectorBernoulliAtomSet_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ)
    (hXmeas : Measurable X) (hYmeas : ∀ i : ℕ, Measurable (Y i))
    (n : ℕ) (z : Fin n → ℕ) :
    MeasurableSet (finiteVectorBernoulliAtomSet X Y n z) := by
  have h_count : MeasurableSet {ω | X ω = n} := by
    change MeasurableSet (X ⁻¹' ({n} : Set ℕ))
    exact hXmeas (measurableSet_singleton n)
  have h_vec :
      MeasurableSet (Set.iInter fun i : Fin n => {ω | Y (i : ℕ) ω = z i}) := by
    apply MeasurableSet.iInter
    intro i
    change MeasurableSet ((Y (i : ℕ)) ⁻¹' ({z i} : Set ℕ))
    exact hYmeas (i : ℕ) (measurableSet_singleton (z i))
  exact h_count.inter h_vec

lemma countRandomSumJointAtomSet_eq_biUnion_finiteVectorAtoms {Ω : Type*}
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (n k : ℕ) :
    countRandomSumJointAtomSet X Y n k =
      (⋃ z, ⋃ _ : z ∈ (randomSumVectorIndex n k : Set (Fin n → ℕ)),
        finiteVectorBernoulliAtomSet X Y n z) := by
  ext ω
  rw [Set.mem_iUnion₂]
  constructor
  · intro hω
    refine ⟨fun i : Fin n => Y i ω, ?_, ?_⟩
    · have hsum : (∑ i : Fin n, Y i ω) = k := by
        rw [show (∑ i : Fin n, Y i ω) = ∑ i ∈ Finset.range n, Y i ω from
          Fin.sum_univ_eq_sum_range (fun i => Y i ω) n]
        rw [← hω.1]
        simpa [randomSumAtomSet, poissonBernoulliRandomSum] using hω.2
      simpa [randomSumVectorIndex] using hsum
    · simp [finiteVectorBernoulliAtomSet, hω.1]
  · rintro ⟨z, hz, hω⟩
    rcases hω with ⟨hX, hzω⟩
    refine ⟨hX, ?_⟩
    change poissonBernoulliRandomSum X Y ω = k
    rw [poissonBernoulliRandomSum, hX]
    have hsum_z : (∑ i : Fin n, z i) = k := by
      simpa [randomSumVectorIndex] using hz
    have hsum_Y : (∑ i : Fin n, Y i ω) = ∑ i : Fin n, z i := by
      apply Finset.sum_congr rfl
      intro i _hi
      have := Set.mem_iInter.mp hzω i
      simpa using this
    rw [← Fin.sum_univ_eq_sum_range (fun i => Y i ω) n]
    exact hsum_Y.trans hsum_z

lemma finiteVectorBernoulli_atoms_pairwise_disjoint {Ω : Type*}
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (n k : ℕ) :
    (randomSumVectorIndex n k : Set (Fin n → ℕ)).PairwiseDisjoint
      (finiteVectorBernoulliAtomSet X Y n) := by
  intro z _hz w _hw hzw
  change Disjoint (finiteVectorBernoulliAtomSet X Y n z)
    (finiteVectorBernoulliAtomSet X Y n w)
  rw [Set.disjoint_left]
  intro ω hzω hwω
  apply hzw
  funext i
  have hzi := Set.mem_iInter.mp hzω.2 i
  have hwi := Set.mem_iInter.mp hwω.2 i
  exact hzi.symm.trans hwi

lemma countRandomSumJointAtomProbability_eq_sum_finiteVectorAtoms {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ)
    (hXmeas : Measurable X) (hYmeas : ∀ i : ℕ, Measurable (Y i))
    (n k : ℕ) :
    countRandomSumJointAtomProbability P X Y n k =
      ∑ z ∈ randomSumVectorIndex n k,
        finiteVectorBernoulliAtomProbability P X Y n z := by
  unfold countRandomSumJointAtomProbability finiteVectorBernoulliAtomProbability
  rw [countRandomSumJointAtomSet_eq_biUnion_finiteVectorAtoms X Y n k]
  have hmeasure :
      P (⋃ z, ⋃ _ : z ∈ (randomSumVectorIndex n k : Set (Fin n → ℕ)),
          finiteVectorBernoulliAtomSet X Y n z) =
        ∑ z ∈ randomSumVectorIndex n k, P (finiteVectorBernoulliAtomSet X Y n z) := by
    exact measure_biUnion_finset (finiteVectorBernoulli_atoms_pairwise_disjoint X Y n k)
      (fun z _hz => finiteVectorBernoulliAtomSet_measurable X Y hXmeas hYmeas n z)
  rw [hmeasure]
  exact ENNReal.toReal_sum (fun _z _hz => measure_ne_top P _)

lemma conditionallyIIDBernoulliRandomSum_of_finiteVectorJointLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (p : ℝ)
    (hXmeas : Measurable X) (hYmeas : ∀ i : ℕ, Measurable (Y i))
    (hVec : ConditionallyIIDBernoulliFiniteVector P X Y p) :
    ConditionallyIIDBernoulliRandomSum P X Y p := by
  intro n k
  rw [countRandomSumJointAtomProbability_eq_sum_finiteVectorAtoms P X Y hXmeas hYmeas n k]
  simp_rw [hVec n]
  rw [← Finset.mul_sum]
  rw [sum_randomSumVectorIndex_prod_eq_convPower]

lemma randomSum_atom_eq_iUnion_count_atoms {Ω : Type*} (X : Ω → ℕ)
    (Y : ℕ → Ω → ℕ) (k : ℕ) :
    randomSumAtomSet X Y k =
      ⋃ n, countRandomSumJointAtomSet X Y n k := by
  ext ω
  constructor
  · intro hω
    exact
      ⟨countRandomSumJointAtomSet X Y (X ω) k, ⟨X ω, rfl⟩,
        by simpa [countRandomSumJointAtomSet, randomSumAtomSet, hω]⟩
  · rintro ⟨s, ⟨n, rfl⟩, hn⟩
    exact hn.2

lemma count_randomSum_atoms_pairwise_disjoint {Ω : Type*} (X : Ω → ℕ)
    (Y : ℕ → Ω → ℕ) (k : ℕ) :
    Pairwise
      (fun m n : ℕ =>
        Disjoint (countRandomSumJointAtomSet X Y m k) (countRandomSumJointAtomSet X Y n k)) := by
  intro m n hmn
  rw [Set.disjoint_left]
  intro ω hm hn
  exact hmn (hm.1.symm.trans hn.1)

lemma bernoulliThinningRandomSumLaw_of_conditionallyIID {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ) (p : ℝ)
    (hXmeas : Measurable X)
    (hSmeas : Measurable (poissonBernoulliRandomSum X Y))
    (hY : ConditionallyIIDBernoulliRandomSum P X Y p) :
    BernoulliThinningRandomSumLaw P X Y p := by
  intro k
  have h_atom_meas : MeasurableSet (randomSumAtomSet X Y k) := by
    change MeasurableSet ((poissonBernoulliRandomSum X Y) ⁻¹' ({k} : Set ℕ))
    exact hSmeas (measurableSet_singleton k)
  have h_count_sum_meas :
      ∀ n : ℕ, MeasurableSet (countRandomSumJointAtomSet X Y n k) := by
    intro n
    have h_count_meas : MeasurableSet {ω | X ω = n} := by
      change MeasurableSet (X ⁻¹' ({n} : Set ℕ))
      exact hXmeas (measurableSet_singleton n)
    simpa [countRandomSumJointAtomSet] using h_count_meas.inter h_atom_meas
  have h_partition :
      P (randomSumAtomSet X Y k) =
        ∑' n : ℕ, P (countRandomSumJointAtomSet X Y n k) := by
    rw [randomSum_atom_eq_iUnion_count_atoms X Y k]
    exact measure_iUnion (count_randomSum_atoms_pairwise_disjoint X Y k) h_count_sum_meas
  calc
    naturalAtomProbability P (poissonBernoulliRandomSum X Y) k
        = (P (randomSumAtomSet X Y k)).toReal := by
          rfl
    _ = ∑' n : ℕ, (P (countRandomSumJointAtomSet X Y n k)).toReal := by
          rw [h_partition, ENNReal.tsum_toReal_eq]
          intro n
          exact measure_ne_top P _
    _ = ∑' n : ℕ,
          naturalAtomProbability P X n * convPower (BernoulliDistribution p) n k := by
          exact tsum_congr fun n => hY n k
    _ = RandomSumDistribution
          (fun n : ℕ => naturalAtomProbability P X n)
          (BernoulliDistribution p) k := by
          rfl

/-
The n-fold convolution of Bernoulli(p) equals the Binomial(n,p) PMF.
-/
lemma convPower_bernoulli (p : ℝ) (n k : ℕ) :
    convPower (BernoulliDistribution p) n k =
    if k ≤ n then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0 := by
  induction' n with n ih generalizing k;
  · cases k <;> aesop;
  · rcases k with ( _ | k ) <;> simp_all +decide [ Nat.choose_succ_succ, pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.sum_range_succ ];
    · rw [ show convPower ( BernoulliDistribution p ) ( n + 1 ) 0 = ∑ j ∈ Finset.range ( 0 + 1 ), convPower ( BernoulliDistribution p ) n j * BernoulliDistribution p ( 0 - j ) by rfl, Finset.sum_range_succ ] ; aesop;
    · rw [ show convPower ( BernoulliDistribution p ) ( n + 1 ) ( k + 1 ) = ∑ j ∈ Finset.range ( k + 2 ), convPower ( BernoulliDistribution p ) n j * BernoulliDistribution p ( k + 1 - j ) by rfl ];
      rw [ Finset.sum_eq_add ( k ) ( k + 1 ) ] <;> simp_all +decide [ Finset.sum_range_succ, Nat.choose_succ_succ ];
      · split_ifs <;> simp_all +decide [ BernoulliDistribution ];
        · rw [ show n - k = n - ( k + 1 ) + 1 by omega ] ; ring;
        · simp_all +decide [ le_antisymm ‹_› ‹_›, pow_succ, mul_assoc, mul_comm, mul_left_comm ];
        · linarith;
      · intro c hc₁ hc₂ hc₃ hc₄; rw [ BernoulliDistribution ] ; split_ifs <;> norm_num ; omega;
        omega

/-
Key summation identity for the compound Poisson-Bernoulli distribution.
-/
lemma poisson_compound_bernoulli_pointwise (Λ : ℝ) (hΛ : 0 < Λ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (∑' n, (Λ ^ n / (n.factorial : ℝ) * exp (-Λ)) *
      (if k ≤ n then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0)) =
    (p * Λ) ^ k / (k.factorial : ℝ) * exp (-(p * Λ)) := by
  trans ∑' n, Λ ^ ( n + k ) / ( ( n + k ) ! : ℝ ) * Real.exp ( -Λ ) * ( if k ≤ n + k then ↑ ( ( n + k ).choose k ) * p ^ k * ( 1 - p ) ^ ( ( n + k ) - k ) else 0 );
  · rw [ ← Summable.sum_add_tsum_nat_add k ];
    · rw [ Finset.sum_eq_zero ] <;> aesop;
    · refine' Summable.of_nonneg_of_le ( fun n => _ ) ( fun n => _ ) ( Real.summable_pow_div_factorial Λ |> Summable.mul_right ( Real.exp ( -Λ ) ) );
      · split_ifs <;> first | positivity | exact mul_nonneg ( by positivity ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp0 _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ ) ) ;
      · split_ifs <;> norm_num;
        · refine' mul_le_of_le_one_right ( by positivity ) _;
          have := add_pow p ( 1 - p ) n;
          norm_num at this;
          exact this.symm ▸ Finset.single_le_sum ( fun m _ => mul_nonneg ( mul_nonneg ( pow_nonneg hp0 m ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) ( n - m ) ) ) ( Nat.cast_nonneg _ ) ) ( Finset.mem_range.mpr ( by linarith ) ) |> le_trans ( by ring_nf; norm_num );
        · positivity;
  · -- Recognize that the sum is a series expansion for $e^{p\Lambda}$.
    have h_series : ∑' n : ℕ, (Λ ^ n / (n ! : ℝ)) * (1 - p) ^ n = Real.exp (Λ * (1 - p)) := by
      rw [ Real.exp_eq_exp_ℝ ];
      rw [ NormedSpace.exp_eq_tsum_div ] ; exact tsum_congr fun n => by rw [ mul_pow ] ; ring;
    convert congr_arg ( fun x : ℝ => x * ( Λ ^ k / ( k ! : ℝ ) ) * p ^ k * Real.exp ( -Λ ) ) h_series using 1;
    · rw [ ← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right ] ; congr ; ext n ; simp +decide [ Nat.cast_choose, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, pow_add, Nat.factorial_ne_zero ];
    · rw [ show - ( p * Λ ) = -Λ + Λ * ( 1 - p ) by ring, Real.exp_add ] ; ring

-- Note: the user's original theorem used `λ` as a variable name, but `λ` is reserved
-- in Lean 4. We use `Λ` (capital lambda) instead.
theorem prob_1_2_pmf_identity
    (Λ : ℝ) (hΛ : Λ > 0) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    RandomSumDistribution (PoissonDistribution Λ) (BernoulliDistribution p) = PoissonDistribution (p * Λ) := by
  ext k
  simp only [RandomSumDistribution, PoissonDistribution]
  have hconv : ∀ n, Λ ^ n / (↑n.factorial) * exp (-Λ) * convPower (BernoulliDistribution p) n k =
      Λ ^ n / (↑n.factorial) * exp (-Λ) *
      (if k ≤ n then (↑(n.choose k)) * p ^ k * (1 - p) ^ (n - k) else 0) := by
    intro n; rw [convPower_bernoulli]
  simp_rw [hconv]
  exact poisson_compound_bernoulli_pointwise Λ hΛ p hp.1 hp.2 k

/-- Problem 1.2: if `X` has Poisson law with mean `Λ` and, after `X` is
generated, the Bernoulli indicators `Y_i` produce the standard thinning
random-sum law, then the actual random sum `Y_1 + ... + Y_X` has Poisson law
with mean `pΛ`. -/
theorem prob_1_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Λ : ℝ) (hΛ : Λ > 0) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (X : Ω → ℕ) (Y : ℕ → Ω → ℕ)
    (hXmeas : Measurable X)
    (hYmeas : ∀ i : ℕ, Measurable (Y i))
    (hSmeas : Measurable (poissonBernoulliRandomSum X Y))
    (hX : HasPoissonLaw P X Λ)
    (hYvec : ConditionallyIIDBernoulliFiniteVector P X Y p) :
    ∀ k : ℕ,
      naturalAtomProbability P (poissonBernoulliRandomSum X Y) k =
        PoissonDistribution (p * Λ) k := by
  intro k
  have hY : ConditionallyIIDBernoulliRandomSum P X Y p :=
    conditionallyIIDBernoulliRandomSum_of_finiteVectorJointLaw
      P X Y p hXmeas hYmeas hYvec
  have hThin : BernoulliThinningRandomSumLaw P X Y p :=
    bernoulliThinningRandomSumLaw_of_conditionallyIID P X Y p hXmeas hSmeas hY
  rw [hThin k]
  have hXpmf : (fun n : ℕ => naturalAtomProbability P X n) = PoissonDistribution Λ := by
    funext n
    exact hX n
  rw [hXpmf]
  exact congrFun (prob_1_2_pmf_identity Λ hΛ p hp) k

end
