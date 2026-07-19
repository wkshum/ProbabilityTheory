import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

/-

  # Lebesgue integral of simple function

-/


/-
\begin{defbox}{6.2}
The \textit{Lebesgue integral} of a simple function $X$ expressed as in (6.1) is defined by
\begin{equation}
\int X\, d\mu \triangleq \sum_{i=1}^{n} a_i \mu(A_i),
\tag{6.2}
\end{equation}
unless the summation contains both $\infty$ and $-\infty$, in which case the integral is not defined.
\end{defbox}
-/



open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/--
A single term in the summation in Definition 6.2.
-/
noncomputable def simpleFunctionIntegralTerm
    (μ : Measure Ω) (X : SimpleFunc Ω EReal) (x : EReal) : EReal :=
  x * (μ (X ⁻¹' {x}) : EReal)

/--
A simple function contributes a positive infinite term
if some term in the Definition 6.2 range-sum equals `⊤`.
(The top element `⊤` represents positive infinity in the extended
real number system)
-/
def simpleFunctionHasPosInf (μ : Measure Ω) (X : SimpleFunc Ω EReal)
  : Prop :=
  ∃ x ∈ X.range, simpleFunctionIntegralTerm μ X x = ⊤

/--
A simple function contributes a negative infinite term
if some term in the Definition 6.2 range-sum equals `⊥`.
(The bottom element `⊥` represents negative infinity in the extended
real number system)
-/
def simpleFunctionHasNegInf (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Prop :=
  ∃ x ∈ X.range, simpleFunctionIntegralTerm μ X x = ⊥

/--
The textbook simple-function integral is defined exactly when the summation
does not contain both `+∞` and `-∞`.
-/
def simpleFunctionIntegralDefined (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Prop :=
  ¬ (simpleFunctionHasPosInf μ X ∧ simpleFunctionHasNegInf μ X)

/--
Canonical value of the finite-range sum in Definition 6.2,
computed over the fiber partition of `X`.
-/
noncomputable def simpleFunctionIntegralValue
  (μ : Measure Ω) (X : SimpleFunc Ω EReal) : EReal :=
  Finset.sum X.range fun x => simpleFunctionIntegralTerm μ X x

/--  ## Definition 6.2
the Lebesgue integral of an `EReal`-valued simple function is
the finite-range sum `∑ x ∈ range(X), x μ(X⁻¹({x}))`, unless both `+∞` and
`-∞` occur with positive measure, in which case it is undefined.
-/
noncomputable def def_6_2 (μ : Measure Ω) (X : SimpleFunc Ω EReal) : Option EReal :=
  by
    classical
    exact
      if h : simpleFunctionIntegralDefined μ X then
        some (simpleFunctionIntegralValue μ X)
      else
        none

/-- Coercion from `ENNReal` preserves finite sums into `EReal`. -/
theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ENNReal) :
    ((∑ i ∈ s, f i : ENNReal) : EReal) = ∑ i ∈ s, ((f i : ENNReal) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih]

/--
Rewrite the Definition 6.2 in textbook after
mapping a finite-valued partition through a function `g`.
-/
theorem integralValue_map (μ : Measure Ω) {β : Type*}
    (g : β → EReal) (f : SimpleFunc Ω β) :
    simpleFunctionIntegralValue μ (f.map g) =
      ∑ x ∈ f.range, g x * (μ (f ⁻¹' {x}) : EReal) := by
  classical
  simp only [simpleFunctionIntegralValue, SimpleFunc.range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases SimpleFunc.mem_range.1 hb with ⟨a, rfl⟩
  simp only [simpleFunctionIntegralTerm]
  rw [SimpleFunc.map_preimage_singleton]
  have hsum :
      ((μ (f ⁻¹' ↑({b ∈ f.range | g b = g (f a)})) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)), ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    rw [← f.sum_measure_preimage_singleton (s := f.range.filter fun y => g y = g (f a)),
      ereal_coe_finset_sum]
  let s : Finset β := f.range.filter fun y => g y = g (f a)
  have hdist :
      g (f a) * ∑ y ∈ s, ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ s, g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert y s hy ih =>
        rw [Finset.sum_insert hy, Finset.sum_insert hy]
        have hy_nonneg : 0 ≤ ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
          positivity
        have hs_nonneg : 0 ≤ ∑ z ∈ s, ((μ (f ⁻¹' {z}) : ENNReal) : EReal) := by
          positivity
        rw [EReal.left_distrib_of_nonneg hy_nonneg hs_nonneg, ih]
  have hsum_mul :
      g (f a) * (μ (f ⁻¹' ↑({b ∈ f.range | g b = g (f a)})) : EReal) =
        g (f a) * ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    exact congrArg (fun t : EReal => g (f a) * t) hsum
  have hdist' :
      g (f a) * ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    simpa [s] using hdist
  have hpointwise :
      ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g (f a) * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) =
        ∑ y ∈ f.range.filter (fun y => g y = g (f a)),
          g y * ((μ (f ⁻¹' {y}) : ENNReal) : EReal) := by
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [(Finset.mem_filter.1 hy).2]
  simpa using hsum_mul.trans (hdist'.trans hpointwise)

/--
If `f ≤ g` pointwise, then the raw finite-range value used in Definition 6.2
is monotone.
-/
theorem integralValue_mono_fun (μ : Measure Ω) {f g : SimpleFunc Ω EReal} (hfg : f ≤ g) :
    simpleFunctionIntegralValue μ f ≤ simpleFunctionIntegralValue μ g := by
  classical
  calc
    simpleFunctionIntegralValue μ f
        = simpleFunctionIntegralValue μ ((f.pair g).map Prod.fst) := by
            simp
    _ = ∑ x ∈ (f.pair g).range, x.1 * (μ (f.pair g ⁻¹' {x}) : EReal) := by
          rw [integralValue_map (μ := μ) (g := Prod.fst)]
    _ ≤ ∑ x ∈ (f.pair g).range, x.2 * (μ (f.pair g ⁻¹' {x}) : EReal) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          have hxle : x.1 ≤ x.2 := by
            rcases SimpleFunc.mem_range.1 hx with ⟨ω, rfl⟩
            exact hfg ω
          have hμnonneg : 0 ≤ (μ (f.pair g ⁻¹' {x}) : EReal) := by
            positivity
          exact mul_le_mul_of_nonneg_right hxle hμnonneg
    _ = simpleFunctionIntegralValue μ ((f.pair g).map Prod.snd) := by
          rw [integralValue_map (μ := μ) (g := Prod.snd)]
    _ = simpleFunctionIntegralValue μ g := by
          simp

/-- Unfold `def_6_2` into its definedness predicate and summation value. -/
theorem def62_eq_some_iff (μ : Measure Ω) (f : SimpleFunc Ω EReal) (v : EReal) :
    def_6_2 μ f = some v ↔
      simpleFunctionIntegralDefined μ f ∧ simpleFunctionIntegralValue μ f = v := by
  classical
  unfold def_6_2
  by_cases h : simpleFunctionIntegralDefined μ f
  · simp [h]
  · simp [h]

/--
Textbook extended-real addition is undefined exactly for the two conflicting
sign combinations `⊤ + ⊥` and `⊥ + ⊤`.
-/
def textbookERealAddDefined (x y : EReal) : Prop :=
  ¬ ((x = ⊤ ∧ y = ⊥) ∨ (x = ⊥ ∧ y = ⊤))

/-- Partial extended-real addition matching the textbook's intended semantics. -/
noncomputable def textbookERealAdd (x y : EReal) : Option EReal := by
  classical
  exact
    if h : textbookERealAddDefined x y then
      some (x + y)
    else
      none

/-- Partial addition on Definition 6.2 integral values. -/
noncomputable def textbookIntegralAdd (u v : Option EReal) : Option EReal := by
  classical
  exact
    match u, v with
    | some x, some y => textbookERealAdd x y
    | _, _ => none

/--
Compatibility condition for the refined partition in the proof of Theorem 6.1(b).
This is the measure-sensitive circumstance under which the textbook calculation
of `∫ (X + Y)` is valid for the Definition 6.2 integral.
-/
def simpleFunctionIntegralAddCompatible (μ : Measure Ω)
    (X Y : SimpleFunc Ω EReal) : Prop :=
  ∀ p ∈ (X.pair Y).range,
    (p.1 + p.2) * (μ (X.pair Y ⁻¹' {p}) : EReal) =
      p.1 * (μ (X.pair Y ⁻¹' {p}) : EReal) +
        p.2 * (μ (X.pair Y ⁻¹' {p}) : EReal)

/--
The textbook left-hand side `∫ (X + Y)` for Definition 6.2: expose the sum only
on the branch where the refined-partition calculation is semantically valid.
-/
noncomputable def simpleFunctionIntegralAdd (μ : Measure Ω)
    (X Y : SimpleFunc Ω EReal) : Option EReal := by
  classical
  exact
    if h : simpleFunctionIntegralAddCompatible μ X Y then
      def_6_2 μ (X + Y)
    else
      none

/--
Ordered textbook summation of `n` extended-real terms, using the same partial
addition semantics as Definition 6.2 and Theorem 6.1.
-/
noncomputable def textbookERealFinSum : (n : ℕ) → (Fin n → EReal) → Option EReal
  | 0, _ => some 0
  | n + 1, f => textbookIntegralAdd (some (f 0)) (textbookERealFinSum n fun i => f i.succ)

/-- The empty ordered textbook sum is `0`. -/
theorem textbookERealFinSum_zero (f : Fin 0 → EReal) :
    textbookERealFinSum 0 f = some 0 := by
  simp [textbookERealFinSum]

/-- Unfold one step of the ordered textbook finite sum. -/
theorem textbookERealFinSum_succ (n : ℕ) (f : Fin (n + 1) → EReal) :
    textbookERealFinSum (n + 1) f =
      textbookIntegralAdd (some (f 0)) (textbookERealFinSum n fun i => f i.succ) := by
  simp [textbookERealFinSum]

/-- The ordered textbook sum of a single term is that term itself. -/
theorem textbookERealFinSum_one (f : Fin 1 → EReal) :
    textbookERealFinSum 1 f = some (f 0) := by
  rw [textbookERealFinSum_succ, textbookERealFinSum_zero]
  simp [textbookIntegralAdd, textbookERealAdd, textbookERealAddDefined]

/--
Ordered chaining of the textbook simple-function additivity interface from
Theorem 6.1(b), over a family indexed by `Fin n`.
-/
noncomputable def simpleFunctionIntegralFinChain (μ : Measure Ω) :
    (n : ℕ) → (Fin n → SimpleFunc Ω EReal) → Option EReal
  | 0, _ => some 0
  | n + 1, F =>
      match simpleFunctionIntegralFinChain μ n (fun i => F i.succ) with
      | some _ => simpleFunctionIntegralAdd μ (F 0) (∑ i : Fin n, F i.succ)
      | none => none

/-- The empty simple-function chain has integral `0`. -/
theorem simpleFunctionIntegralFinChain_zero (μ : Measure Ω) (F : Fin 0 → SimpleFunc Ω EReal) :
    simpleFunctionIntegralFinChain μ 0 F = some 0 := by
  simp [simpleFunctionIntegralFinChain]

/-- Unfold one step of the ordered simple-function integral chain. -/
theorem simpleFunctionIntegralFinChain_succ (μ : Measure Ω) (n : ℕ)
    (F : Fin (n + 1) → SimpleFunc Ω EReal) :
    simpleFunctionIntegralFinChain μ (n + 1) F =
      match simpleFunctionIntegralFinChain μ n (fun i => F i.succ) with
      | some _ => simpleFunctionIntegralAdd μ (F 0) (∑ i : Fin n, F i.succ)
      | none => none := by
  simp [simpleFunctionIntegralFinChain]

/--
The simple-function summands associated to a finite indicator representation
`∑ b_i 1_{B_i}`.
-/
noncomputable def indicatorRepresentationSummand
    (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) :
    Fin n → SimpleFunc Ω EReal :=
  fun i => (SimpleFunc.const Ω (b i)).restrict (B i)

/--
The simple function represented by the finite indicator family `∑ b_i 1_{B_i}`.
-/
noncomputable def indicatorRepresentationSimpleFunction
    (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : SimpleFunc Ω EReal :=
  ∑ i : Fin n, indicatorRepresentationSummand (Ω := Ω) n b B i

/--
The raw weighted sum `∑ b_i μ(B_i)` with the ordered partial-addition semantics
used by the Chapter 6 extended-real support layer.
-/
noncomputable def indicatorRepresentationWeightedSum
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  textbookERealFinSum n fun i => b i * (μ (B i) : EReal)

/--
The Theorem 6.2 representation integral interface: evaluate the represented
family in the same order as the textbook proof, by repeatedly adding the
indicator summands through the Chapter 6 simple-function additivity object.
-/
noncomputable def indicatorRepresentationIntegral
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  simpleFunctionIntegralFinChain μ n (indicatorRepresentationSummand (Ω := Ω) n b B)

/--
The left-hand-side Chapter 6 integral calculation for the represented finite
indicator family, chained in the same order as the representation.
-/
noncomputable def indicatorRepresentationIntegralChain
    (μ : Measure Ω) (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω) : Option EReal :=
  indicatorRepresentationIntegral (Ω := Ω) μ n b B

/-- Unfold the represented simple function at one successor step. -/
theorem indicatorRepresentationSimpleFunction_succ
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationSimpleFunction (Ω := Ω) (n + 1) b B =
      indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0 +
        indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ) := by
  simp [indicatorRepresentationSimpleFunction, indicatorRepresentationSummand, Fin.sum_univ_succ]

/-- Unfold the raw weighted sum at one successor step. -/
theorem indicatorRepresentationWeightedSum_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationWeightedSum (Ω := Ω) μ (n + 1) b B =
      textbookIntegralAdd
        (some (b 0 * (μ (B 0) : EReal)))
        (indicatorRepresentationWeightedSum (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ)) := by
  simp [indicatorRepresentationWeightedSum, textbookERealFinSum_succ]

/-- Unfold the Theorem 6.2 representation integral at one successor step. -/
theorem indicatorRepresentationIntegral_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationIntegral (Ω := Ω) μ (n + 1) b B =
      match indicatorRepresentationIntegral (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
      | some _ =>
          simpleFunctionIntegralAdd μ
            (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
            (indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ))
      | none => none := by
  congr! 2

/-- Unfold the left-hand-side chained representation integral at one successor step. -/
theorem indicatorRepresentationIntegralChain_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationIntegralChain (Ω := Ω) μ (n + 1) b B =
      match indicatorRepresentationIntegralChain (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
      | some _ =>
          simpleFunctionIntegralAdd μ
            (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
            (indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ))
      | none => none := by
  simpa [indicatorRepresentationIntegralChain] using
    (indicatorRepresentationIntegral_succ (Ω := Ω) (μ := μ) (n := n) (b := b) (B := B))




---------------------------
-- Connection to Mathlib
---------------------------



/-
An `ENNReal`-valued simple function has no negative-infinite integral term.
-/
theorem not_simpleFunctionHasNegInf_map_ennreal
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    ¬ simpleFunctionHasNegInf μ (X.map fun x : ENNReal => (x : EReal)) := by
  classical
  rintro ⟨x, hx_range, hx_bot⟩
  -- it is the coercion of some `ENNReal`, hence nonnegative.
  have hx_nonneg : 0 ≤ x := by
    rcases SimpleFunc.mem_range.1 hx_range with ⟨a, rfl⟩
    change (0 : EReal) ≤ ((X a : ENNReal) : EReal)
    exact_mod_cast (show (0 : ENNReal) ≤ X a from zero_le)

  -- The measure factor is also nonnegative.
  have hμ_nonneg :
      0 ≤ ((μ ((X.map fun x : ENNReal => (x : EReal)) ⁻¹' {x}) : ENNReal) : EReal) := by
    positivity

  -- Hence the corresponding summand is nonnegative.
  have hterm_nonneg :
      0 ≤ simpleFunctionIntegralTerm μ
          (X.map fun x : ENNReal => (x : EReal)) x := by
    unfold simpleFunctionIntegralTerm
    exact mul_nonneg hx_nonneg hμ_nonneg

  -- But `⊥ < 0`, so a nonnegative term cannot be `⊥`.
  have hbot_lt_zero : (⊥ : EReal) < 0 := by
    exact EReal.bot_lt_coe 0

  have hnot : ¬ simpleFunctionIntegralTerm μ
          (X.map fun x : ENNReal => (x : EReal)) x ≤ ⊥ := by
    intro hle
    exact not_le_of_gt hbot_lt_zero (le_trans hterm_nonneg hle)

  exact hnot (le_of_eq hx_bot)


/-
Definition 6.2 is defined for every nonnegative simple function.
-/
theorem simpleFunctionIntegralDefined_map_ennreal
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    simpleFunctionIntegralDefined μ (X.map fun x : ENNReal => (x : EReal)) := by
  -- By definition of `simpleFunctionIntegralDefined`, we need to show that if `X.map (fun x => x : ENNReal → EReal)` has a positive infinite term, it cannot have a negative infinite term.
  unfold simpleFunctionIntegralDefined
  intro h_contra
  obtain ⟨x, hx⟩ := h_contra;
  convert not_simpleFunctionHasNegInf_map_ennreal μ X hx using 1

/-
The textbook value agrees with Mathlib's `SimpleFunc.lintegral`.
-/
theorem simpleFunctionIntegralValue_map_ennreal_eq_lintegral
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    simpleFunctionIntegralValue μ (X.map fun x : ENNReal => (x : EReal)) =
      ((X.lintegral μ : ENNReal) : EReal) := by
  classical
  calc
    simpleFunctionIntegralValue μ (X.map fun x : ENNReal => (x : EReal))
        =
          ∑ x ∈ X.range,
            (x : EReal) * (μ (X ⁻¹' {x}) : EReal) := by
          simpa using
            integralValue_map μ (fun x : ENNReal => (x : EReal)) X
    _ =
        ((∑ x ∈ X.range, x * μ (X ⁻¹' {x}) : ENNReal) : EReal) := by
          rw [ereal_coe_finset_sum]
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact_mod_cast
            (show x * μ (X ⁻¹' {x}) = x * μ (X ⁻¹' {x}) from rfl)
    _ =
        ((X.lintegral μ : ENNReal) : EReal) := by
          rfl


/-
Definition 6.2 agrees with Mathlib's simple-function lower integral.
-/
theorem def_6_2_map_ennreal_eq_lintegral
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    def_6_2 μ (X.map fun x : ENNReal => (x : EReal)) =
      some ((X.lintegral μ : ENNReal) : EReal) := by
  classical
  unfold def_6_2
  simp [
    simpleFunctionIntegralDefined_map_ennreal μ X,
    simpleFunctionIntegralValue_map_ennreal_eq_lintegral μ X
  ]
