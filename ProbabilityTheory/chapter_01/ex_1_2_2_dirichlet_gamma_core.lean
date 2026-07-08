import Mathlib
import ToyApollo.Support.DirichletGamma

/-
TASK ID: ex_1_2_2
TYPE: Example_Proof
SOURCE PLAN: 37_chap1_mixed_singular
TASK CONTENT:
\textbf{Example 1.2.2 (Dirichlet Distribution)} \\
Consider a positive constant $\beta$ and $n$ positive constants $\alpha_1,\dots,\alpha_n$. For $i=1,2,\dots,n$, let $X_i$ be independent Gamma distributed random variables with shape parameter $\alpha_i$ and scale parameter $\beta$, which we denote by $\Gamma(\alpha_i,\beta)$. The pdf of $X_i$ is given by (1.2).

Define
\[
V\triangleq X_1+X_2+\cdots +X_n
\]
as the sum of these Gamma random variables. The components of the random vector
\[
\mathbf{Y}=(Y_1,Y_2,\dots,Y_n)\triangleq (X_1/V,X_2/V,\dots,X_n/V)
\]
are distributed according to the Dirichlet distribution with parameters $\alpha_1,\dots,\alpha_n$. The random vector $\mathbf{Y}$ lies in the region defined by $y_1+y_2+\cdots +y_n=1$ and $y_i\ge 0$ for all $i$ with probability $1$. The Dirichlet distribution is singular because this region has zero volume in $\mathbb{R}^n$. A sample scatter plot is shown in Fig. 1.2.

\textbf{Figure 1.2.} A scatter plot of Dirichlet distribution in Example 1.2.2, with parameters $\alpha_1=\alpha_3=1$ and $\alpha_2=2$. All sample points are on the plane $x+y+z=1$.

The Dirichlet distribution plays a prominent role in the method of latent Dirichlet allocation, a popular technique in natural language processing. Although the Dirichlet distribution does not have a pdf, we can project the random variables to an $(n-1)$-dimensional subspace and describe the probability distribution in the lower-dimensional space. Since the $n$ random values must sum to $1$, we can consider the first $n-1$ components only. The pdf of $Y_1,\dots,Y_{n-1}$ is given by
\begin{equation}
f(y_1,\dots,y_{n-1})
=
\frac{\Gamma(\alpha_1+\cdots +\alpha_n)}{\prod_{k=1}^{n}\Gamma(\alpha_k)}
\left(\prod_{k=1}^{n-1} y_k^{\alpha_k-1}\right)
(1-y_1-\cdots -y_{n-1})^{\alpha_n-1},
\tag{1.4}
\end{equation}
for $(y_1,y_2,\dots,y_{n-1})$ with $y_1+y_2+\cdots +y_{n-1}\le 1$ and $y_k\ge 0$ for $k=1,\dots,n-1$. We can compute probabilities pertaining to this distribution using this lower-dimensional pdf. When $n=2$, the pdf of $Y_1$ reduces to a Beta distribution,
\[
f(y)=
\frac{\Gamma(\alpha_1+\alpha_2)}{\Gamma(\alpha_1)\Gamma(\alpha_2)}
y^{\alpha_1-1}(1-y)^{\alpha_2-1}
\]
for $0\le y\le 1$.

In Python, we can use the \texttt{dirichlet} function in the \texttt{numpy.random} module to generate a Dirichlet-distributed random vector. The following is an example of drawing a number of samples from a Dirichlet distribution with parameters $(1,1,2)$ using the default random number generator.
\begin{verbatim}
from numpy import random
rng = random.default_rng()      # default random number generator
X = rng.dirichlet((1, 1, 2), 8) # draw 8 samples
print(X)                        # print the random samples as an array
\end{verbatim}

A sample run of this program yields the following output:
\begin{verbatim}
[[0.1844921  0.51764633 0.29786156]
 [0.1943196  0.18637496 0.61930544]
 [0.06687522 0.28048234 0.65264245]
 [0.50722478 0.14452905 0.34824617]
 [0.22316573 0.05919519 0.71763908]
 [0.28439455 0.22016395 0.4954415 ]
 [0.18963489 0.13846004 0.67190507]
 [0.20121907 0.28116356 0.51761736]]
\end{verbatim}

Each row of this array represents a sample from the Dirichlet distribution. Note that the sum of the numbers in each row is equal to $1$, as required by the Dirichlet distribution. In this example, we observe that the third component of each sample is often the largest, due to its high weight in the parameter vector $(1,1,2)$.

In each of the previous examples, there are sets with zero length or area that occur with strictly positive probability. As a result, the probability distributions associated with these examples cannot be represented by probability density functions.

We formally define a singular random variable as follows.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## Shared Gamma/Dirichlet support wrappers -/

/-- Sum of the positive Gamma variables before normalization. -/
def ex122GammaTotal {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

/-- The simplex where the normalized Dirichlet vector lives. -/
def ex122DirichletSimplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) = 1}

/-- The simplex is contained in the affine hyperplane whose coordinates sum to one,
so it has zero ambient volume. -/
theorem ex122DirichletSimplex_volume_zero (n : ℕ) :
    (volume : Measure (Fin (n + 1) → ℝ)) (ex122DirichletSimplex n) = 0 := by
  simpa [ex122DirichletSimplex, DirichletFullSimplex] using
    DirichletFullSimplex_volume_zero_succ n

/-- The Dirichlet normalization map `Y_i = X_i / (∑ j, X_j)`. -/
def ex122NormalizedVector {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i / ex122GammaTotal x

theorem ex122_normalized_sum {n : ℕ} (x : Fin n → ℝ) (hV : ex122GammaTotal x ≠ 0) :
    (∑ i, ex122NormalizedVector x i) = 1 := by
  simpa [ex122GammaTotal, ex122NormalizedVector, sourceNormalizedVector, gammaVectorTotal] using
    sourceNormalizedVector_sum x hV

theorem ex122_normalized_nonneg {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < ex122GammaTotal x) :
    ∀ i, 0 ≤ ex122NormalizedVector x i := by
  intro i
  exact div_nonneg (hx i) hV.le

theorem ex122_normalized_mem_simplex {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < ex122GammaTotal x) :
    ex122NormalizedVector x ∈ ex122DirichletSimplex n := by
  simpa [ex122DirichletSimplex, ex122GammaTotal, ex122NormalizedVector] using
    sourceNormalizedVector_mem_fullSimplex x hx hV

theorem measurable_ex122GammaTotal {n : ℕ} :
    Measurable (ex122GammaTotal : (Fin n → ℝ) → ℝ) := by
  unfold ex122GammaTotal
  fun_prop

theorem measurable_ex122NormalizedVector {n : ℕ} :
    Measurable (ex122NormalizedVector : (Fin n → ℝ) → Fin n → ℝ) := by
  unfold ex122NormalizedVector ex122GammaTotal
  fun_prop

theorem measurableSet_ex122DirichletSimplex (n : ℕ) :
    MeasurableSet (ex122DirichletSimplex n) := by
  simpa [ex122DirichletSimplex, DirichletFullSimplex] using
    measurableSet_DirichletFullSimplex (n + 1)

/-! ## Probability spine for the normalized-Gamma construction -/

/-- Mathlib's Gamma law uses shape/rate. The source uses shape/scale `β`, so
the rate is `β⁻¹`. -/
def ex122GammaScaleLaw (α β : ℝ) : Measure ℝ :=
  ProbabilityTheory.gammaMeasure α β⁻¹

theorem ex122GammaScaleLaw_eq_withDensity_gammaPDFReal (α β : ℝ) :
    ex122GammaScaleLaw α β =
      (volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (ProbabilityTheory.gammaPDFReal α β⁻¹ x)) := by
  unfold ex122GammaScaleLaw ProbabilityTheory.gammaMeasure ProbabilityTheory.gammaPDF
  rfl

theorem ex122GammaScaleLaw_isProbability {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122GammaScaleLaw α β) := by
  simpa [ex122GammaScaleLaw] using gammaScaleLaw_isProbability hα hβ

instance ex122GammaScaleLaw_noAtoms (α β : ℝ) :
    NoAtoms (ex122GammaScaleLaw α β) := by
  unfold ex122GammaScaleLaw ProbabilityTheory.gammaMeasure
  infer_instance

instance ex122GammaScaleLaw_sigmaFinite (α β : ℝ) :
    SigmaFinite (ex122GammaScaleLaw α β) := by
  unfold ex122GammaScaleLaw ProbabilityTheory.gammaMeasure ProbabilityTheory.gammaPDF
  infer_instance

theorem ex122GammaScaleLaw_positive_ae {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    ∀ᵐ x ∂ex122GammaScaleLaw α β, 0 < x := by
  simpa [ex122GammaScaleLaw] using gammaScaleLaw_positive_ae hα hβ

/-- Product law of the independent Gamma variables before normalization. -/
def ex122GammaProductLaw {n : ℕ} (α : Fin n → ℝ) (β : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun i => ex122GammaScaleLaw (α i) β

theorem ex122GammaProductLaw_isProbability {n : ℕ} (α : Fin n → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122GammaProductLaw α β) := by
  simpa [ex122GammaProductLaw] using gammaProductLaw_isProbability α hα hβ

theorem ex122GammaProductLaw_coordinates_positive_ae {n : ℕ}
    (α : Fin n → ℝ) {β : ℝ} (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ∀ᵐ x ∂ex122GammaProductLaw α β, ∀ i, 0 < x i := by
  simpa [ex122GammaProductLaw] using gammaProductLaw_coordinates_positive_ae α hα hβ

theorem ex122GammaProductLaw_total_positive_ae {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ} (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ∀ᵐ x ∂ex122GammaProductLaw α β, 0 < ex122GammaTotal x := by
  simpa [ex122GammaProductLaw, ex122GammaTotal] using
    gammaProductLaw_total_positive_ae (n := n + 1) (Nat.succ_pos n) α hα hβ

/-- The Dirichlet law is the pushforward of the independent Gamma product law
under the normalization map. -/
def ex122DirichletLaw {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ) :
    Measure (Fin (n + 1) → ℝ) :=
  Measure.map (fun x : Fin (n + 1) → ℝ => ex122NormalizedVector x)
    (ex122GammaProductLaw α β)

theorem ex122DirichletLaw_isProbability {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    IsProbabilityMeasure (ex122DirichletLaw α β) := by
  simpa [ex122DirichletLaw] using DirichletLaw_isProbability α hα hβ

theorem ex122DirichletLaw_supported_on_simplex {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ∀ᵐ y ∂ex122DirichletLaw α β, y ∈ ex122DirichletSimplex n := by
  simpa [ex122DirichletLaw, ex122DirichletSimplex, ex122NormalizedVector,
    ex122GammaProductLaw, ex122GammaScaleLaw, DirichletLaw, DirichletFullSimplex,
    sourceNormalizedVector, gammaVectorTotal, gammaProductLaw, gammaScaleLaw] using
    DirichletLaw_supported_on_simplex (n := n + 1) (Nat.succ_pos n) α hα hβ

theorem ex122DirichletLaw_simplex_probability_one {n : ℕ}
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β) :
    ex122DirichletLaw α β (ex122DirichletSimplex n) = 1 := by
  simpa [ex122DirichletLaw, ex122DirichletSimplex, ex122NormalizedVector,
    ex122GammaProductLaw, ex122GammaScaleLaw, DirichletLaw, DirichletFullSimplex,
    sourceNormalizedVector, gammaVectorTotal, gammaProductLaw, gammaScaleLaw] using
    DirichletLaw_simplex_probability_one (n := n + 1) (Nat.succ_pos n) α hα hβ

/-- A random vector whose coordinates have the source Gamma laws and are
independent has joint law equal to the Gamma product law. -/
theorem ex122_independent_gamma_joint_hasLaw
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : Fin (n + 1) → ℝ) (β : ℝ)
    (X : Fin (n + 1) → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (ex122GammaScaleLaw (α i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    HasLaw (fun ω i => X i ω) (ex122GammaProductLaw α β) P := by
  simpa [ex122GammaScaleLaw, ex122GammaProductLaw] using
    independent_gamma_joint_hasLaw P α β X hXlaw hIndep

theorem ex122_normalization_map_hasLaw_dirichlet
    {n : ℕ} (α : Fin (n + 1) → ℝ) (β : ℝ) :
    HasLaw
      (fun x : Fin (n + 1) → ℝ => ex122NormalizedVector x)
      (ex122DirichletLaw α β)
      (ex122GammaProductLaw α β) := by
  simpa [ex122NormalizedVector, ex122DirichletLaw, ex122GammaProductLaw] using
    normalization_map_hasLaw_dirichlet α β

/-- Source probability spine: independent Gamma variables normalized by their
sum have the Dirichlet law defined as the normalization pushforward. -/
theorem ex122_independent_gamma_normalized_hasLaw_dirichlet
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : Fin (n + 1) → ℝ) (β : ℝ)
    (X : Fin (n + 1) → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (ex122GammaScaleLaw (α i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    HasLaw
      (fun ω => ex122NormalizedVector (fun i => X i ω))
      (ex122DirichletLaw α β)
      P := by
  simpa [ex122GammaScaleLaw, ex122NormalizedVector, ex122DirichletLaw] using
    independent_gamma_normalized_hasLaw_dirichlet P α β X hXlaw hIndep

theorem ex122_independent_gamma_normalized_simplex_ae
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (α : Fin (n + 1) → ℝ) {β : ℝ}
    (hα : ∀ i, 0 < α i) (hβ : 0 < β)
    (X : Fin (n + 1) → Ω → ℝ)
    (hXlaw : ∀ i, HasLaw (X i) (ex122GammaScaleLaw (α i) β) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ∀ᵐ ω ∂P,
      ex122NormalizedVector (fun i => X i ω) ∈ ex122DirichletSimplex n := by
  have hlaw := ex122_independent_gamma_normalized_hasLaw_dirichlet P α β X hXlaw hIndep
  exact (hlaw.ae_iff (measurableSet_setOf.1 (measurableSet_ex122DirichletSimplex n))).2
    (ex122DirichletLaw_supported_on_simplex α hα hβ)
