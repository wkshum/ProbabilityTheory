import Mathlib

/-
TASK ID: prob_1_5
TYPE: Problem
SOURCE PLAN: 39_chap1_problems
TASK CONTENT:
\textbf{1.5.} Suppose $X$ and $Y$ are zero-mean, independent, and jointly Gaussian random variables with variance $E[X^2]=E[Y^2]=1$. Let $U$ and $V$ be a linear transformation of $X$ and $Y$ computed by
\[
\begin{bmatrix}
U\\
V
\end{bmatrix}
=
\begin{bmatrix}
a & b\\
b & a
\end{bmatrix}
\begin{bmatrix}
X\\
Y
\end{bmatrix},
\]
where $a$ and $b$ are constants:
\begin{enumerate}[label=(\alph*)]
    \item Find all combinations of $a$ and $b$ such that the random vector $(U,V)$ is singular.
    \item Write down the joint pdf of $(U,V)$ when it is not singular.
    \item How would you describe $(U,V)$ in the singular case?
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW
open MeasureTheory Set Real ProbabilityTheory

noncomputable section

/-- The transformed pair `(U, V)` produced from `X` and `Y`. -/
noncomputable def uvPair {Ω : Type*} (a b : ℝ) (X Y : Ω → ℝ) : Ω → ℝ × ℝ :=
  fun ω => (a * X ω + b * Y ω, b * X ω + a * Y ω)

/-- The linear map on `ℝ × ℝ` sending `(x, y)` to `(a*x + b*y, b*x + a*y)`. -/
noncomputable def uvLinearMap (a b : ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun p := (a * p.1 + b * p.2, b * p.1 + a * p.2)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' c p := by
    ext <;> simp <;> ring

/-- The covariance matrix of `(U, V)` when `X` and `Y` are centered independent unit Gaussians. -/
noncomputable def uvCovarianceMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a ^ 2 + b ^ 2, 2 * a * b; 2 * a * b, a ^ 2 + b ^ 2]

/--
The joint pdf of `(U, V)` in the nonsingular case `a ≠ ± b`.

This is the bivariate Gaussian density determined by the covariance matrix
`[[a^2 + b^2, 2ab], [2ab, a^2 + b^2]]`.
-/
noncomputable def uvJointPdf (a b u v : ℝ) : ℝ :=
  (1 / (2 * Real.pi * |a ^ 2 - b ^ 2|)) *
    Real.exp
      (-(((a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) - 4 * a * b * u * v) /
          (2 * (a ^ 2 - b ^ 2) ^ 2)))

/-- The joint density of two independent standard real Gaussians on `ℝ × ℝ`. -/
noncomputable def standardGaussianPairPdf (p : ℝ × ℝ) : ENNReal :=
  gaussianPDF (0 : ℝ) (1 : NNReal) p.1 * gaussianPDF (0 : ℝ) (1 : NNReal) p.2

/-- The explicit inverse linear map in the nonsingular case. -/
noncomputable def uvInverseLinearMap (a b : ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun p :=
    ((a * p.1 - b * p.2) / (a ^ 2 - b ^ 2),
      (-b * p.1 + a * p.2) / (a ^ 2 - b ^ 2))
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' c p := by
    ext <;> simp <;> ring

/-- The determinant of the source linear map is the expected `a^2 - b^2`. -/
theorem uvLinearMap_det (a b : ℝ) :
    LinearMap.det (uvLinearMap a b) = a ^ 2 - b ^ 2 := by
  have hlin :
      uvLinearMap a b =
        Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
          !![a, b; b, a] := by
    rw [Matrix.toLin_finTwoProd]
    ext <;> simp [uvLinearMap]
  rw [hlin, LinearMap.det_toLin, Matrix.det_fin_two]
  simp
  ring

/-- The explicit inverse is a left inverse of `uvLinearMap`. -/
theorem uvInverseLinearMap_left {a b : ℝ} (hdet : a ^ 2 - b ^ 2 ≠ 0)
    (p : ℝ × ℝ) :
    uvInverseLinearMap a b (uvLinearMap a b p) = p := by
  ext <;> simp [uvInverseLinearMap, uvLinearMap]
  · field_simp [hdet]
    ring
  · field_simp [hdet]
    ring

/-- The explicit inverse is a right inverse of `uvLinearMap`. -/
theorem uvInverseLinearMap_right {a b : ℝ} (hdet : a ^ 2 - b ^ 2 ≠ 0)
    (p : ℝ × ℝ) :
    uvLinearMap a b (uvInverseLinearMap a b p) = p := by
  ext <;> simp [uvInverseLinearMap, uvLinearMap]
  · field_simp [hdet]
    ring
  · field_simp [hdet]
    ring

/-- The nonsingular linear map as a measurable equivalence with the explicit inverse. -/
noncomputable def uvLinearMeasurableEquiv (a b : ℝ) (hdet : a ^ 2 - b ^ 2 ≠ 0) :
    ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun := uvLinearMap a b
  invFun := uvInverseLinearMap a b
  left_inv := uvInverseLinearMap_left hdet
  right_inv := uvInverseLinearMap_right hdet
  measurable_toFun :=
    Continuous.measurable (LinearMap.continuous_of_finiteDimensional (uvLinearMap a b))
  measurable_invFun :=
    Continuous.measurable (LinearMap.continuous_of_finiteDimensional (uvInverseLinearMap a b))

/-- Transporting a density through a measurable equivalence composes it with the inverse. -/
theorem map_withDensity_measurableEquiv {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (e : α ≃ᵐ α) {f : α → ENNReal} (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  rw [withDensity_apply _ (e.measurable hs)]
  rw [withDensity_apply _ hs]
  convert
    (setLIntegral_map (μ := μ) (g := e) (f := fun y => f (e.symm y)) hs
      (hf.comp e.symm.measurable) e.measurable).symm using 1
  simp

/-- The standard pair density is measurable. -/
theorem standardGaussianPairPdf_measurable : Measurable standardGaussianPairPdf := by
  exact ((measurable_gaussianPDF (0 : ℝ) (1 : NNReal)).comp measurable_fst).mul
    ((measurable_gaussianPDF (0 : ℝ) (1 : NNReal)).comp measurable_snd)

/-- The quadratic form produced by substituting the inverse coordinates. -/
theorem uvInverse_quadratic {a b : ℝ} (hdet : a ^ 2 - b ^ 2 ≠ 0) (u v : ℝ) :
    ((a * u - b * v) / (a ^ 2 - b ^ 2)) ^ 2 +
        ((-b * u + a * v) / (a ^ 2 - b ^ 2)) ^ 2 =
      ((a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) - 4 * a * b * u * v) /
        (a ^ 2 - b ^ 2) ^ 2 := by
  field_simp [hdet]
  ring

/-- The real-valued inverse/Jacobian density simplifies to the closed-form density. -/
theorem prob_1_5_inverse_density_real {a b : ℝ} (hdet : a ^ 2 - b ^ 2 ≠ 0)
    (u v : ℝ) :
    |(a ^ 2 - b ^ 2)⁻¹| *
        gaussianPDFReal (0 : ℝ) (1 : NNReal) ((a * u - b * v) / (a ^ 2 - b ^ 2)) *
        gaussianPDFReal (0 : ℝ) (1 : NNReal) ((-b * u + a * v) / (a ^ 2 - b ^ 2)) =
      uvJointPdf a b u v := by
  let x := (a * u - b * v) / (a ^ 2 - b ^ 2)
  let y := (-b * u + a * v) / (a ^ 2 - b ^ 2)
  let q := ((a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) - 4 * a * b * u * v) /
    (a ^ 2 - b ^ 2) ^ 2
  have hquad : x ^ 2 + y ^ 2 = q := by
    dsimp [x, y, q]
    exact uvInverse_quadratic hdet u v
  have hconst :
      (√Real.pi)⁻¹ * (√(2 : ℝ))⁻¹ * ((√Real.pi)⁻¹ * (√(2 : ℝ))⁻¹) =
        Real.pi⁻¹ * (2 : ℝ)⁻¹ := by
    field_simp [Real.pi_ne_zero, (Real.sqrt_ne_zero').mpr Real.pi_pos,
      (Real.sqrt_ne_zero').mpr (by norm_num : (0 : ℝ) < 2)]
    try rw [Real.sq_sqrt (le_of_lt Real.pi_pos),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    try ring_nf
  have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(y ^ 2) / 2) =
      Real.exp (-(q / 2)) := by
    rw [← Real.exp_add]
    congr 1
    rw [← hquad]
    ring
  have habsdet : |a ^ 2 - b ^ 2| ≠ 0 := abs_ne_zero.mpr hdet
  calc
    |(a ^ 2 - b ^ 2)⁻¹| *
        gaussianPDFReal (0 : ℝ) (1 : NNReal) ((a * u - b * v) / (a ^ 2 - b ^ 2)) *
        gaussianPDFReal (0 : ℝ) (1 : NNReal) ((-b * u + a * v) / (a ^ 2 - b ^ 2)) =
        |a ^ 2 - b ^ 2|⁻¹ *
          ((√Real.pi)⁻¹ * (√(2 : ℝ))⁻¹ * ((√Real.pi)⁻¹ * (√(2 : ℝ))⁻¹)) *
          (Real.exp (-(x ^ 2) / 2) * Real.exp (-(y ^ 2) / 2)) := by
          simp [gaussianPDFReal, x, y, abs_inv]
          ring
    _ = |a ^ 2 - b ^ 2|⁻¹ * (Real.pi⁻¹ * (2 : ℝ)⁻¹) * Real.exp (-(q / 2)) := by
          rw [hconst, hexp]
    _ = uvJointPdf a b u v := by
          simp [uvJointPdf, q]
          field_simp [hdet, habsdet, Real.pi_ne_zero]
          try simp [hdet]

/-- The inverse-density form from the Jacobian theorem is the closed-form `uvJointPdf`. -/
theorem prob_1_5_inverse_density_eq_uvJointPdf
    (a b : ℝ) (hneq₁ : a ≠ b) (hneq₂ : a ≠ -b) :
    (fun p : ℝ × ℝ =>
        ENNReal.ofReal |(a ^ 2 - b ^ 2)⁻¹| *
          standardGaussianPairPdf (uvInverseLinearMap a b p)) =
      (fun p : ℝ × ℝ => ENNReal.ofReal (uvJointPdf a b p.1 p.2)) := by
  have hdet : a ^ 2 - b ^ 2 ≠ 0 := by
    intro hz
    have hsing : a = b ∨ a = -b := by
      grind
    rcases hsing with hab | hab
    · exact hneq₁ hab
    · exact hneq₂ hab
  funext p
  let x := (a * p.1 - b * p.2) / (a ^ 2 - b ^ 2)
  let y := (-b * p.1 + a * p.2) / (a ^ 2 - b ^ 2)
  have hx_nonneg : 0 ≤ gaussianPDFReal (0 : ℝ) (1 : NNReal) x := by
    simp [gaussianPDFReal]
    positivity
  have hfac_nonneg : 0 ≤ |(a ^ 2 - b ^ 2)⁻¹| := abs_nonneg _
  calc
    ENNReal.ofReal |(a ^ 2 - b ^ 2)⁻¹| * standardGaussianPairPdf (uvInverseLinearMap a b p) =
        ENNReal.ofReal |(a ^ 2 - b ^ 2)⁻¹| *
          (ENNReal.ofReal (gaussianPDFReal (0 : ℝ) (1 : NNReal) x) *
            ENNReal.ofReal (gaussianPDFReal (0 : ℝ) (1 : NNReal) y)) := by
          simp [standardGaussianPairPdf, gaussianPDF, uvInverseLinearMap, x, y]
    _ = ENNReal.ofReal (|(a ^ 2 - b ^ 2)⁻¹| *
          (gaussianPDFReal (0 : ℝ) (1 : NNReal) x *
            gaussianPDFReal (0 : ℝ) (1 : NNReal) y)) := by
          rw [← ENNReal.ofReal_mul hx_nonneg]
          rw [← ENNReal.ofReal_mul hfac_nonneg]
    _ = ENNReal.ofReal (uvJointPdf a b p.1 p.2) := by
          rw [show |(a ^ 2 - b ^ 2)⁻¹| *
              (gaussianPDFReal (0 : ℝ) (1 : NNReal) x *
                gaussianPDFReal (0 : ℝ) (1 : NNReal) y) =
              |(a ^ 2 - b ^ 2)⁻¹| * gaussianPDFReal (0 : ℝ) (1 : NNReal) x *
                gaussianPDFReal (0 : ℝ) (1 : NNReal) y by ring]
          rw [prob_1_5_inverse_density_real hdet]

/--
Jacobian landing theorem up to the final closed-form simplification of the Gaussian density.

This is the measure-theoretic change-of-variables step: the linear image of the standard pair
density is Lebesgue density given by the explicit inverse coordinates and the Jacobian factor.
-/
theorem prob_1_5_jacobian_inverse_density
    (a b : ℝ) (hneq₁ : a ≠ b) (hneq₂ : a ≠ -b) :
    Measure.map (uvLinearMap a b)
        ((volume : Measure (ℝ × ℝ)).withDensity standardGaussianPairPdf) =
      (volume : Measure (ℝ × ℝ)).withDensity
        (fun p =>
          ENNReal.ofReal |(a ^ 2 - b ^ 2)⁻¹| *
            standardGaussianPairPdf (uvInverseLinearMap a b p)) := by
  have hdet : a ^ 2 - b ^ 2 ≠ 0 := by
    intro hz
    have hsing : a = b ∨ a = -b := by
      grind
    rcases hsing with hab | hab
    · exact hneq₁ hab
    · exact hneq₂ hab
  let e := uvLinearMeasurableEquiv a b hdet
  have htransport :=
    map_withDensity_measurableEquiv (μ := (volume : Measure (ℝ × ℝ))) e
      standardGaussianPairPdf_measurable
  have hdetlin : LinearMap.det (uvLinearMap a b) ≠ 0 := by
    rw [uvLinearMap_det]
    exact hdet
  calc
    Measure.map (uvLinearMap a b)
        ((volume : Measure (ℝ × ℝ)).withDensity standardGaussianPairPdf) =
        (Measure.map (uvLinearMap a b) (volume : Measure (ℝ × ℝ))).withDensity
          (fun p => standardGaussianPairPdf (uvInverseLinearMap a b p)) := by
          simpa [e, uvLinearMeasurableEquiv] using htransport
    _ =
        (ENNReal.ofReal |(a ^ 2 - b ^ 2)⁻¹| •
          (volume : Measure (ℝ × ℝ))).withDensity
          (fun p => standardGaussianPairPdf (uvInverseLinearMap a b p)) := by
          rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
            (volume : Measure (ℝ × ℝ)) hdetlin]
          rw [uvLinearMap_det]
    _ =
        (volume : Measure (ℝ × ℝ)).withDensity
          (fun p =>
            ENNReal.ofReal |(a ^ 2 - b ^ 2)⁻¹| *
              standardGaussianPairPdf (uvInverseLinearMap a b p)) := by
          rw [MeasureTheory.withDensity_smul_measure]
          rw [← MeasureTheory.withDensity_smul]
          · rfl
          · exact standardGaussianPairPdf_measurable.comp
              (Continuous.measurable
                (LinearMap.continuous_of_finiteDimensional (uvInverseLinearMap a b)))

/--
The source-route joint law of `(X, Y)`: independent standard real Gaussians have the product
Lebesgue density.
-/
theorem prob_1_5_standard_pair_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ)
    (hX : Measure.map X P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hY : Measure.map Y P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hindep : ProbabilityTheory.IndepFun X Y P) :
    Measure.map (fun ω => (X ω, Y ω)) P =
      (volume : Measure (ℝ × ℝ)).withDensity standardGaussianPairPdf := by
  have hXm : AEMeasurable X P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hX]
    simp [NeZero.ne]
  have hYm : AEMeasurable Y P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hY]
    simp [NeZero.ne]
  have hpair :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hXm hYm).1 hindep
  rw [hX, hY] at hpair
  calc
    Measure.map (fun ω => (X ω, Y ω)) P =
        (gaussianReal (0 : ℝ) (1 : NNReal)).prod
          (gaussianReal (0 : ℝ) (1 : NNReal)) := hpair
    _ =
        ((volume : Measure ℝ).withDensity (gaussianPDF (0 : ℝ) (1 : NNReal))).prod
          ((volume : Measure ℝ).withDensity (gaussianPDF (0 : ℝ) (1 : NNReal))) := by
          rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0)]
    _ =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
          standardGaussianPairPdf := by
          rw [MeasureTheory.prod_withDensity
            (measurable_gaussianPDF (0 : ℝ) (1 : NNReal))
            (measurable_gaussianPDF (0 : ℝ) (1 : NNReal))]
          rfl
    _ = (volume : Measure (ℝ × ℝ)).withDensity standardGaussianPairPdf := by
          rfl

/--
The transformed law is the push-forward of the standard joint Gaussian density through the source
linear map.  This keeps the real probabilistic route in the public theorem surface instead of only
restating the closed-form density formula.
-/
theorem prob_1_5_transformed_law_as_linear_image
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a b : ℝ)
    (hX : Measure.map X P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hY : Measure.map Y P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hindep : ProbabilityTheory.IndepFun X Y P) :
    Measure.map (uvPair a b X Y) P =
      Measure.map (uvLinearMap a b)
        ((volume : Measure (ℝ × ℝ)).withDensity standardGaussianPairPdf) := by
  have hXm : AEMeasurable X P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hX]
    simp [NeZero.ne]
  have hYm : AEMeasurable Y P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hY]
    simp [NeZero.ne]
  have hpairm : AEMeasurable (fun ω => (X ω, Y ω)) P := hXm.prodMk hYm
  have hlinm :
      AEMeasurable (uvLinearMap a b)
        (Measure.map (fun ω => (X ω, Y ω)) P) := by
    exact (Continuous.measurable
      (LinearMap.continuous_of_finiteDimensional (uvLinearMap a b))).aemeasurable
  calc
    Measure.map (uvPair a b X Y) P =
        Measure.map ((uvLinearMap a b) ∘ fun ω => (X ω, Y ω)) P := by
          rfl
    _ = Measure.map (uvLinearMap a b)
        (Measure.map (fun ω => (X ω, Y ω)) P) := by
          exact (AEMeasurable.map_map_of_aemeasurable hlinm hpairm).symm
    _ = Measure.map (uvLinearMap a b)
        ((volume : Measure (ℝ × ℝ)).withDensity standardGaussianPairPdf) := by
          rw [prob_1_5_standard_pair_law P X Y hX hY hindep]

/-- In the nonsingular case, `(U, V)` has the closed-form joint Lebesgue density. -/
theorem prob_1_5_nonsingular_joint_pdf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a b : ℝ)
    (hX : Measure.map X P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hY : Measure.map Y P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hindep : ProbabilityTheory.IndepFun X Y P)
    (hneq₁ : a ≠ b) (hneq₂ : a ≠ -b) :
    Measure.map (uvPair a b X Y) P =
      (volume : Measure (ℝ × ℝ)).withDensity
        (fun p => ENNReal.ofReal (uvJointPdf a b p.1 p.2)) := by
  calc
    Measure.map (uvPair a b X Y) P =
        Measure.map (uvLinearMap a b)
          ((volume : Measure (ℝ × ℝ)).withDensity standardGaussianPairPdf) := by
          exact prob_1_5_transformed_law_as_linear_image P X Y a b hX hY hindep
    _ =
        (volume : Measure (ℝ × ℝ)).withDensity
          (fun p =>
            ENNReal.ofReal |(a ^ 2 - b ^ 2)⁻¹| *
              standardGaussianPairPdf (uvInverseLinearMap a b p)) := by
          exact prob_1_5_jacobian_inverse_density a b hneq₁ hneq₂
    _ =
        (volume : Measure (ℝ × ℝ)).withDensity
          (fun p => ENNReal.ofReal (uvJointPdf a b p.1 p.2)) := by
          rw [prob_1_5_inverse_density_eq_uvJointPdf a b hneq₁ hneq₂]

/-
Part (a): the transformation matrix `!![a, b; b, a]` is singular iff `a = b` or `a = -b`.
-/
theorem prob_1_5_part_a (a b : ℝ) :
    a ^ 2 - b ^ 2 = 0 ↔ (a = b ∨ a = -b) := by
  grind

/--
Part (b): when `a ≠ ± b`, the transformed pair `(U, V)` has the nonsingular bivariate Gaussian
joint pdf determined by the covariance matrix of `(U, V)`.
-/
theorem prob_1_5_part_b
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a b u v : ℝ)
    (hX : Measure.map X P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hY : Measure.map Y P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hindep : ProbabilityTheory.IndepFun X Y P)
    (hneq₁ : a ≠ b) (hneq₂ : a ≠ -b) :
    Measure.map (uvPair a b X Y) P =
        (volume : Measure (ℝ × ℝ)).withDensity
          (fun p => ENNReal.ofReal (uvJointPdf a b p.1 p.2)) ∧
      0 < |a ^ 2 - b ^ 2| ∧
      uvCovarianceMatrix a b = !![a ^ 2 + b ^ 2, 2 * a * b; 2 * a * b, a ^ 2 + b ^ 2] ∧
      uvJointPdf a b u v =
        (1 / (2 * Real.pi * |a ^ 2 - b ^ 2|)) *
          Real.exp
            (-(((a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) - 4 * a * b * u * v) /
                (2 * (a ^ 2 - b ^ 2) ^ 2))) := by
  have hdet_ne : a ^ 2 - b ^ 2 ≠ 0 := by
    intro hdet
    rcases (prob_1_5_part_a a b).1 hdet with hab | hab
    · exact hneq₁ hab
    · exact hneq₂ hab
  refine ⟨prob_1_5_nonsingular_joint_pdf P X Y a b hX hY hindep hneq₁ hneq₂,
    abs_pos.mpr hdet_ne, rfl, rfl⟩

/-- The diagonal support set describing the singular case `a = b`. -/
theorem prob_1_5_singular_support_eq :
    volume {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  erw [show { p : ℝ × ℝ | p.1 = p.2 } = ( Set.range fun x : ℝ => ( x, x ) ) by ext ; aesop,
    MeasureTheory.Measure.prod_apply]
  · simp +decide [Set.preimage]
  ·
    exact
      (by
        rw [show (range (fun x : ℝ => (x, x))) = {x : ℝ × ℝ | x.1 = x.2} by ext ; aesop]
        exact measurableSet_eq_fun measurable_fst measurable_snd)

/-- The anti-diagonal support set describing the singular case `a = -b`. -/
theorem prob_1_5_singular_support_neg :
    volume {p : ℝ × ℝ | p.1 = -p.2} = 0 := by
  erw [show { p : ℝ × ℝ | p.1 = -p.2 } = ( Set.range fun x : ℝ => ( x, -x ) ) by ext ; aesop,
    MeasureTheory.Measure.prod_apply]
  · simp +decide [Set.preimage]
  ·
    exact
      (by
        rw [show (range fun x : ℝ => (x, -x)) = {p : ℝ × ℝ | p.2 = -p.1} by ext ; aesop]
        exact measurableSet_eq_fun measurable_snd (measurable_neg.comp measurable_fst))

/--
Part (c), case `a = b`: the transformed pair lies on the diagonal almost surely, so `(U, V)` is
described by the singular relation `V = U`.
-/
theorem prob_1_5_part_c_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a = b) (X Y : Ω → ℝ) :
    P ((uvPair a b X Y) ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 1 := by
  have hpreimage :
      (uvPair a b X Y) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = Set.univ := by
    ext ω
    simp [uvPair, hab]
  simp [hpreimage]

/--
Part (c), case `a = -b`: the transformed pair lies on the anti-diagonal almost surely, so `(U, V)`
is described by the singular relation `V = -U`.
-/
theorem prob_1_5_part_c_neg
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a = -b) (X Y : Ω → ℝ) :
    P ((uvPair a b X Y) ⁻¹' {p : ℝ × ℝ | p.1 = -p.2}) = 1 := by
  have hpreimage :
      (uvPair a b X Y) ⁻¹' {p : ℝ × ℝ | p.1 = -p.2} = Set.univ := by
    ext ω
    simp [uvPair, hab]
    ring
  simp [hpreimage]

/--
Main theorem combining all three textbook parts:

1. the singularity condition `a = ± b`;
2. the nonsingular joint pdf determined by the covariance matrix of `(U, V)`;
3. the singular descriptions `V = U` and `V = -U` in the two degenerate cases.
-/
theorem prob_1_5
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a b : ℝ)
    (hX : Measure.map X P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hY : Measure.map Y P = gaussianReal (0 : ℝ) (1 : NNReal))
    (hindep : ProbabilityTheory.IndepFun X Y P) :
    (a ^ 2 - b ^ 2 = 0 ↔ (a = b ∨ a = -b)) ∧
    ((a ≠ b ∧ a ≠ -b) →
      ∀ u v,
        Measure.map (uvPair a b X Y) P =
          (volume : Measure (ℝ × ℝ)).withDensity
            (fun p => ENNReal.ofReal (uvJointPdf a b p.1 p.2)) ∧
        0 < |a ^ 2 - b ^ 2| ∧
        uvCovarianceMatrix a b = !![a ^ 2 + b ^ 2, 2 * a * b; 2 * a * b, a ^ 2 + b ^ 2] ∧
        uvJointPdf a b u v =
          (1 / (2 * Real.pi * |a ^ 2 - b ^ 2|)) *
            Real.exp
              (-(((a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) - 4 * a * b * u * v) /
                  (2 * (a ^ 2 - b ^ 2) ^ 2)))) ∧
    (a = b → P ((uvPair a b X Y) ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 1) ∧
    (a = -b → P ((uvPair a b X Y) ⁻¹' {p : ℝ × ℝ | p.1 = -p.2}) = 1) := by
  refine ⟨prob_1_5_part_a a b, ?_, ?_, ?_⟩
  · intro hns u v
    exact prob_1_5_part_b P X Y a b u v hX hY hindep hns.1 hns.2
  · intro hab
    exact prob_1_5_part_c_eq P a b hab X Y
  · intro hab
    exact prob_1_5_part_c_neg P a b hab X Y
