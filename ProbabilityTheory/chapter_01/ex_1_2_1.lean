import Mathlib

/-
TASK ID: ex_1_2_1
TYPE: Example_Proof
SOURCE PLAN: 37_chap1_mixed_singular
TASK CONTENT:
\textbf{Example 1.2.1 (Saturated Gaussian Random Variable)} \\
Consider a saturation function $f(x)$ defined by
\[
f(x)\triangleq
\begin{cases}
-1.5 & \text{if } x<-1.5,\\
x & \text{if } -1.5\le x\le 1.5,\\
1.5 & \text{if } x>1.5.
\end{cases}
\]

Let $X$ be a standard Gaussian random variable. The random variable $Y=f(X)$ is confined to the interval $[-1.5,1.5]$ and is a mixture of discrete and continuous random variables. Due to the two probability masses located at the boundary of $[-1.5,1.5]$, the cumulative distribution function $F_Y(y)=\Pr(Y\le y)$ has jump discontinuities at $y=\pm 1.5$. The random variable $Y$ does not have a probability density function because the cdf is not differentiable at $y=\pm 1.5$. Figure 1.1 illustrates the cdf of $Y$. This is an example of distribution of mixed type.

\textbf{Figure 1.1.} A plot of the cumulative distribution function in Example 1.2.1.

A natural question to ask in Example 1.2.1 is the conditional distribution of $X$ given $Y=f(X)$. Suppose we can observe the value of $Y$ and want to infer the conditional distribution of $X$ based on the information contained in $Y$. However, we cannot answer this question directly using elementary probability theory because both the pdf of $Y$ and the joint pdf of $X$ and $Y$ do not exist; the usual formula for conditional pdf $f_{XY}(x,y)/f_Y(y)$ does not apply. Therefore, we must resort to more advanced theory to derive the conditional distribution of $X$ given $Y$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- Saturation map appearing in Example 1.2.1. -/
def saturationMap (x : ℝ) : ℝ :=
  if x < (-3 / 2 : ℝ) then (-3 / 2 : ℝ) else if x ≤ (3 / 2 : ℝ) then x else (3 / 2 : ℝ)

theorem measurable_saturationMap : Measurable saturationMap := by
  unfold saturationMap
  exact
    Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_id
        measurable_const)

theorem saturationMap_mem_interval (x : ℝ) :
    saturationMap x ∈ Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ) := by
  unfold saturationMap
  split_ifs with hlow hmid
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨by linarith [not_lt.mp hlow], hmid⟩
  · exact ⟨by linarith [not_lt.mp hlow, not_le.mp hmid], le_rfl⟩

theorem saturationMap_preimage_left :
    saturationMap ⁻¹' ({(-3 / 2 : ℝ)} : Set ℝ) = Set.Iic (-3 / 2 : ℝ) := by
  ext x
  change saturationMap x = (-3 / 2 : ℝ) ↔ x ≤ (-3 / 2 : ℝ)
  unfold saturationMap
  split_ifs with hlow hmid
  · simp [le_of_lt hlow]
  · constructor
    · intro hx
      linarith
    · intro hx
      have : x = (-3 / 2 : ℝ) := le_antisymm hx (not_lt.mp hlow)
      simp [this]
  · constructor
    · intro hx
      norm_num at hx
    · intro hx
      linarith [not_le.mp hmid]

theorem saturationMap_preimage_right :
    saturationMap ⁻¹' ({(3 / 2 : ℝ)} : Set ℝ) = Set.Ici (3 / 2 : ℝ) := by
  ext x
  change saturationMap x = (3 / 2 : ℝ) ↔ (3 / 2 : ℝ) ≤ x
  unfold saturationMap
  split_ifs with hlow hmid
  · constructor
    · intro hx
      norm_num at hx
    · intro hx
      linarith
  · constructor
    · intro hx
      have : x = (3 / 2 : ℝ) := by simpa using hx
      linarith
    · intro hx
      have : x = (3 / 2 : ℝ) := le_antisymm hmid hx
      simp [this]
  · simp [le_of_lt (not_le.mp hmid)]

/-- The standard Gaussian law used by Example 1.2.1. -/
def standardGaussianLaw : Measure ℝ := gaussianReal 0 1

/-- The law of the saturated Gaussian random variable `Y = saturationMap X`. -/
def saturatedGaussianLaw : Measure ℝ := Measure.map saturationMap standardGaussianLaw

theorem standardGaussianLaw_Iic_pos (a : ℝ) :
    0 < standardGaussianLaw (Set.Iic a) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hac : (volume : Measure ℝ) ≪ standardGaussianLaw := by
    simpa [standardGaussianLaw] using
      (gaussianReal_absolutelyContinuous' (0 : ℝ) (v := (1 : NNReal)) (by norm_num))
  have hvolzero : (volume : Measure ℝ) (Set.Iic a) = 0 := hac hzero
  rw [Real.volume_Iic] at hvolzero
  exact ENNReal.top_ne_zero hvolzero

theorem standardGaussianLaw_Ici_pos (a : ℝ) :
    0 < standardGaussianLaw (Set.Ici a) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hac : (volume : Measure ℝ) ≪ standardGaussianLaw := by
    simpa [standardGaussianLaw] using
      (gaussianReal_absolutelyContinuous' (0 : ℝ) (v := (1 : NNReal)) (by norm_num))
  have hvolzero : (volume : Measure ℝ) (Set.Ici a) = 0 := hac hzero
  rw [Real.volume_Ici] at hvolzero
  exact ENNReal.top_ne_zero hvolzero

theorem saturatedGaussianLaw_left_atom :
    saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ) =
      standardGaussianLaw (Set.Iic (-3 / 2 : ℝ)) := by
  rw [saturatedGaussianLaw, Measure.map_apply measurable_saturationMap (measurableSet_singleton _),
    saturationMap_preimage_left]

theorem saturatedGaussianLaw_right_atom :
    saturatedGaussianLaw ({(3 / 2 : ℝ)} : Set ℝ) =
      standardGaussianLaw (Set.Ici (3 / 2 : ℝ)) := by
  rw [saturatedGaussianLaw, Measure.map_apply measurable_saturationMap (measurableSet_singleton _),
    saturationMap_preimage_right]

theorem saturatedGaussianLaw_left_atom_pos :
    0 < saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ) := by
  rw [saturatedGaussianLaw_left_atom]
  exact standardGaussianLaw_Iic_pos _

theorem saturatedGaussianLaw_right_atom_pos :
    0 < saturatedGaussianLaw ({(3 / 2 : ℝ)} : Set ℝ) := by
  rw [saturatedGaussianLaw_right_atom]
  exact standardGaussianLaw_Ici_pos _

theorem saturatedGaussianLaw_boundary_atoms :
    0 < saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ) ∧
      0 < saturatedGaussianLaw ({(3 / 2 : ℝ)} : Set ℝ) :=
  ⟨saturatedGaussianLaw_left_atom_pos, saturatedGaussianLaw_right_atom_pos⟩

/-- The cumulative distribution function of the saturated Gaussian law. -/
def saturatedGaussianCDF (y : ℝ) : ENNReal :=
  saturatedGaussianLaw (Set.Iic y)

/-- The strict-left cdf value used to state jumps at atoms. -/
def saturatedGaussianStrictLeftCDF (y : ℝ) : ENNReal :=
  saturatedGaussianLaw (Set.Iio y)

/-- The cdf value at an atom splits into the strict-left value plus the atom mass. -/
theorem saturatedGaussianCDF_jump (a : ℝ) :
    saturatedGaussianCDF a =
      saturatedGaussianStrictLeftCDF a + saturatedGaussianLaw ({a} : Set ℝ) := by
  have hdisj : Disjoint (Set.Iio a) ({a} : Set ℝ) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hxsingleton
    have hxa : x = a := by simpa using hxsingleton
    exact lt_irrefl a (by simpa [hxa] using hx)
  simpa [saturatedGaussianCDF, saturatedGaussianStrictLeftCDF, Set.Iio_union_right] using
    (measure_union (μ := saturatedGaussianLaw) hdisj (measurableSet_singleton a))

/-- Source-facing left jump identity for the cdf at `-1.5`. -/
theorem saturatedGaussianCDF_left_jump :
    saturatedGaussianCDF (-3 / 2 : ℝ) =
      saturatedGaussianStrictLeftCDF (-3 / 2 : ℝ) +
        saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ) :=
  saturatedGaussianCDF_jump (-3 / 2 : ℝ)

/-- Source-facing right jump identity for the cdf at `1.5`. -/
theorem saturatedGaussianCDF_right_jump :
    saturatedGaussianCDF (3 / 2 : ℝ) =
      saturatedGaussianStrictLeftCDF (3 / 2 : ℝ) +
        saturatedGaussianLaw ({(3 / 2 : ℝ)} : Set ℝ) :=
  saturatedGaussianCDF_jump (3 / 2 : ℝ)

/-- The two boundary atoms of the saturated Gaussian law. -/
def saturationBoundary : Set ℝ :=
  ({(-3 / 2 : ℝ)} : Set ℝ) ∪ ({(3 / 2 : ℝ)} : Set ℝ)

/-- The continuous interior part of the saturation range. -/
def saturationInterior : Set ℝ :=
  Set.Ioo (-3 / 2 : ℝ) (3 / 2 : ℝ)

/-- The mixed support: two atoms plus the open interior interval. -/
def saturationMixedSupport : Set ℝ :=
  saturationBoundary ∪ saturationInterior

theorem measurableSet_saturationBoundary : MeasurableSet saturationBoundary := by
  simp [saturationBoundary]

theorem measurableSet_saturationInterior : MeasurableSet saturationInterior := by
  simp [saturationInterior]

theorem measurableSet_saturationMixedSupport : MeasurableSet saturationMixedSupport := by
  exact measurableSet_saturationBoundary.union measurableSet_saturationInterior

theorem saturationMap_mem_mixedSupport (x : ℝ) :
    saturationMap x ∈ saturationMixedSupport := by
  have hx := saturationMap_mem_interval x
  by_cases hleft : saturationMap x = (-3 / 2 : ℝ)
  · simp [saturationMixedSupport, saturationBoundary, hleft]
  by_cases hright : saturationMap x = (3 / 2 : ℝ)
  · simp [saturationMixedSupport, saturationBoundary, hright]
  · right
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hleft), lt_of_le_of_ne hx.2 hright⟩

theorem saturationBoundary_disjoint_interior :
    Disjoint saturationBoundary saturationInterior := by
  rw [Set.disjoint_left]
  intro x hxB hxI
  rcases (by simpa [saturationBoundary] using hxB) with hx | hx <;>
    simp [saturationInterior, hx] at hxI

theorem saturatedGaussianLaw_supported_on_mixedSupport :
    ∀ᵐ y ∂saturatedGaussianLaw, y ∈ saturationMixedSupport := by
  rw [saturatedGaussianLaw]
  exact
    (ae_map_iff measurable_saturationMap.aemeasurable
      measurableSet_saturationMixedSupport).mpr
      (Filter.Eventually.of_forall fun x => saturationMap_mem_mixedSupport x)

/-- Textbook mixed-type decomposition: the saturated law is the sum of its
boundary-atom restriction and its interior restriction. -/
theorem saturatedGaussianLaw_mixed_decomposition :
    saturatedGaussianLaw =
      saturatedGaussianLaw.restrict saturationBoundary +
        saturatedGaussianLaw.restrict saturationInterior := by
  have hsupport :
      saturatedGaussianLaw.restrict saturationMixedSupport = saturatedGaussianLaw :=
    Measure.restrict_eq_self_of_ae_mem saturatedGaussianLaw_supported_on_mixedSupport
  have hdecomp :
      saturatedGaussianLaw.restrict saturationMixedSupport =
        saturatedGaussianLaw.restrict saturationBoundary +
          saturatedGaussianLaw.restrict saturationInterior := by
    simpa [saturationMixedSupport] using
      (Measure.restrict_union (μ := saturatedGaussianLaw)
        saturationBoundary_disjoint_interior measurableSet_saturationInterior)
  exact hsupport.symm.trans hdecomp

theorem saturationMap_eq_self_on_interior {x : ℝ} (hx : x ∈ saturationInterior) :
    saturationMap x = x := by
  unfold saturationMap
  rcases hx with ⟨hx_left, hx_right⟩
  split_ifs with hlow hmid
  · linarith
  · rfl
  · linarith

theorem saturationMap_preimage_interior :
    saturationMap ⁻¹' saturationInterior = saturationInterior := by
  ext x
  constructor
  · intro hx
    by_cases hlow : x < (-3 / 2 : ℝ)
    · simp [saturationMap, saturationInterior, hlow] at hx
    · by_cases hmid : x ≤ (3 / 2 : ℝ)
      · simpa [saturationMap, saturationInterior, hlow, hmid] using hx
      · simp [saturationMap, saturationInterior, hlow, hmid] at hx
  · intro hx
    simpa [saturationMap_eq_self_on_interior hx] using hx

theorem saturatedGaussianLaw_restrict_interior_eq_standard :
    saturatedGaussianLaw.restrict saturationInterior =
      standardGaussianLaw.restrict saturationInterior := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  rw [saturatedGaussianLaw,
    Measure.map_apply measurable_saturationMap (hs.inter measurableSet_saturationInterior)]
  congr 1
  ext x
  constructor
  · intro hx
    have hxI : x ∈ saturationInterior := by
      have : x ∈ saturationMap ⁻¹' saturationInterior := hx.2
      simpa [saturationMap_preimage_interior] using this
    exact ⟨by simpa [saturationMap_eq_self_on_interior hxI] using hx.1, hxI⟩
  · intro hx
    exact ⟨by simpa [saturationMap_eq_self_on_interior hx.2] using hx.1,
      by simpa [saturationMap_eq_self_on_interior hx.2] using hx.2⟩

/-- The interior part is continuous in the measure-theoretic sense: it is
absolutely continuous with respect to Lebesgue measure. -/
theorem saturatedGaussianLaw_interior_absolutelyContinuous_volume :
    saturatedGaussianLaw.restrict saturationInterior ≪ (volume : Measure ℝ) := by
  rw [saturatedGaussianLaw_restrict_interior_eq_standard]
  have hac : standardGaussianLaw ≪ (volume : Measure ℝ) := by
    simpa [standardGaussianLaw] using
      (gaussianReal_absolutelyContinuous (0 : ℝ) (v := (1 : NNReal)) (by norm_num))
  exact (hac.restrict saturationInterior).trans Measure.absolutelyContinuous_restrict

/-- The joint law of `(X, saturationMap X)`. -/
def saturatedGaussianJointLaw : Measure (ℝ × ℝ) :=
  Measure.map (fun x : ℝ => (x, saturationMap x)) standardGaussianLaw

/-- The deterministic graph on which the joint law of `(X,Y)` is supported. -/
def saturationGraph : Set (ℝ × ℝ) :=
  {p | p.2 = saturationMap p.1}

theorem measurableSet_saturationGraph : MeasurableSet saturationGraph := by
  have hmeas : Measurable fun p : ℝ × ℝ => p.2 - saturationMap p.1 :=
    measurable_snd.sub (measurable_saturationMap.comp measurable_fst)
  have hpre : saturationGraph = (fun p : ℝ × ℝ => p.2 - saturationMap p.1) ⁻¹' ({0} : Set ℝ) := by
    ext p
    simp [saturationGraph, sub_eq_zero]
  rw [hpre]
  exact hmeas (measurableSet_singleton 0)

/-- Source-facing joint-pdf obstruction: the joint law is concentrated on the
one-dimensional graph of `saturationMap`, which is why the elementary joint-pdf
formula is not the right interface for this example. -/
theorem saturatedGaussianJointLaw_supported_on_graph :
    saturatedGaussianJointLaw saturationGraph = 1 := by
  let f : ℝ → ℝ × ℝ := fun x => (x, saturationMap x)
  have hf : Measurable f := measurable_id.prodMk measurable_saturationMap
  change (Measure.map f standardGaussianLaw) saturationGraph = 1
  rw [Measure.map_apply hf measurableSet_saturationGraph]
  have hpre :
      f ⁻¹' saturationGraph = Set.univ := by
    ext x
    simp [f, saturationGraph]
  rw [hpre]
  simp [standardGaussianLaw]

theorem volume_prod_saturationGraph_zero :
    (volume.prod volume) saturationGraph = 0 := by
  apply Measure.measure_prod_null_of_ae_null measurableSet_saturationGraph
  exact Filter.Eventually.of_forall fun x => by
    have hsection :
        Prod.mk x ⁻¹' saturationGraph = ({saturationMap x} : Set ℝ) := by
      ext y
      simp [saturationGraph]
    change volume (Prod.mk x ⁻¹' saturationGraph) = 0
    rw [hsection]
    simp

theorem saturatedGaussianJointLaw_not_absolutelyContinuous_volume_prod :
    ¬ saturatedGaussianJointLaw ≪ (volume.prod volume) := by
  intro hac
  have hzero : saturatedGaussianJointLaw saturationGraph = 0 :=
    hac volume_prod_saturationGraph_zero
  rw [saturatedGaussianJointLaw_supported_on_graph] at hzero
  norm_num at hzero

theorem saturatedGaussianLaw_not_absolutelyContinuous_volume :
    ¬ saturatedGaussianLaw ≪ (volume : Measure ℝ) := by
  intro hac
  have hzero : saturatedGaussianLaw ({(-3 / 2 : ℝ)} : Set ℝ) = 0 := by
    exact hac (by simp)
  exact (ne_of_gt saturatedGaussianLaw_left_atom_pos) hzero

/-- The theorem-backed data package for the saturated Gaussian example. -/
structure SaturatedGaussianExample where
  saturation : ℝ → ℝ
  law : Measure ℝ
  cdf : ℝ → ENNReal
  strictLeftCDF : ℝ → ENNReal
  boundary : Set ℝ
  interior : Set ℝ
  jointLaw : Measure (ℝ × ℝ)
  jointGraph : Set (ℝ × ℝ)
  bounded_range : ∀ x, saturation x ∈ Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ)
  left_atom : 0 < law ({(-3 / 2 : ℝ)} : Set ℝ)
  right_atom : 0 < law ({(3 / 2 : ℝ)} : Set ℝ)
  left_cdf_jump :
    cdf (-3 / 2 : ℝ) =
      strictLeftCDF (-3 / 2 : ℝ) + law ({(-3 / 2 : ℝ)} : Set ℝ)
  right_cdf_jump :
    cdf (3 / 2 : ℝ) =
      strictLeftCDF (3 / 2 : ℝ) + law ({(3 / 2 : ℝ)} : Set ℝ)
  mixed_decomposition :
    law = law.restrict boundary + law.restrict interior
  interior_absolutelyContinuous : law.restrict interior ≪ (volume : Measure ℝ)
  joint_law_supported_on_graph : jointLaw jointGraph = 1
  joint_no_density : ¬ jointLaw ≪ (volume.prod volume)
  no_density : ¬ law ≪ (volume : Measure ℝ)
  conditional_pdf_formula_obstruction :
    ¬ law ≪ (volume : Measure ℝ) ∧
      ¬ jointLaw ≪ (volume.prod volume) ∧
        jointLaw jointGraph = 1

/-- Exported declaration for Example 1.2.1. -/
def ex_1_2_1 : SaturatedGaussianExample where
  saturation := saturationMap
  law := saturatedGaussianLaw
  cdf := saturatedGaussianCDF
  strictLeftCDF := saturatedGaussianStrictLeftCDF
  boundary := saturationBoundary
  interior := saturationInterior
  jointLaw := saturatedGaussianJointLaw
  jointGraph := saturationGraph
  bounded_range := saturationMap_mem_interval
  left_atom := saturatedGaussianLaw_left_atom_pos
  right_atom := saturatedGaussianLaw_right_atom_pos
  left_cdf_jump := saturatedGaussianCDF_left_jump
  right_cdf_jump := saturatedGaussianCDF_right_jump
  mixed_decomposition := saturatedGaussianLaw_mixed_decomposition
  interior_absolutelyContinuous := saturatedGaussianLaw_interior_absolutelyContinuous_volume
  joint_law_supported_on_graph := saturatedGaussianJointLaw_supported_on_graph
  joint_no_density := saturatedGaussianJointLaw_not_absolutelyContinuous_volume_prod
  no_density := saturatedGaussianLaw_not_absolutelyContinuous_volume
  conditional_pdf_formula_obstruction :=
    ⟨saturatedGaussianLaw_not_absolutelyContinuous_volume,
      saturatedGaussianJointLaw_not_absolutelyContinuous_volume_prod,
      saturatedGaussianJointLaw_supported_on_graph⟩
