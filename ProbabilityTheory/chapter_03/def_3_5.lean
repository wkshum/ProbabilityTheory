import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic

open Set Filter

/-- # Definition 3.5
A function $F: \mathbb{R} \to \mathbb{R}$ is called a **Stieltjes measure function** if:
1. $F$ is non-decreasing.
2. $F$ is continuous from the right, i.e., $\lim_{y \to x^+} F(y) = F(x)$ for all $x \in \mathbb{R}$.
-/
structure StieltjesMeasureFunction where
  /-- The underlying function $F: \mathbb{R} \to \mathbb{R}$. -/
  toFun : ℝ → ℝ
  /-- $F$ is non-decreasing: $x \le y \implies F(x) \le F(y)$. -/
  non_decreasing : Monotone toFun
  /-- $F$ is continuous from the right at every point $x$. -/
  right_continuous : ∀ x : ℝ, ContinuousWithinAt toFun (Ici x) x

/-- Coercion to allow a `StieltjesMeasureFunction` to be used directly as a function. -/
instance : CoeFun StieltjesMeasureFunction (fun _ => ℝ → ℝ) where
  coe F := F.toFun

/--
Conversion from the user-defined `StieltjesMeasureFunction` to Mathlib's
internal `StieltjesFunction` structure.
-/
def StieltjesMeasureFunction.toStieltjesFunction (F : StieltjesMeasureFunction) :
    StieltjesFunction ℝ where
  toFun := F.toFun
  mono' := F.non_decreasing
  right_continuous' := F.right_continuous
