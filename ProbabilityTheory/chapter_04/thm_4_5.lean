import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!  # Theorem 4.5  Borel Measurability of Continuous Functions
This theorem proves that any continuous function between finite-dimensional
real vector spaces (ℝ^m and ℝ^n) is Borel measurable.
-/

section Theorem_4_5

open MeasureTheory

/--   ## Theorem 4.5
A continuous function f from ℝ^m to ℝ^n is Borel measurable.

In Mathlib, the default MeasurableSpace instance for `ℝ` and its products
`Fin n → ℝ` is the Borel σ-algebra. The lemma `Continuous.measurable`
provides the proof that any continuous function is measurable with
respect to these Borel σ-algebras.
-/
theorem continuous_to_borel_measurable {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) : Measurable f :=
  -- In Mathlib, a continuous function between topological spaces is
  -- measurable with respect to their Borel σ-algebras.
  hf.measurable

/--
Alternative formulation:
To explicitly show that the preimage of any Borel set is measurable
(matching the style of Definition 4.1 provided in the context).
-/
theorem continuous_preimage_borel {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (f ⁻¹' B) :=
  -- `hf.measurable` is of type `Measurable f`, which by definition
  -- means `∀ B, MeasurableSet B → MeasurableSet (f ⁻¹' B)`.
  hf.measurable hB

/--
Generic version:
Any continuous function between two Borel spaces is measurable.
-/
example {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Continuous f) : Measurable f :=
  hf.measurable


end Theorem_4_5
