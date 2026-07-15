import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic


/-

 # Definition 4.1  Measurable function

-/

open MeasureTheory Set

/--
## Definition 4.1

Let (Ω, 𝓕) be a measurable space. A function X : Ω → ℝ is
called a (real-valued) measurable function if for any Borel set B in ℬ(ℝ),
the preimage X⁻¹(B) = {ω ∈ Ω : X(ω) ∈ B} is in 𝓕.
-/
def IsRealMeasurable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → MeasurableSet (X ⁻¹' B)

/-
Note: In Lean's Mathlib, this property is definitionaly
equal to `Measurable X`
when ℝ is equipped with its standard Borel σ-algebra.
-/
example {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) :
    IsRealMeasurable X ↔ Measurable X :=
  Iff.rfl
