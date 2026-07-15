import Mathlib

/-!
Definition 4.4: complex numbers and their Borel structure.

This file records the standard identification of `ℂ` with `ℝ × ℝ`.
-/

/-- The real part of a complex number. -/
def complexRealPart (z : ℂ) : ℝ := z.re

/-- The imaginary part of a complex number. -/
def complexImagPart (z : ℂ) : ℝ := z.im

/-- Identify a complex number with a pair of real numbers. -/
def complexToPair (z : ℂ) : ℝ × ℝ := (z.re, z.im)

/-- Build a complex number from a pair of real numbers. -/
def pairToComplex (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- The standard equivalence between `ℂ` and `ℝ × ℝ`. -/
noncomputable def complexEquivRealProd : ℂ ≃ ℝ × ℝ :=
  Complex.equivRealProd

/-- The topological identification of `ℂ` with `ℝ × ℝ`. -/
noncomputable def complexHomeomorphRealProd : Homeomorph ℂ (ℝ × ℝ) :=
  Complex.equivRealProdCLM.toHomeomorph

/-- The Borel-structure identification of `ℂ` with `ℝ × ℝ`. -/
noncomputable def complexMeasurableEquivRealProd : ℂ ≃ᵐ (ℝ × ℝ) :=
  complexHomeomorphRealProd.toMeasurableEquiv

/-- Open rectangles in `ℂ`, viewed through the identification `ℂ ≃ ℝ × ℝ`. -/
def complexOpenRectangle (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

theorem pairToComplex_complexToPair (z : ℂ) : pairToComplex (complexToPair z) = z := by
  apply Complex.ext <;> simp [pairToComplex, complexToPair]

theorem complexToPair_pairToComplex (p : ℝ × ℝ) : complexToPair (pairToComplex p) = p := by
  cases p
  simp [pairToComplex, complexToPair]

theorem measurable_complexToPair : Measurable complexToPair := by
  fun_prop

theorem measurable_pairToComplex : Measurable pairToComplex := by
  have h : Measurable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    fun_prop
  simpa [pairToComplex] using h

theorem isOpen_complexOpenRectangle (a b c d : ℝ) : IsOpen (complexOpenRectangle a b c d) := by
  simpa [complexOpenRectangle] using
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))

theorem measurableSet_complexOpenRectangle (a b c d : ℝ) :
    MeasurableSet (complexOpenRectangle a b c d) :=
  (isOpen_complexOpenRectangle a b c d).measurableSet
