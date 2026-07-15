import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic

/-- 
The addition of complex numbers is equivalent to vector addition:
(a + bi) + (c + di) = (a + c) + (b + d)i.
In Lean, this is a definitional identity for the Complex structure.
-/
theorem complex_addition_equivalence (a b c d : ℝ) :
    Complex.mk a b + Complex.mk c d = Complex.mk (a + c) (b + d) := rfl

/-- 
The absolute value (modulus) of z is the length of the vector (a, b) 
and is defined as |z| = √(a² + b²).
We use the standard norm for complex numbers.
-/
noncomputable def complex_abs (z : ℂ) : ℝ := Norm.norm z

/-- Local notation for absolute value as used in the text. -/
local notation "|" z "|" => complex_abs z

/-- 
The absolute value satisfies the triangle inequality:
|z₁ + z₂| ≤ |z₁| + |z₂|.
This follows from the standard triangle inequality for normed spaces.
-/
theorem complex_triangle_inequality (z1 z2 : ℂ) :
    |z1 + z2| ≤ |z1| + |z2| :=
  norm_add_le z1 z2

/-- 
We perform complex multiplication by expanding:
(a + bi)(c + di) = (ac - bd) + i(bc + ad).
This is a definitional identity for the Mul instance of Complex.
-/
theorem complex_multiplication_equivalence (a b c d : ℝ) :
    Complex.mk a b * Complex.mk c d = Complex.mk (a * c - b * d) (a * d + b * c) := rfl

/-- 
The conjugate of z, denoted by (a + bi)∗ ≜ a - bi, 
is the reflection of z along the real axis.
By defining it via the constructor, we ensure definitional equality for rfl.
-/
def complex_conjugate (z : ℂ) : ℂ :=
  ⟨z.re, -z.im⟩

/-- Notation for the conjugate as specified in the text. -/
postfix:max "∗" => complex_conjugate

/-- Verification: The conjugate reflects z along the real axis (a + bi)* = a - bi. -/
theorem complex_conjugate_spec (a b : ℝ) :
    (Complex.mk a b)∗ = Complex.mk a (-b) := rfl