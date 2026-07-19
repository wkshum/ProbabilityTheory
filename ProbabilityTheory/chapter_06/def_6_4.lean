import Mathlib.Tactic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-
  # Definition 6.4 Positive part and negative part of real-valued function
-/

/-
\begin{defbox}{6.4}
For real-valued measurable function $X$, we let
\[
X^+ \triangleq \max(X,0)
\qquad \text{and} \qquad
X^- \triangleq -\min(X,0)
\]
be the \textit{positive part} and \textit{negative part} of $X$, respectively.

Both the positive and negative parts of $X$ are measurable because the functions $\max(x,0)$ and $-\min(x,0)$ are continuous (Theorem 4.5). Moreover, we have
\[
X=X^+-X^-
\qquad \text{and} \qquad
|X|=X^+ + X^-.
\]

Using these concepts, we can define the Lebesgue integral of a real-valued function by reducing the definition to the nonnegative case.
\end{defbox}
-/


open MeasureTheory

/-- Definition:
  the positive part `X⁺ = max(X, 0)` of a real-valued function. -/
noncomputable def positivePart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => max (X ω) 0

/-- Definition:
  The negative part `X⁻ = -min(X, 0)` of a real-valued function. -/
noncomputable def negativePart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => -min (X ω) 0

/-- ## Definition 6.4. -/
noncomputable def def_6_4 {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : (Ω → ℝ) × (Ω → ℝ) :=
  (positivePart X, negativePart X)

section PositiveNegativeParts

variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}



/-- The positive part of a measurable real-valued function is measurable. -/
theorem measurable_positivePart (hX : Measurable X) : Measurable (positivePart X) := by
  unfold positivePart
  exact (continuous_id.max continuous_const).measurable.comp hX

/-- The negative part of a measurable real-valued function is measurable. -/
theorem measurable_negativePart (hX : Measurable X) : Measurable (negativePart X) := by
  unfold negativePart
  exact ((continuous_id.min continuous_const).neg).measurable.comp hX

/-- The positive part is nonnegative. -/
theorem positivePart_nonneg (ω : Ω) : 0 ≤ positivePart X ω := by
  exact le_max_right (X ω) 0

/-- The negative part is nonnegative. -/
theorem negativePart_nonneg (ω : Ω) : 0 ≤ negativePart X ω := by
  simp [negativePart]

/-- The negative part of X equals max (-X,0) -/
theorem negativePart_eq_max_neg (X : Ω → ℝ) :
    negativePart X = fun ω => max (-X ω) 0 := by
  funext ω
  simpa [negativePart] using (max_neg_neg (X ω) (0 : ℝ)).symm

/-- X equals positive part of X minus negative part of X -/
theorem self_eq_positivePart_sub_negativePart (X : Ω → ℝ) :
    X = fun ω => positivePart X ω - negativePart X ω := by
  funext ω
  rw [negativePart_eq_max_neg]
  simp only [positivePart,
    max_zero_sub_max_neg_zero_eq_self]

/--  Absolute value of X equals positive part plus negative part -/
theorem abs_eq_positivePart_add_negativePart (X : Ω → ℝ) :
    (fun ω => |X ω|) = fun ω => positivePart X ω + negativePart X ω := by
  funext ω
  by_cases hω : 0 ≤ X ω
  · have hneg : ¬ X ω < 0 := not_lt_of_ge hω
    have hmax : max (X ω) 0 = X ω := max_eq_left hω
    have hmin : min (X ω) 0 = 0 := min_eq_right hω
    have habs : |X ω| = X ω := abs_of_nonneg hω
    simp [positivePart, negativePart, hmax, hmin, habs]
  · have hlt : X ω < 0 := lt_of_not_ge hω
    have hmax : max (X ω) 0 = 0 := max_eq_right (le_of_lt hlt)
    have hmin : min (X ω) 0 = X ω := min_eq_left (le_of_lt hlt)
    have habs : |X ω| = -X ω := abs_of_neg hlt
    simp [positivePart, negativePart, hmax, hmin, habs]

end PositiveNegativeParts
