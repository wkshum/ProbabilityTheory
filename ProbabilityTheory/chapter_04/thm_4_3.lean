import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Theorem 4.3: Composition of Measurable Functions

Suppose $f : (\Omega, \mathcal{F}) \to (\Omega', \mathcal{G})$ is $(\mathcal{F}, \mathcal{G})$-measurable,
and $g : (\Omega', \mathcal{G}) \to (\Omega'', \mathcal{H})$ is $(\mathcal{G}, \mathcal{H})$-measurable.
Then the composed function $h = g \circ f$ is $(\mathcal{F}, \mathcal{H})$-measurable.

**Proof**: Suppose $A$ is a set in $\mathcal{H}$. Because $g$ is measurable, $g^{-1}(A)$ is in $\mathcal{G}$.
Because $f$ is measurable, $f^{-1}(g^{-1}(A))$ is in $\mathcal{F}$.
The proof is completed by noting $h^{-1}(A) = f^{-1}(g^{-1}(A))$.
-/

section Theorem_4_3

variable {Ω Ω' Ω'' : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']

/-- ## Theorem 4.3 (Composition of Measurable Functions) -/
theorem measurable_composition {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g)
      : Measurable (g ∘ f) := by
  -- Suppose A is a set in H (i.e., A is a measurable set in Ω'')
  intro A hA
  -- Because g is measurable, the pre-image g⁻¹(A) is measurable in Ω'
  have h_pre_g : MeasurableSet (g ⁻¹' A) := hg hA
  -- Because f is measurable, f⁻¹(g⁻¹(A)) is measurable in Ω
  have h_pre_f : MeasurableSet (f ⁻¹' (g ⁻¹' A)) := hf h_pre_g
  -- h⁻¹(A) is equal to f⁻¹(g⁻¹(A)). In Lean, these are definitionally equal.
  exact h_pre_f

/-- A concise formalization matching the logic of the proof. -/
theorem measurable_composition_short {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) :=
  fun _ hA => hf (hg hA)


end Theorem_4_3
