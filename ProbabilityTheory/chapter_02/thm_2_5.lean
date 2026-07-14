import ProbabilityTheory.chapter_02.def_2_6
import ProbabilityTheory.chapter_02.thm_2_4

/-

  Theorem 2.5 Upper semi-continuity of measure

-/

/-
\begin{thmbox}{2.5 (Upper Semi-Continuity)}
Suppose $A_1\supseteq A_2\supseteq A_3\supseteq \cdots$ is a sequence of decreasing
sets in $\mathcal{F}$, and $(\Omega,\mathcal{F},\mu)$ is a measure space. Furthermore,
 suppose $\mu(A_1)<\infty$. Then
\[
\lim_{k\to\infty} \mu(A_k)=\mu\left(\bigcap_{i=1}^{\infty} A_i\right).
\]
\end{thmbox}

\textit{Proof} Apply Theorem 2.4 to the sequence of events
$E_i\triangleq A_1\setminus A_i$, for $i=1,2,3,\dots$, and exploit that fact that
 $\mu(E_i)=\mu(A_1)-\mu(A_i)$. \hfill $\square$

The properties in Theorems 2.4 and 2.5 are also known as \textit{continuity from below} and \textit{continuity from above}, respectively.

It is a customary to use the notation $A_k \nearrow A$ to signify that $(A_k)_{k=1}^{\infty}$ is a sequence of increasing sets with union $A$. Similarly, we write $A_k \searrow A$ for a sequence of decreasing sets with intersection $A$.
-/


open MeasureTheory Set

def thm_2_5_gap {Ω : Type*} (A : ℕ → Set Ω) (i : ℕ) : Set Ω :=
  A 0 \ A i

theorem thm_2_5_gap_increasing {Ω : Type*} {A : ℕ → Set Ω}
    (hA : SetSeqDecreasing A) :
    SetSeqIncreasing (thm_2_5_gap A) := by
  change Monotone (thm_2_5_gap A)
  intro i j hij x hx
  exact ⟨hx.1, fun hxAj => hx.2 (hA hij hxAj)⟩

theorem thm_2_5_gap_measurable {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hMeas : ∀ i, MeasurableSet (A i)) :
    ∀ i, MeasurableSet (thm_2_5_gap A i) := by
  intro i
  exact (hMeas 0).diff (hMeas i)

theorem thm_2_5_gap_iUnion_eq {Ω : Type*} (A : ℕ → Set Ω) :
    (⋃ i, thm_2_5_gap A i) = A 0 \ ⋂ i, A i := by
  ext x
  simp [thm_2_5_gap]

theorem thm_2_5_gap_measure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Set Ω} (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) (i : ℕ) :
    μ (thm_2_5_gap A i) = μ (A 0) - μ (A i) := by
  have hAi_subset : A i ⊆ A 0 := hA (Nat.zero_le i)
  have hAi_fin : μ (A i) ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_top_of_lt hfin) (measure_mono hAi_subset)
  exact measure_sdiff hAi_subset (hMeas i).nullMeasurableSet hAi_fin

theorem thm_2_5_source_spine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) :
    μ (⋂ i, A i) = ⨅ i, μ (A i) := by
  have hA0_ne_top : μ (A 0) ≠ ⊤ := ne_top_of_lt hfin
  have hInter_subset : (⋂ i, A i) ⊆ A 0 := iInter_subset A 0
  have hInter_fin : μ (⋂ i, A i) ≤ μ (A 0) := measure_mono hInter_subset
  have hsource :
      μ (⋃ i, thm_2_5_gap A i) = ⨆ i, μ (thm_2_5_gap A i) :=
    thm_2_4 μ (thm_2_5_gap A) (thm_2_5_gap_increasing hA)
      (thm_2_5_gap_measurable hMeas)
  rw [← ENNReal.sub_sub_cancel hA0_ne_top (iInf_le (fun i => μ (A i)) 0),
    ENNReal.sub_iInf, ← ENNReal.sub_sub_cancel hA0_ne_top hInter_fin,
    ← measure_sdiff hInter_subset (.iInter fun i => (hMeas i).nullMeasurableSet)
      (ne_top_of_le_ne_top hA0_ne_top hInter_fin),
    ← thm_2_5_gap_iUnion_eq A, hsource]
  exact congrArg (fun t => μ (A 0) - t)
    (iSup_congr fun i => thm_2_5_gap_measure μ hA hMeas hfin i)

/-- Exported statement for Theorem 2.5. -/
theorem thm_2_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i))
    (hfin : μ (A 0) < ⊤) :
    μ (⋂ i, A i) = ⨅ i, μ (A i) := by
  exact thm_2_5_source_spine μ A hA hMeas hfin

/-- Explicit filter-limit form of Theorem 2.5. -/
theorem thm_2_5_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) :
    Filter.Tendsto (fun i => μ (A i)) Filter.atTop (nhds (μ (⋂ i, A i))) := by
  have hanti : Antitone fun i => μ (A i) := fun i j hij => measure_mono (hA hij)
  have hinf : μ (⋂ i, A i) = ⨅ i, μ (A i) := thm_2_5 μ A hA hMeas hfin
  rw [hinf]
  exact tendsto_atTop_iInf hanti
