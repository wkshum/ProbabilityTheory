import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import ProbabilityTheory.chapter_04.def_4_3_limsup_liminf

open MeasureTheory
open scoped Topology

/-! # Theorem 4.8. measurability of limsup and liminf of measurable `EReal`-valued
functions, plus a packaged criterion for measurability of a pointwise limit.
-/

theorem measurable_tailSupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (fun ω => tailSup (fun i => f i ω) n) := by
  simpa [tailSup] using (Measurable.iSup fun k => hf (n + k))

theorem measurable_tailInfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (fun ω => tailInf (fun i => f i ω) n) := by
  simpa [tailInf] using (Measurable.iInf fun k => hf (n + k))

theorem measurable_seqLimsupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLimsup (fun i => f i ω)) := by
  simpa [seqLimsup] using (Measurable.iInf fun n => measurable_tailSupEReal f hf n)

theorem measurable_seqLiminfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLiminf (fun i => f i ω)) := by
  simpa [seqLiminf] using (Measurable.iSup fun n => measurable_tailInfEReal f hf n)

theorem seqLimsup_eq_filter_limsupEReal (u : ℕ → EReal) :
    seqLimsup u = Filter.limsup u Filter.atTop := by
  simpa [seqLimsup, tailSup, Nat.add_comm] using
    (Filter.limsup_eq_iInf_iSup_of_nat' (u := u)).symm

theorem seqLiminf_eq_filter_liminfEReal (u : ℕ → EReal) :
    seqLiminf u = Filter.liminf u Filter.atTop := by
  simpa [seqLiminf, tailInf, Nat.add_comm] using
    (Filter.liminf_eq_iSup_iInf_of_nat' (u := u)).symm

theorem measurable_of_tendstoEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) {g : Ω → EReal}
    (hg : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    Measurable g := by
  have h_eq : g = fun ω => seqLimsup (fun i => f i ω) := by
    funext ω
    have h_limsup :
        Filter.limsup (fun n => f n ω) Filter.atTop ≤ g ω := by
      rw [Filter.limsup_le_iff]
      intro y hy
      exact (hg ω) (Iio_mem_nhds hy)
    have h_liminf :
        g ω ≤ Filter.liminf (fun n => f n ω) Filter.atTop := by
      rw [Filter.le_liminf_iff]
      intro y hy
      exact (hg ω) (Ioi_mem_nhds hy)
    have h_ge_limsup :
        g ω ≤ Filter.limsup (fun n => f n ω) Filter.atTop := by
      exact le_trans h_liminf (Filter.liminf_le_limsup (u := fun n => f n ω) (f := Filter.atTop))
    calc
      g ω = Filter.limsup (fun n => f n ω) Filter.atTop := le_antisymm h_ge_limsup h_limsup
      _ = seqLimsup (fun n => f n ω) := (seqLimsup_eq_filter_limsupEReal (fun n => f n ω)).symm
  rw [h_eq]
  exact measurable_seqLimsupEReal f hf

/-- ## Theorem 4.8 in bundled form. -/
theorem thm_4_8 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) {g : Ω → EReal}
    (hg : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    Measurable (fun ω => seqLimsup (fun i => f i ω)) ∧
      Measurable (fun ω => seqLiminf (fun i => f i ω)) ∧
      Measurable g := by
  exact ⟨measurable_seqLimsupEReal f hf, measurable_seqLiminfEReal f hf,
    measurable_of_tendstoEReal f hf hg⟩
