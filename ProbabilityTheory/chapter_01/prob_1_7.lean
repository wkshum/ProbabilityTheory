import Mathlib

open MeasureTheory Set Real

noncomputable def Uniform (a b : ℝ) : ℝ → ℝ := fun ω => ω

noncomputable def jointCDF (X : ℝ → ℝ) (Y : ℝ → ℝ) (u v : ℝ) : ℝ :=
  (volume (Icc (0:ℝ) 2 ∩ {ω | X ω ≤ u} ∩ {ω | Y ω ≤ v})).toReal / 2

theorem prob_1_7 (u v : ℝ) : jointCDF (Uniform (0:ℝ) 2) (fun ω => Int.floor ((Uniform (0:ℝ) 2) ω)) u v =
    if u < 0 ∨ v < 0 then 0
    else if v < 1 then (min u 1)/2
    else (min u 2)/2 := by
      split_ifs <;> simp_all +decide [ jointCDF ];
      · unfold Uniform;
        rw [ show ( Icc 0 2 ∩ { ω : ℝ | ω ≤ u } ∩ { ω : ℝ | ( ⌊ω⌋ : ℝ ) ≤ v } ) = ∅ from Set.eq_empty_of_forall_notMem fun x hx => by rcases ‹u < 0 ∨ v < 0› with ( h | h ) <;> linarith [ hx.1.1.1, hx.1.1.2, hx.1.2.out, hx.2.out, show ( ⌊x⌋ : ℝ ) ≥ 0 by exact_mod_cast Int.floor_nonneg.mpr ( by linarith [ hx.1.1.1, hx.1.1.2, hx.1.2.out ] ) ] ] ; norm_num;
      · -- Since $v < 1$, the set $\{ω | ⌊ω⌋ ≤ v\}$ is equal to $[0, 1)$.
        have h_floor : (Icc (0:ℝ) 2 ∩ {ω | ω ≤ u} ∩ {ω | (⌊ω⌋ : ℝ) ≤ v}) = (Icc (0:ℝ) (min u 1)) \ {1} := by
          -- To prove equality of sets, we show each set is a subset of the other.
          apply Set.ext
          intro ω
          simp [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Iic];
          constructor <;> intro h;
          · exact ⟨ ⟨ by linarith, by linarith, by exact le_of_not_gt fun h' => by linarith [ show ( ⌊ω⌋ : ℝ ) ≥ 1 by exact_mod_cast Int.floor_pos.mpr h'.le ] ⟩, by rintro rfl; norm_num at h; linarith ⟩;
          · exact ⟨ ⟨ ⟨ by linarith, by linarith ⟩, by linarith ⟩, by linarith [ show ( ⌊ω⌋ : ℝ ) ≤ 0 by exact_mod_cast Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; cases lt_or_gt_of_ne h.2 <;> linarith ) ) ] ⟩;
        erw [ h_floor, MeasureTheory.measure_diff_null ] <;> norm_num;
        have hu0 : 0 ≤ u := by
          linarith
        by_cases hu : u ≤ 1
        · rw [min_eq_left hu]
          have hmin : min (ENNReal.ofReal u) 1 = ENNReal.ofReal u := by
            apply min_eq_left
            exact_mod_cast hu
          rw [hmin, ENNReal.toReal_ofReal hu0]
        · have hu' : 1 ≤ u := le_of_not_ge hu
          rw [min_eq_right hu']
          have hmin : min (ENNReal.ofReal u) 1 = (1 : ENNReal) := by
            apply min_eq_right
            rw [ENNReal.ofReal_eq_coe_nnreal hu0]
            exact_mod_cast hu'
          rw [hmin, ENNReal.toReal_one]
      · -- Since $v \geq 1$, we have $\min u 2 = u$ if $u \leq 2$ and $\min u 2 = 2$ if $u > 2$.
        have h_min : (volume (Icc 0 2 ∩ {ω | ω ≤ u} ∩ {ω | ⌊ω⌋ ≤ v})).toReal = (volume (Icc 0 2 ∩ {ω | ω ≤ u})).toReal := by
          congr 1;
          refine' MeasureTheory.measure_congr _;
          rw [ MeasureTheory.ae_eq_set ];
          constructor <;> rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] <;> norm_num;
          · exact Filter.Eventually.of_forall fun x hx₁ hx₂ hx₃ hx₄ => ⟨ hx₁, hx₂, hx₃ ⟩;
          · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton 2 ) ] with x hx using fun _ _ _ => by linarith [ show ( ⌊x⌋ : ℝ ) ≤ 1 by exact_mod_cast Int.le_of_lt_add_one ( Int.floor_lt.mpr ( by norm_num; linarith [ show x < 2 by exact lt_of_le_of_ne ( by linarith ) hx ] ) ) ] ;
        convert h_min using 1;
        rw [ show ( Icc 0 2 ∩ { ω | ω ≤ u } : Set ℝ ) = Set.Icc 0 ( Min.min u 2 ) by ext; aesop, Real.volume_Icc ] ; norm_num;
        rw [ ENNReal.toReal_min ] ; norm_num [ ENNReal.toReal_ofReal ( by linarith : 0 ≤ u ) ];
        · norm_num;
        · norm_cast
