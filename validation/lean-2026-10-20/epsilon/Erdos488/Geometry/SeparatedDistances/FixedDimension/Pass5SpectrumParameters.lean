import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5GeometryParameters

/-! Concrete digit-domain and separation margins for the fifth-pass spectrum. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5HalfSpan (k : ℕ) : ℝ := ((k : ℝ)-11/12)/2
noncomputable def pass5ConcreteDigitBudget (k : ℕ) : ℝ :=
  (9/8 : ℝ)*((9/8 : ℝ)*k+1)*pass5HalfSpan k

theorem pass5_halfSpan_pos {k : ℕ} (hk : 2 ≤ k) : 0 < pass5HalfSpan k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold pass5HalfSpan
  linarith

theorem pass5_digitBudget_pos {k : ℕ} (hk : 2 ≤ k) : 0 < pass5ConcreteDigitBudget k := by
  have := pass5_halfSpan_pos hk
  unfold pass5ConcreteDigitBudget
  positivity

theorem pass5_digitBudget_strict {k : ℕ} (hk : 2 ≤ k) :
    2*pass5ConcreteDigitBudget k < (9/8 : ℝ)^2*(k : ℝ)^2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold pass5ConcreteDigitBudget pass5HalfSpan
  nlinarith

theorem pass5_tau_sq {m : ℕ} (hm : 18177 ≤ m) :
    (pass5Tau m)^2 = 1-1/((9/8 : ℝ)*((pass5Offset m : ℝ)+1)) := by
  have ht0 : 0 < pass5Tau m := lt_trans (by norm_num) (pass5Tau_bounds m hm).1
  unfold pass5Tau at *
  exact Real.sq_sqrt (Real.sqrt_pos.mp ht0).le

theorem pass5_digit_domain {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k)
    {ν : ℝ} (hν : pass5Scale k*((pass5Offset m : ℝ)+1) ≤ ν) :
    2*pass5ConcreteDigitBudget k ≤ (1-(pass5Tau m)^2)*ν := by
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have ht0 : 0 < pass5Tau m := by linarith
  have hτ : 0 ≤ 1-(pass5Tau m)^2 := by nlinarith
  have hid : (1-(pass5Tau m)^2)*
      (pass5Scale k*((pass5Offset m : ℝ)+1)) = (9/8 : ℝ)^2*(k : ℝ)^2 := by
    rw [pass5_tau_sq hm]
    unfold pass5Scale
    have hK : ((pass5Offset m : ℝ)+1) ≠ 0 := by positivity
    field_simp
    <;> ring
  have hb := pass5_digitBudget_strict hk
  have hp := mul_le_mul_of_nonneg_left hν hτ
  rw [hid] at hp
  exact hb.le.trans hp

theorem pass5_fine_gap {m : ℕ} (hm : 18177 ≤ m) :
    1 ≤ pass5Tau m*(9/8 : ℝ)*(853589/960000 : ℝ) :=
  (pass5_five_conditions m hm).2.2.1.le

theorem pass5_carry_gap {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    1 ≤ pass5Tau m*((9/8 : ℝ)^2*k*(853589/960000 : ℝ)-
      2*(9/8 : ℝ)*pass5HalfSpan k) := by
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have ht0 : 0 ≤ pass5Tau m := by linarith
  have hmul : 0 ≤ pass5Tau m*((k : ℝ)-2) := mul_nonneg ht0 (by linarith)
  unfold pass5HalfSpan
  nlinarith

theorem pass5_macro_gap {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    1 ≤ pass5Scale k-2*pass5ConcreteDigitBudget k/pass5Tau m := by
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have ht0 : 0 < pass5Tau m := by linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul : 0 ≤ ((9/8 : ℝ)*pass5Tau m-1)*(k : ℝ)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hb : 2*pass5ConcreteDigitBudget k ≤ (pass5Scale k-1)*pass5Tau m := by
    unfold pass5Scale pass5ConcreteDigitBudget pass5HalfSpan
    nlinarith
  have hd := (div_le_iff₀ ht0).2 hb
  linarith

theorem pass5_local_below_macro {m k : ℕ} (hm : 18177 ≤ m) :
    (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2 ≤
      pass5Scale k*(pass5Offset m : ℝ) := by
  have hK := pass5Offset_ge_284_mul m hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcoeff : (101 : ℝ)*(49/100)*(m : ℝ) ≤
      (9/8 : ℝ)^3*(pass5Offset m : ℝ) := by nlinarith
  have h := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (k : ℝ))
  unfold pass5Scale
  nlinarith only [h]

/-- Every cross length clears every local length by at least one. -/
theorem pass5_mixed_scalar {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k)
    (ν D L : ℝ) (hν : pass5Scale k*((pass5Offset m : ℝ)+1) ≤ ν)
    (hD : |D-ν| ≤ pass5ConcreteDigitBudget k/pass5Tau m)
    (hL : L ≤ (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2) : 1 ≤ D-L := by
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have ht0 : 0 < pass5Tau m := by linarith
  have he0 : 0 ≤ pass5ConcreteDigitBudget k/pass5Tau m :=
    div_nonneg (pass5_digitBudget_pos hk).le ht0.le
  have hmacro := pass5_macro_gap hm hk
  have hmacro' : 1 ≤ pass5Scale k - 2*(pass5ConcreteDigitBudget k/pass5Tau m) := by
    convert hmacro using 1 <;> ring
  have hlocal := hL.trans (pass5_local_below_macro hm)
  have hlower := (abs_le.mp hD).1
  rw [mul_add, mul_one] at hν
  linarith only [hν, hmacro', hlocal, hlower, he0]

noncomputable def pass5FiniteDiameter (m k : ℕ) : ℝ :=
  ((9/8 : ℝ)^3*((pass5Offset m : ℝ)+(m.choose 2 : ℝ))+
    (9/8 : ℝ)^2/(2*pass5Tau m))*(k : ℝ)^2

theorem pass5_cross_diameter_scalar {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k)
    (ν D : ℝ)
    (hν : ν ≤ pass5Scale k*((pass5Offset m : ℝ)+(m.choose 2 : ℝ)))
    (hD : |D-ν| ≤ pass5ConcreteDigitBudget k/pass5Tau m) :
    D < (24057/32768 : ℝ)*((m : ℝ)*k)^2 := by
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have ht0 : 0 < pass5Tau m := by linarith
  have hsmall := pass5_digitBudget_strict hk
  have herr : pass5ConcreteDigitBudget k/pass5Tau m ≤
      (9/8 : ℝ)^2/(2*pass5Tau m)*(k : ℝ)^2 := by
    apply (div_le_iff₀ ht0).2
    have he : ((9/8 : ℝ)^2/(2*pass5Tau m)*(k : ℝ)^2)*pass5Tau m =
        (9/8 : ℝ)^2*(k : ℝ)^2/2 := by field_simp
    rw [he]
    linarith
  have hupper := (abs_le.mp hD).2
  have hbound : D ≤ pass5FiniteDiameter m k := by
    unfold pass5FiniteDiameter pass5Scale at *
    nlinarith
  exact hbound.trans_lt (pass5_finite_diameter_bound m k hm hk)

theorem pass5_local_diameter_scalar {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k)
    (L : ℝ) (hL : L ≤ (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2) :
    L < (24057/32768 : ℝ)*((m : ℝ)*k)^2 := by
  have hlower := hL.trans (pass5_local_below_macro hm)
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have ht0 : 0 < pass5Tau m := by linarith
  have hterm : 0 ≤ pass5Scale k*(m.choose 2 : ℝ) +
      (9/8 : ℝ)^2/(2*pass5Tau m)*(k : ℝ)^2 := by
    unfold pass5Scale
    positivity
  have hbound : L ≤ pass5FiniteDiameter m k := by
    unfold pass5FiniteDiameter pass5Scale at *
    nlinarith
  exact hbound.trans_lt (pass5_finite_diameter_bound m k hm hk)

end Erdos488.Geometry.SeparatedDistances.FixedDimension
