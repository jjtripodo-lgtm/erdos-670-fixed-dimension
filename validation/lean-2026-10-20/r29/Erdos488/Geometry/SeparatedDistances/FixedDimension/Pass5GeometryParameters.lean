import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Parameters

/-! The concrete circle scales discharge the macro/completion scalar gates.
This module constructs no points; the geometry source is kept separate. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5CircleTheta (k : ℕ) : ℝ := (49/100 : ℝ) / k
noncomputable def pass5Scale (k : ℕ) : ℝ := (9/8 : ℝ)^3 * (k : ℝ)^2
noncomputable def pass5Radius (m k : ℕ) : ℝ := 101 * (m : ℝ) * (k : ℝ)^2

theorem pass5_scale_pos {k : ℕ} (hk : 2 ≤ k) : 0 < pass5Scale k := by
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold pass5Scale
  positivity

theorem pass5_theta_pos {k : ℕ} (hk : 2 ≤ k) : 0 < pass5CircleTheta k := by
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold pass5CircleTheta
  positivity

theorem pass5_radius_pos {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    0 < pass5Radius m k := by
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold pass5Radius
  positivity

theorem pass5_radius_scale {m k : ℕ} (hk : 2 ≤ k) :
    pass5Radius m k / pass5Scale k = 101 * (m : ℝ) / (9/8 : ℝ)^3 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold pass5Radius pass5Scale
  field_simp
  <;> ring

theorem pass5_flattening_gate {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    (pass5Radius m k / pass5Scale k)^2 ≤ (pass5Offset m : ℝ)^2/16 := by
  have hK := pass5Offset_ge_284_mul m hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hK0 : (0 : ℝ) ≤ pass5Offset m := Nat.cast_nonneg _
  have hratio : 4 * (101 * (m : ℝ)/(9/8 : ℝ)^3) ≤ (pass5Offset m : ℝ) := by
    norm_num at *
    linarith
  rw [pass5_radius_scale hk]
  have hsq := mul_self_le_mul_self
    (by positivity : 0 ≤ 4*(101*(m : ℝ)/(9/8 : ℝ)^3)) hratio
  nlinarith only [hsq]

theorem pass5_completion_gate {m k : ℕ} (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    7056*((9/8 : ℝ)/pass5CircleTheta k)^2*((9/8 : ℝ)*k)^2 *
      ((pass5Offset m : ℝ)+(m : ℝ)) ≤ (pass5Radius m k)^2 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hcond := (pass5_five_conditions m hm).2.2.2.2.2.1
  have hcond0 : 0 ≤ 84*(9/8 : ℝ)^2/(49/100 : ℝ) *
      Real.sqrt ((pass5Offset m : ℝ)+m) := by positivity
  have hsq := mul_self_le_mul_self hcond0 hcond
  have hsqrt := Real.sq_sqrt (show 0 ≤ (pass5Offset m : ℝ)+(m : ℝ) by positivity)
  have hcoeff : (84*(9/8 : ℝ)^2/(49/100 : ℝ))^2 *
      ((pass5Offset m : ℝ)+m) ≤ (101*(m : ℝ))^2 := by
    nlinarith only [hsq, hsqrt]
  have heq : 7056*((9/8 : ℝ)/pass5CircleTheta k)^2*((9/8 : ℝ)*k)^2 =
      (84*(9/8 : ℝ)^2/(49/100 : ℝ))^2 * (k : ℝ)^4 := by
    unfold pass5CircleTheta
    field_simp
    <;> ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ (k : ℝ)^4)
  unfold pass5Radius
  nlinarith only [h]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
