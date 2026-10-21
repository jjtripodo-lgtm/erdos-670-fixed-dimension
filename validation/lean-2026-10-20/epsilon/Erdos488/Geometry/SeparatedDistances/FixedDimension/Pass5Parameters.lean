import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! Exact scalar certificates for the orthogonal-circle fifth-pass manuscript.
These results prove the numerical hypotheses; they do not assert existence
of the geometric configuration supplied by the finite criterion. -/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Offset (m : ℕ) : ℕ :=
  ⌈(m : ℝ) * ((m : ℝ) - 1) / 64⌉₊

noncomputable def pass5Tau (m : ℕ) : ℝ :=
  Real.sqrt (1 - 1 / ((9 / 8 : ℝ) * ((pass5Offset m : ℝ) + 1)))

/-- The chosen harmonic reserve is valid throughout the new parameter range. -/
theorem pass5_harmonic_linear_bound {m : ℕ} (hm : 18177 ≤ m) :
    (harmonic m : ℝ) ≤ (m : ℝ) / 1100 := by
  induction m, hm using Nat.le_induction with
  | base =>
      have hlog : Real.log (18177 : ℝ) ≤ Real.log ((2 : ℝ)^15) := by
        rw [Real.log_le_log_iff (by norm_num) (by positivity)]
        norm_num
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h ⊢
        exact h
      have hH := harmonic_le_one_add_log 18177
      change (harmonic 18177 : ℝ) ≤ 1 + Real.log (18177 : ℝ) at hH
      change (harmonic 18177 : ℝ) ≤ (18177 : ℝ) / 1100
      rw [Real.log_pow] at hlog
      norm_num at hlog
      nlinarith
  | succ m hm ih =>
      have hden : (1100 : ℝ) ≤ (m+1 : ℕ) := by
        exact_mod_cast (show 1100 ≤ m+1 by omega)
      have hi : ((m+1 : ℕ) : ℝ)⁻¹ ≤ (1/1100 : ℝ) := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1100) hden
      rw [harmonic_succ]
      push_cast
      push_cast at hi
      linarith

theorem pass5Offset_lower (m : ℕ) :
    (m : ℝ) * ((m : ℝ) - 1) / 64 ≤ (pass5Offset m : ℝ) :=
  Nat.le_ceil _

theorem pass5Offset_upper (m : ℕ) (hm : 1 ≤ m) :
    (pass5Offset m : ℝ) < (m : ℝ) * ((m : ℝ) - 1) / 64 + 1 := by
  apply Nat.ceil_lt_add_one
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  positivity

theorem pass5Offset_ge_284_mul (m : ℕ) (hm : 18177 ≤ m) :
    284 * (m : ℝ) ≤ (pass5Offset m : ℝ) := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have h := pass5Offset_lower m
  nlinarith

theorem pass5Offset_add_m_upper (m : ℕ) (hm : 18177 ≤ m) :
    (pass5Offset m : ℝ) + m ≤ (m : ℝ)^2 / 63 := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have h := pass5Offset_upper m (by omega)
  nlinarith

theorem pass5Offset_harmonic_reserve (m : ℕ) (hm : 18177 ≤ m) :
    16384 * (harmonic m : ℝ)^2 ≤ (pass5Offset m : ℝ) := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have hH0 : (0 : ℝ) ≤ harmonic m := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic m by unfold harmonic; positivity)
  have hH := pass5_harmonic_linear_bound hm
  have hHsq : (harmonic m : ℝ)^2 ≤ ((m : ℝ)/1100)^2 := by nlinarith
  have hK := pass5Offset_lower m
  nlinarith

/-- The tolerance is bounded by an exact rational lower certificate. -/
theorem pass5Tau_bounds (m : ℕ) (hm : 18177 ≤ m) :
    (9999/10000 : ℝ) < pass5Tau m ∧ pass5Tau m < 1 := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have hK := pass5Offset_ge_284_mul m hm
  have hden : 0 < (9/8 : ℝ) * ((pass5Offset m : ℝ)+1) := by positivity
  have hrecip : 1 / ((9/8 : ℝ) * ((pass5Offset m : ℝ)+1)) <
      (19999/100000000 : ℝ) := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hrecip0 : 0 < 1 / ((9/8 : ℝ) * ((pass5Offset m : ℝ)+1)) :=
    one_div_pos.mpr hden
  unfold pass5Tau
  constructor
  · apply (Real.lt_sqrt (by norm_num)).2
    nlinarith
  · apply (Real.sqrt_lt (by linarith) (by norm_num)).2
    linarith

/-- All five finite-criterion inequalities at the exact concrete parameters.
The conjunction includes parameter admissibility and the actual derived tolerance. -/
theorem pass5_five_conditions (m : ℕ) (hm : 18177 ≤ m) :
    0 < pass5Tau m ∧ pass5Tau m < 1 ∧
    1 < pass5Tau m * (9/8 : ℝ) * (853589/960000 : ℝ) ∧
    max (m : ℝ) (16384 * (harmonic m : ℝ)^2) ≤ (pass5Offset m : ℝ) ∧
    4 * 101 * (m : ℝ) / (9/8 : ℝ)^3 ≤ (pass5Offset m : ℝ) ∧
    84 * (9/8 : ℝ)^2 / (49/100 : ℝ) *
      Real.sqrt ((pass5Offset m : ℝ) + m) ≤ 101 * (m : ℝ) ∧
    4 * (12 : ℝ) < 101 * (49/100 : ℝ) * (77599/80000 : ℝ) := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨ht, ht1⟩ := pass5Tau_bounds m hm
  have hK := pass5Offset_ge_284_mul m hm
  have hH := pass5Offset_harmonic_reserve m hm
  have hupper := pass5Offset_add_m_upper m hm
  have hs0 := Real.sqrt_nonneg ((pass5Offset m : ℝ) + m)
  have hsq := Real.sq_sqrt (show 0 ≤ (pass5Offset m : ℝ) + m by positivity)
  refine ⟨by linarith, ht1, ?_, max_le (by linarith) hH, ?_, ?_, ?_⟩
  · nlinarith
  · norm_num at *
    linarith
  · have hs : Real.sqrt ((pass5Offset m : ℝ) + m) ≤ (m : ℝ)/7 := by
      nlinarith
    norm_num at *
    nlinarith
  · norm_num

/-- The rational definitions of kappa, gamma, and lambda are exact. -/
theorem pass5_digit_constants :
    (1 - 1/(12 : ℝ)) = 11/12 ∧
    (1 - (49/100 : ℝ)^2/8) = 77599/80000 ∧
    (1 - 1/(12 : ℝ)) * (1 - (49/100 : ℝ)^2/8) = 853589/960000 := by
  norm_num

/-- The finite-criterion diameter is strictly below the manuscript's leading
coefficient, without yet invoking the geometric finite criterion. -/
theorem pass5_finite_diameter_bound (m k : ℕ) (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    ((9/8 : ℝ)^3 * ((pass5Offset m : ℝ) + (m.choose 2 : ℝ)) +
      (9/8 : ℝ)^2 / (2 * pass5Tau m)) * (k : ℝ)^2 <
      (24057/32768 : ℝ) * ((m : ℝ) * k)^2 := by
  have hm' : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK := pass5Offset_upper m (by omega)
  have ht := (pass5Tau_bounds m hm).1
  have ht0 : 0 < pass5Tau m := by linarith
  have hrecip : (9/8 : ℝ)^2 / (2 * pass5Tau m) <
      (9/8 : ℝ)^2 / (2 * (9999/10000 : ℝ)) := by
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num)
    linarith
  have hcoeff : (9/8 : ℝ)^3 * ((pass5Offset m : ℝ) + (m.choose 2 : ℝ)) +
      (9/8 : ℝ)^2 / (2 * pass5Tau m) < (24057/32768 : ℝ)*(m : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    nlinarith
  have h := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos (by linarith : (0 : ℝ) < k))
  nlinarith only [h]

end Erdos488.Geometry.SeparatedDistances.FixedDimension
