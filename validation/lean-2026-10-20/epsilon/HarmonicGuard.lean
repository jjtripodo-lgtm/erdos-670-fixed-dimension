import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace Erdos670EpsilonFamily

/-- Uniform harmonic reserve from the written epsilon construction.
The base is bounded logarithmically and the squared bound is propagated using
the exact harmonic recurrence. -/
theorem harmonic_square_bound {m : ℕ} (hm : 8192 ≤ m) :
    (harmonic m : ℝ)^2 ≤ (m : ℝ)/16 := by
  have hnonneg (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic n by unfold harmonic; positivity)
  induction m, hm using Nat.le_induction with
  | base =>
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have he : (8192 : ℝ) = 2^13 := by norm_num
    have hH := harmonic_le_one_add_log 8192
    change (harmonic 8192 : ℝ) ≤ 1+Real.log (8192 : ℝ) at hH
    rw [he, Real.log_pow] at hH
    norm_num only [Nat.cast_ofNat] at hH
    change (harmonic 8192 : ℝ)^2 ≤ (8192 : ℝ)/16
    have hH0 := hnonneg 8192
    have hH14 : (harmonic 8192 : ℝ) ≤ 14 := by linarith
    nlinarith
  | succ m hm ih =>
    have hm' : (8192 : ℝ) ≤ m := by exact_mod_cast hm
    have hH0 := hnonneg m
    have hH : (harmonic m : ℝ) ≤ ((m : ℝ)+1)/64 := by
      nlinarith [sq_nonneg ((harmonic m : ℝ)-8)]
    have hden : 0 < (m : ℝ)+1 := by positivity
    have hinv0 : 0 ≤ ((m : ℝ)+1)⁻¹ := inv_nonneg.mpr hden.le
    have hinv : ((m : ℝ)+1)⁻¹ ≤ (1/8192 : ℝ) := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8192) (by linarith : (8192 : ℝ) ≤ (m : ℝ)+1)
    have hcancel : ((m : ℝ)+1)*((m : ℝ)+1)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hden)
    have hmul := mul_le_mul_of_nonneg_right hH hinv0
    rw [harmonic_succ]
    push_cast
    nlinarith [mul_nonneg hinv0 (sub_nonneg.mpr hinv)]

#print axioms harmonic_square_bound
end Erdos670EpsilonFamily
