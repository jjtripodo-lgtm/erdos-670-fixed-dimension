import PointFamily
import CrossGeneric

namespace Erdos670R29
set_option maxHeartbeats 1500000
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma digit_eq_sineDigit (k i : ℕ) :
    digit k i = sineDigit ((519/1000)/(k : ℝ)) (((k : ℝ)-1)/2) i := by
  unfold digit angleZ sineDigit
  simp [div_eq_mul_inv, mul_comm]

lemma digit_bound (k i : ℕ) (hk : 0 < k) (hi : i < k) :
    |digit k i| ≤ ((k : ℝ)-1)/2 := by
  rw [digit_eq_sineDigit]
  exact finite_sineDigit_bound _ k i (by positivity) hi

lemma digit_step (k i : ℕ) (hk : 0 < k) (hi : i+1 < k) :
    (1-(519/1000 : ℝ)^2/8) ≤ digit k (i+1)-digit k i := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hscale : ((519/1000)/(k : ℝ))^2*(k : ℝ)^2 ≤ (519/1000 : ℝ)^2 := by
    field_simp <;> norm_num
  have h := finite_sineDigit_step ((519/1000)/(k : ℝ)) ((519/1000 : ℝ)^2) k i
    (by positivity) hi hscale
  simpa only [digit_eq_sineDigit, Nat.cast_add, Nat.cast_one] using h

lemma concrete_digit_budget (k : ℕ) (hk : 100 ≤ k) (D : ℝ) (hD : 9709/500 ≤ D) :
    2*digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k ≤
      (1-(971/1000 : ℝ)^2)*((k : ℝ)^2*D) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hD (sq_nonneg (k : ℝ))
  unfold digitBudget
  nlinarith [sq_nonneg (k : ℝ)]

lemma concrete_fine : (1 : ℝ) ≤ (971/1000)*(533/500)*(1-(519/1000)^2/8) := by norm_num
lemma concrete_carry (k : ℕ) (hk : 100 ≤ k) :
    (1 : ℝ) ≤ (971/1000)*((138/125)*(k : ℝ)*(1-(519/1000)^2/8)-
      2*(533/500)*(((k : ℝ)-1)/2)) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith
lemma concrete_macro_gap (k : ℕ) (hk : 100 ≤ k) :
    (1 : ℝ) ≤ (569/500)*(k : ℝ)^2-
      2*digitBudget (138/125) (533/500) (((k : ℝ)-1)/2) k/(971/1000) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  unfold digitBudget
  nlinarith [sq_nonneg (k : ℝ)]

#print axioms digit_step
#print axioms concrete_digit_budget
#print axioms concrete_macro_gap
end Erdos670R29
