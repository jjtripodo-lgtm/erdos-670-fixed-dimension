import TwoCircleMacro

namespace Erdos670EpsilonFamily
open Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5

/-- The source's sole numerical operator-budget check. -/
theorem budget_constant : (7056 : ℝ)*(9/8)^5 < 128^2 := by norm_num

/-- The written uniform incidence reserve, with all epsilon-dependent factors. -/
theorem uniform_digit_budget (ξ m K k : ℝ) (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8)
    (hKm0 : 0 ≤ K+m)
    (hKm : K+m ≤ (9/8)*ξ*m^2) :
    7056*((1+ξ)/(Real.sqrt ξ/k))^2*((1+ξ)*k)^2*(K+m) ≤
      (128*m*k^2)^2 := by
  have ha : 0 < Real.sqrt ξ := Real.sqrt_pos.2 hξ
  have ha2 : (Real.sqrt ξ)^2 = ξ := Real.sq_sqrt hξ.le
  have hs0 : 0 ≤ 1+ξ := by linarith
  have hs : 1+ξ ≤ (9/8 : ℝ) := by linarith
  have hp : (1+ξ)^4 ≤ (9/8 : ℝ)^4 := by gcongr
  have hcore : 7056*(1+ξ)^4*(K+m) ≤ 128^2*ξ*m^2 := by
    calc
      _ ≤ 7056*(9/8)^4*((9/8)*ξ*m^2) := by gcongr
      _ ≤ 128^2*ξ*m^2 := by nlinarith [mul_nonneg hξ.le (sq_nonneg m)]
  have hdiv : 7056*(1+ξ)^4/ξ*(K+m) ≤ (128*m)^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hξ).2
    nlinarith only [hcore]
  have hmul := mul_le_mul_of_nonneg_right hdiv (sq_nonneg (k^2))
  have he : 7056*((1+ξ)/(Real.sqrt ξ/k))^2*((1+ξ)*k)^2*(K+m) =
      (7056*(1+ξ)^4/ξ*(K+m))*(k^2)^2 := by
    rw [div_div_eq_mul_div, div_pow, mul_pow, ha2]
    ring
  rw [he]
  nlinarith only [hmul]

/-- The strict fine-step reserve asserted in the written construction. -/
theorem fine_step_polynomial (ξ : ℝ) (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) :
    1 < (1-ξ/8)^2*(1+ξ) := by
  have hsq : 0 ≤ ξ^2 := sq_nonneg ξ
  have hcube : 0 ≤ ξ^3 := pow_nonneg hξ.le 3
  have hξsq : ξ^2 ≤ ξ/8 := by nlinarith
  nlinarith

#print axioms uniform_digit_budget
#print axioms fine_step_polynomial
end Erdos670EpsilonFamily
