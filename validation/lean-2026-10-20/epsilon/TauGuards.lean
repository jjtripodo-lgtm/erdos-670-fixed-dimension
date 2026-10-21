import UniformMacro
import Erdos488.Geometry.SeparatedDistances.FixedDimension.SineDigits

namespace Erdos670EpsilonFamily

noncomputable def epsilonTau (ξ : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (1-1/((1+ξ)*(epsilonOffset ξ m+1)))

theorem epsilon_tau_bounds (ξ : ℝ) (m : ℕ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) :
    1-ξ/8 < epsilonTau ξ m ∧ epsilonTau ξ m < 1 ∧
      1 < epsilonTau ξ m*(1+ξ)*(1-ξ/8) := by
  obtain ⟨hm8192,hKlo,_⟩ := epsilon_parameter_bounds ξ m hξ hξsmall hm
  have hm' : (8192 : ℝ) ≤ m := by exact_mod_cast hm8192
  have hξm : 1024 ≤ ξ*(m : ℝ) := by
    have h := (div_le_iff₀ hξ).1 hm
    nlinarith only [h]
  have hK0 : 0 ≤ epsilonOffset ξ m := by linarith
  have hden : 0 < (1+ξ)*(epsilonOffset ξ m+1) := by positivity
  have hrec0 : 0 < 1/((1+ξ)*(epsilonOffset ξ m+1)) := by positivity
  have hrec : 1/((1+ξ)*(epsilonOffset ξ m+1)) < ξ/8 := by
    apply (div_lt_iff₀ hden).2
    have hxK := mul_le_mul_of_nonneg_left hKlo hξ.le
    have hproduct : 0 ≤ ξ^2*(epsilonOffset ξ m+1) := by positivity
    nlinarith
  have hg0 : 0 < 1-ξ/8 := by linarith
  have hlow : 1-ξ/8 < epsilonTau ξ m := by
    apply (Real.lt_sqrt hg0.le).2
    nlinarith
  have hup : epsilonTau ξ m < 1 := by
    apply (Real.sqrt_lt (by linarith : 0 ≤ 1-1/((1+ξ)*(epsilonOffset ξ m+1))) (by norm_num)).2
    linarith
  refine ⟨hlow,hup,?_⟩
  have hp := fine_step_polynomial ξ hξ hξsmall
  have hh := mul_lt_mul_of_pos_right hlow (show 0 < (1+ξ)*(1-ξ/8) by positivity)
  nlinarith only [hp,hh]

/-- A strict inter-macro block gap, rather than a non-strict unit bound. -/
theorem strict_macro_gap (s τ k : ℝ) (hs : 1 < s) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hk : 1 ≤ k) (hτs : 1 < τ*s) :
    1 < s^3*k^2-2*(s*(s*k+1)*((k-1)/2))/τ := by
  have hs0 : 0 < s := by linarith
  have hk0 : 0 < k := by linarith
  have hmain := mul_pos (show 0 < τ*s-1 by linarith) (show 0 < s^2*k^2 by positivity)
  have hside : 0 ≤ (s^2-s)*k := mul_nonneg (by nlinarith) (by linarith)
  have hc : 2*(s*(s*k+1)*((k-1)/2))/τ < s^3*k^2-1 := by
    apply (div_lt_iff₀ hτ).2
    nlinarith
  linarith

theorem strict_carry_gap (s τ lam k : ℝ) (hs : 0 < s) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hk : 0 ≤ k)
    (hfine : 1 < τ*s*lam) :
    1 < τ*(s^2*k*lam-s*(k-1)) := by
  have hτs : 1 < τ*s := by
    have h := mul_le_mul_of_nonneg_left hlam1 (mul_pos hτ hs).le
    nlinarith only [h,hfine]
  have hsl : 1 < s*lam := by
    have h := mul_le_mul_of_nonneg_right hτ1 (mul_nonneg hs.le hlam)
    nlinarith only [h,hfine]
  have hcore := mul_nonneg (show 0 ≤ s*lam-1 by linarith) hk
  have hmul := mul_nonneg hτ.le (mul_nonneg hs.le hcore)
  nlinarith only [hmul,hτs]

/-- The exact uniform sine marks satisfy the entire centered envelope and
adjacent lower slope used by the cross-edge argument. -/
theorem uniform_sine_digits (ξ : ℝ) (k : ℕ) (hξ : 0 < ξ) (hk : 2 ≤ k) :
    (∀ i, i < k →
      |Erdos488.Geometry.SeparatedDistances.FixedDimension.sineDigit
        (Real.sqrt ξ/(k : ℝ)) (((k : ℝ)-1)/2) i| ≤ ((k : ℝ)-1)/2) ∧
    (∀ i, i+1 < k → 1-ξ/8 ≤
      Erdos488.Geometry.SeparatedDistances.FixedDimension.sineDigit
        (Real.sqrt ξ/(k : ℝ)) (((k : ℝ)-1)/2) (i+1)-
      Erdos488.Geometry.SeparatedDistances.FixedDimension.sineDigit
        (Real.sqrt ξ/(k : ℝ)) (((k : ℝ)-1)/2) i) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hθ : 0 < Real.sqrt ξ/(k : ℝ) := div_pos (Real.sqrt_pos.2 hξ) hk0
  have hscale : (Real.sqrt ξ/(k : ℝ))^2*(k : ℝ)^2 = ξ := by
    rw [div_pow, Real.sq_sqrt hξ.le]
    field_simp
  constructor
  · intro i hi
    exact Erdos488.Geometry.SeparatedDistances.FixedDimension.finite_sineDigit_bound _ k i hθ hi
  · intro i hi
    exact Erdos488.Geometry.SeparatedDistances.FixedDimension.finite_sineDigit_step _ ξ k i hθ hi hscale.le

#print axioms strict_carry_gap
#print axioms uniform_sine_digits
#print axioms epsilon_tau_bounds
#print axioms strict_macro_gap
end Erdos670EpsilonFamily
