import CrossBounds

namespace Erdos670EpsilonFamily

/-- The written diameter coefficient estimate, with explicit scalar envelopes. -/
theorem diameter_coefficient (ξ m k K M τ : ℝ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8)
    (hlarge : 6 ≤ ξ*m^2) (hK : K ≤ ξ*m^2+1) (hM : M ≤ m^2/2)
    (hτ : 63/64 ≤ τ) :
    (((1+ξ)^3*(K+M)+(1+ξ)^2/(2*τ))*k^2) ≤
      (1/2+4*ξ)*(m*k)^2 := by
  have hs0 : 0 ≤ 1+ξ := by linarith
  have hs : 1+ξ ≤ (9/8 : ℝ) := by linarith
  have hs2 : (1+ξ)^2 ≤ (9/8 : ℝ)^2 := by gcongr
  have hs3 : (1+ξ)^3 ≤ (9/8 : ℝ)^3 := by gcongr
  have hξsq : ξ^2 ≤ ξ/8 := by nlinarith
  have hξcube : ξ^3 ≤ ξ/64 := by
    have h := mul_le_mul_of_nonneg_left hξsq hξ.le
    nlinarith
  have hcubic : (1+ξ)^3 ≤ 1+4*ξ := by nlinarith
  have hτ0 : 0 < 2*τ := by linarith
  have hfrac : (1+ξ)^2/(2*τ) ≤ 1 := by
    apply (div_le_iff₀ hτ0).2
    nlinarith only [hs2,hτ]
  have hfirst : (1+ξ)^3*(K+M) ≤ (1+ξ)^3*((ξ+1/2)*m^2+1) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs0 3)
    nlinarith only [hK,hM]
  have hsecond := mul_le_mul_of_nonneg_right hcubic
    (show 0 ≤ (ξ+1/2)*m^2 by positivity)
  have hcore : (1+ξ)^3*(K+M)+(1+ξ)^2/(2*τ) ≤
      (1/2+4*ξ)*m^2 := by
    have hq := mul_le_mul_of_nonneg_right hξsq (sq_nonneg m)
    nlinarith only [hfirst,hsecond,hfrac,hs3,hlarge,hq]
  have hmul := mul_le_mul_of_nonneg_right hcore (sq_nonneg k)
  nlinarith only [hmul]

theorem epsilon_cross_diameter_bound {m k : ℕ} (ξ : ℝ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k)
    (A B : Fin m) (hAB : A.val < B.val) (i j : ℕ) (hi : i < k) (hj : j < k) :
    epsilonCrossLength ξ k A B i j ≤ (1/2+4*ξ)*((m : ℝ)*(k : ℝ))^2 := by
  obtain ⟨hm8192,_,_⟩ := epsilon_parameter_bounds ξ m hξ hξsmall hm
  have hm' : (8192 : ℝ) ≤ m := by exact_mod_cast hm8192
  have hξm : 1024 ≤ ξ*(m : ℝ) := by
    have h := (div_le_iff₀ hξ).1 hm
    nlinarith only [h]
  have hlarge : 6 ≤ ξ*(m : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hξm (Nat.cast_nonneg m)]
  have hK : epsilonOffset ξ m ≤ ξ*(m : ℝ)^2+1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ ξ*(m : ℝ)^2)).le
  have hM : (m.choose 2 : ℝ) ≤ (m : ℝ)^2/2 := by
    rw [Nat.cast_choose_two]
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  have ht := epsilon_tau_bounds ξ m hξ hξsmall hm
  have ht0 : 0 < epsilonTau ξ m := by linarith [ht.1]
  have ht63 : (63/64 : ℝ) ≤ epsilonTau ξ m := by linarith [ht.1]
  have hb : epsilonDigitBudget ξ k ≤ (1+ξ)^2*(k : ℝ)^2/2 := by
    unfold epsilonDigitBudget Erdos488.Geometry.SeparatedDistances.FixedDimension.pass5DigitBudget epsilonHalfSpan
    have hp : 0 ≤ ξ*(1+ξ)*(k : ℝ) := by positivity
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hb ht0.le
  have hu := epsilonCrossLength_upper ξ hξ hξsmall hm hk A B hAB i j hi hj
  have hc := diameter_coefficient ξ (m : ℝ) (k : ℝ) (epsilonOffset ξ m) (m.choose 2 : ℝ)
    (epsilonTau ξ m) hξ hξsmall hlarge hK hM ht63
  unfold epsilonScale at hu
  have he : ((1+ξ)^3*(epsilonOffset ξ m+(m.choose 2 : ℝ))+
      (1+ξ)^2/(2*epsilonTau ξ m))*(k : ℝ)^2 =
      (1+ξ)^3*(k : ℝ)^2*(epsilonOffset ξ m+(m.choose 2 : ℝ))+
        ((1+ξ)^2*(k : ℝ)^2/2)/epsilonTau ξ m := by ring
  rw [he] at hc
  linarith

/-- Coarse cross band exceeds the entire local band. -/
theorem epsilon_cross_center_lower (ξ : ℝ) (m k : ℕ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) :
    1024*(m : ℝ)*(k : ℝ)^2 ≤ epsilonScale ξ k*epsilonOffset ξ m := by
  obtain ⟨_,hK,_⟩ := epsilon_parameter_bounds ξ m hξ hξsmall hm
  have hK0 : 0 ≤ epsilonOffset ξ m := by unfold epsilonOffset; positivity
  have hs : (1 : ℝ) ≤ (1+ξ)^3 := one_le_pow₀ (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hK (sq_nonneg (k : ℝ))
  have h2 := mul_le_mul_of_nonneg_right hs (mul_nonneg (sq_nonneg (k : ℝ)) hK0)
  unfold epsilonScale
  nlinarith only [h1,h2]

#print axioms epsilon_cross_diameter_bound
#print axioms epsilon_cross_center_lower
#print axioms diameter_coefficient
end Erdos670EpsilonFamily
