import TauGuards
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossSeparation

namespace Erdos670EpsilonFamily
open Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def epsilonScale (ξ : ℝ) (k : ℕ) : ℝ := (1+ξ)^3*(k : ℝ)^2
noncomputable def epsilonHalfSpan (k : ℕ) : ℝ := ((k : ℝ)-1)/2
noncomputable def epsilonDigitBudget (ξ : ℝ) (k : ℕ) : ℝ :=
  pass5DigitBudget (1+ξ) (epsilonHalfSpan k) k

/-- The complete exact radicand budget at every valid macro baseline. -/
theorem epsilon_digit_domain (ξ : ℝ) (m k : ℕ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k)
    (ν : ℝ) (hν : epsilonScale ξ k*(epsilonOffset ξ m+1) ≤ ν) :
    2*epsilonDigitBudget ξ k ≤ (1-(epsilonTau ξ m)^2)*ν := by
  obtain ⟨hlow,hup,_⟩ := epsilon_tau_bounds ξ m hξ hξsmall hm
  have ht : 0 < epsilonTau ξ m := by linarith
  have hK0 : 0 ≤ epsilonOffset ξ m := by unfold epsilonOffset; positivity
  have hs : 0 < 1+ξ := by linarith
  have hden : (1+ξ)*(epsilonOffset ξ m+1) ≠ 0 := by positivity
  have hrad : 0 ≤ 1-1/((1+ξ)*(epsilonOffset ξ m+1)) :=
    (Real.sqrt_pos.1 ht).le
  have hsq : (epsilonTau ξ m)^2 = 1-1/((1+ξ)*(epsilonOffset ξ m+1)) :=
    Real.sq_sqrt hrad
  have hratio : 1-(epsilonTau ξ m)^2 = 1/((1+ξ)*(epsilonOffset ξ m+1)) := by linarith
  have hr0 : 0 ≤ 1-(epsilonTau ξ m)^2 := by rw [hratio]; positivity
  have he : (1-(epsilonTau ξ m)^2)*(epsilonScale ξ k*(epsilonOffset ξ m+1)) =
      (1+ξ)^2*(k : ℝ)^2 := by
    rw [hratio]
    unfold epsilonScale
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hν hr0
  rw [he] at hmul
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hbudget : 2*epsilonDigitBudget ξ k ≤ (1+ξ)^2*(k : ℝ)^2 := by
    unfold epsilonDigitBudget pass5DigitBudget epsilonHalfSpan
    have hprod : 0 ≤ ξ*(1+ξ)*(k : ℝ) := by positivity
    nlinarith
  exact hbudget.trans hmul

/-- Strict fine, carry, and macro-block guards at all admissible sizes. -/
theorem epsilon_cross_guards (ξ : ℝ) (m k : ℕ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k) :
    0 < epsilonTau ξ m ∧ epsilonTau ξ m ≤ 1 ∧ 0 ≤ 1-ξ/8 ∧
    1 < epsilonTau ξ m*(1+ξ)*(1-ξ/8) ∧
    1 < epsilonTau ξ m*((1+ξ)^2*(k : ℝ)*(1-ξ/8)-2*(1+ξ)*epsilonHalfSpan k) ∧
    1 < epsilonScale ξ k-2*epsilonDigitBudget ξ k/epsilonTau ξ m := by
  obtain ⟨hlow,hup,hfine⟩ := epsilon_tau_bounds ξ m hξ hξsmall hm
  have ht : 0 < epsilonTau ξ m := by linarith
  have hs : 0 < 1+ξ := by linarith
  have hg : 0 ≤ 1-ξ/8 := by linarith
  have hg1 : 1-ξ/8 ≤ 1 := by linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨ht,hup.le,hg,hfine,?_,?_⟩
  · have h := strict_carry_gap (1+ξ) (epsilonTau ξ m) (1-ξ/8) (k : ℝ)
      hs ht hup.le hg hg1 (by positivity) hfine
    unfold epsilonHalfSpan
    nlinarith only [h]
  · have hτs : 1 < epsilonTau ξ m*(1+ξ) := by
      have h := mul_le_mul_of_nonneg_left hg1 (mul_pos ht hs).le
      nlinarith only [h,hfine]
    exact strict_macro_gap (1+ξ) (epsilonTau ξ m) (k : ℝ)
      (by linarith) ht hup.le (by linarith) hτs

#print axioms epsilon_digit_domain
#print axioms epsilon_cross_guards
end Erdos670EpsilonFamily
