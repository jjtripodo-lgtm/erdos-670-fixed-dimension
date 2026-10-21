import ScalarGuards
import HarmonicGuard

namespace Erdos670EpsilonFamily
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5

noncomputable def epsilonOffset (ξ : ℝ) (m : ℕ) : ℝ := (⌈ξ*(m : ℝ)^2⌉₊ : ℝ)

theorem epsilon_parameter_bounds (ξ : ℝ) (m : ℕ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) :
    8192 ≤ m ∧ 1024*(m : ℝ) ≤ epsilonOffset ξ m ∧
    epsilonOffset ξ m + m ≤ (9/8)*ξ*(m : ℝ)^2 := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hξm : 1024 ≤ ξ*(m : ℝ) := by
    have h := (div_le_iff₀ hξ).1 hm
    nlinarith only [h]
  have h8192 : (8192 : ℝ) ≤ m := by
    nlinarith [mul_le_mul_of_nonneg_right hξsmall hm0]
  have hKlo : ξ*(m : ℝ)^2 ≤ epsilonOffset ξ m := Nat.le_ceil _
  have hKhi : epsilonOffset ξ m < ξ*(m : ℝ)^2+1 :=
    Nat.ceil_lt_add_one (by positivity)
  refine ⟨by exact_mod_cast h8192, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hξm hm0]
  · nlinarith [mul_le_mul_of_nonneg_right hξm hm0]

theorem uniform_shortening (m K k ξ : ℝ) (hm : 0 ≤ m) (hk : 0 < k)
    (hξ : 0 < ξ) (hK : 1024*m ≤ K) :
    ((128*m*k^2)^2+(128*m*k^2)^2)/((1+ξ)^3*k^2)^2 ≤ K^2/16 := by
  have hs : 1 ≤ 1+ξ := by linarith
  have hs0 : 0 < 1+ξ := by linarith
  have hp : (1 : ℝ) ≤ (1+ξ)^6 := by nlinarith [one_le_pow₀ hs (n := 6)]
  have hK0 : 0 ≤ K := by linarith
  have hKsq : (1024*m)^2 ≤ K^2 := by nlinarith
  have he : ((128*m*k^2)^2+(128*m*k^2)^2)/((1+ξ)^3*k^2)^2 =
      32768*m^2/(1+ξ)^6 := by
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < (1+ξ)^6)).2
  have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg K)
  nlinarith

/-- All universal macro and incidence obligations are discharged from the
literal epsilon parameters. Only ξ,m,k admissibility remains. -/
theorem uniform_macro_exists (ξ : ℝ) (m k : ℕ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k) :
    ∃ p : Fin m → EuclideanSpace ℝ (Fin (m-1)),
    ∃ U : Matrix (Fin (m-1)) (Fin m) ℝ,
    ∃ W : Matrix (Fin m) (Fin m) ℝ,
      (∀ A B, A ≠ B → ‖p A-p B‖^2 =
        (circleColexDistance (epsilonOffset ξ m) A B)^2-
          2*(((128*(m : ℝ)*(k : ℝ)^2)^2+(128*(m : ℝ)*(k : ℝ)^2)^2)/
            ((1+ξ)^3*(k : ℝ)^2)^2)) ∧
      (Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => (128*(m : ℝ)*(k : ℝ)^2)^2)) ∧
      (∀ A B,
        (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
          ((1+ξ)/(Real.sqrt ξ/(k : ℝ)))*
            ((if B.val < A.val then circleColexDistance (epsilonOffset ξ m) A B else 0) +
              ((1+ξ)*(k : ℝ))*(if A.val < B.val then
                circleColexDistance (epsilonOffset ξ m) A B else 0))) := by
  obtain ⟨hm8192,hKlo,hKhi⟩ := epsilon_parameter_bounds ξ m hξ hξsmall hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm' : (8192 : ℝ) ≤ m := by exact_mod_cast hm8192
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : 0 ≤ epsilonOffset ξ m := by linarith
  have hH := harmonic_square_bound hm8192
  apply colex_two_radius_macro_exists_m (by omega) (by linarith)
    (by nlinarith) (by linarith)
    ((1+ξ)^3*(k : ℝ)^2) (128*(m : ℝ)*(k : ℝ)^2) (128*(m : ℝ)*(k : ℝ)^2)
    (1+ξ) (Real.sqrt ξ/(k : ℝ)) (k : ℝ)
  · exact uniform_shortening (m : ℝ) (epsilonOffset ξ m) (k : ℝ) ξ hm0
      (by linarith) hξ hKlo
  · nlinarith
  · exact uniform_digit_budget ξ (m : ℝ) (epsilonOffset ξ m) (k : ℝ)
      hξ hξsmall (by linarith) hKhi

#print axioms epsilon_parameter_bounds
#print axioms uniform_shortening
#print axioms uniform_macro_exists
end Erdos670EpsilonFamily
