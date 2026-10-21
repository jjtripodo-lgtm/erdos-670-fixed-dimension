import TwoCircleMacro
import TwoCircleGeometry

namespace Erdos670EpsilonFamily
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5

theorem twoCircle_colex_cross_distance {m : ℕ}
    (p : Fin m → EuclideanSpace ℝ (Fin (m-1)))
    (U : Matrix (Fin (m-1)) (Fin m) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (K S R₀ R₁ s θ k : ℝ) (hS : S ≠ 0)
    (hmetric : ∀ A B, A ≠ B → ‖p A-p B‖^2 =
      (circleColexDistance K A B)^2-2*((R₀^2+R₁^2)/S^2))
    (hfactor : Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => R₀^2))
    (hproj : ∀ A B,
      (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
        (s/θ)*((if B.val < A.val then circleColexDistance K A B else 0) +
          (s*k)*(if A.val < B.val then circleColexDistance K A B else 0)))
    (A B : Fin m) (hAB : A.val < B.val) (z z' w w' : ℝ) :
    dist (twoCirclePoint (fun A i => p A i) U W S R₀ R₁ A z w)
      (twoCirclePoint (fun A i => p A i) U W S R₀ R₁ B z' w') =
      Real.sqrt ((S*circleColexDistance K A B)^2 +
        2*(S*circleColexDistance K A B)*(s^2*k*(Real.sin z/θ)+s*(Real.sin z'/θ))) := by
  have hne : A ≠ B := by intro h; subst B; omega
  have hBA : ¬B.val < A.val := by omega
  have hbase := two_radius_macro_cancellation S R₀ R₁ (circleColexDistance K A B)
    (‖p A-p B‖^2) hS (hmetric A B hne)
  have hbase' : S^2*(∑ i, (p A i-p B i)^2)+2*(R₀^2+R₁^2) =
      (S*circleColexDistance K A B)^2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_sub, Pi.sub_apply] using hbase
  have hA := hproj A B
  have hB := hproj B A
  simp only [hAB, hBA, if_true, if_false, zero_add] at hA
  simp only [hAB, hBA, if_true, if_false, mul_zero, add_zero,
    circleColexDistance_symm K B A] at hB
  have hsine (v u : Fin (m-1) → ℝ) (t : ℝ) :
      v ⬝ᵥ (fun i => u i*Real.sin t) = (v ⬝ᵥ u)*Real.sin t := by
    simp only [dotProduct, Finset.sum_mul, mul_assoc]
  have hsq := twoCircle_cross_square (fun A i => p A i) U W S R₀ R₁
    hfactor A B hne z z' w w'
  have hneg : (fun i => (p A i-p B i)) = -(fun i => (p B-p A) i) := by
    ext i
    simp
  rw [dotProduct_sub, hsine, hsine] at hsq
  simp only [Pi.sub_def] at hsq
  have hB' : (fun i => p A i-p B i) ⬝ᵥ (fun i => U i B) =
      -((s/θ)*circleColexDistance K A B) := by
    rw [hneg, neg_dotProduct, hB]
  rw [hbase', hB'] at hsq
  have hA' : (fun i => p A i-p B i) ⬝ᵥ (fun i => U i A) =
      (s/θ)*(s*k*circleColexDistance K A B) := hA
  rw [hA'] at hsq
  have he : (S*circleColexDistance K A B)^2 +
        2*S*((s/θ)*(s*k*circleColexDistance K A B)*Real.sin z-
          -((s/θ)*circleColexDistance K A B)*Real.sin z') =
      (S*circleColexDistance K A B)^2 +
        2*(S*circleColexDistance K A B)*(s^2*k*(Real.sin z/θ)+s*(Real.sin z'/θ)) := by ring
  rw [he] at hsq
  rw [← hsq, Real.sqrt_sq (dist_nonneg)]

#print axioms twoCircle_colex_cross_distance
end Erdos670EpsilonFamily
