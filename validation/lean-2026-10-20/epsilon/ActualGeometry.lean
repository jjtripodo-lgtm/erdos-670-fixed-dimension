import UniformMacro
import CrossGeometry
import CrossSpectrum
import LocalLengths

namespace Erdos670EpsilonFamily
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5
open EuclideanEpsilonResearch

noncomputable def epsilonPoint {m : ℕ}
    (q : Fin m → EuclideanSpace ℝ (Fin (m-1)))
    (U : Matrix (Fin (m-1)) (Fin m) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (ξ : ℝ) (p k : ℕ) (A : Fin m) (i : Fin k) :
    EuclideanSpace ℝ (TwoCircleCoordinate (Fin (m-1)) (Fin m)) :=
  twoCirclePoint (fun A j => q A j) U W (epsilonScale ξ k)
    (128*(m : ℝ)*(k : ℝ)^2) (128*(m : ℝ)*(k : ℝ)^2) A
    ((Real.sqrt ξ/(k : ℝ))*((i : ℝ)-((k : ℝ)-1)/2))
    ((epsilonRuler p k A.val i.val : ℝ)/(3*(p : ℝ)*(k : ℝ)))

theorem epsilonPoint_local_distance {m : ℕ}
    (q : Fin m → EuclideanSpace ℝ (Fin (m-1)))
    (U : Matrix (Fin (m-1)) (Fin m) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (ξ : ℝ) (p k : ℕ)
    (hfactor : Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => (128*(m : ℝ)*(k : ℝ)^2)^2))
    (A : Fin m) (i j : Fin k) (hij : i.val < j.val) :
    dist (epsilonPoint q U W ξ p k A i) (epsilonPoint q U W ξ p k A j) =
      epsilonLocalLength p m k A.val i.val (j.val-i.val) (Real.sqrt ξ) := by
  have hnat : i.val+(j.val-i.val)=j.val := by omega
  have hcast : ((j.val-i.val : ℕ) : ℝ) = (j : ℝ)-(i : ℝ) := by
    rw [Nat.cast_sub (by omega)]
  have hz : ((Real.sqrt ξ/(k : ℝ))*((i : ℝ)-((k : ℝ)-1)/2)-
      (Real.sqrt ξ/(k : ℝ))*((j : ℝ)-((k : ℝ)-1)/2))/2 =
      -(Real.sqrt ξ*(j.val-i.val : ℕ)/(2*(k : ℝ))) := by rw [hcast]; ring
  have hw : (((epsilonRuler p k A.val i.val : ℝ)/(3*(p : ℝ)*(k : ℝ)))-
      ((epsilonRuler p k A.val j.val : ℝ)/(3*(p : ℝ)*(k : ℝ))))/2 =
      -((epsilonRulerGap p k A.val i.val (j.val-i.val) : ℝ)/(6*(p : ℝ)*(k : ℝ))) := by
    simp only [epsilonRulerGap, hnat, Int.cast_sub]
    ring
  have hsq := twoCircle_same_square (fun A j => q A j) U W (epsilonScale ξ k)
    (128*(m : ℝ)*(k : ℝ)^2) (128*(m : ℝ)*(k : ℝ)^2) hfactor A
    ((Real.sqrt ξ/(k : ℝ))*((i : ℝ)-((k : ℝ)-1)/2))
    ((Real.sqrt ξ/(k : ℝ))*((j : ℝ)-((k : ℝ)-1)/2))
    ((epsilonRuler p k A.val i.val : ℝ)/(3*(p : ℝ)*(k : ℝ)))
    ((epsilonRuler p k A.val j.val : ℝ)/(3*(p : ℝ)*(k : ℝ)))
  rw [hz,hw] at hsq
  simp only [Real.sin_neg, mul_neg, neg_sq] at hsq
  change dist _ _ = Real.sqrt _
  rw [← hsq, Real.sqrt_sq (dist_nonneg)]
  rfl

theorem epsilonPoint_cross_distance {m : ℕ}
    (q : Fin m → EuclideanSpace ℝ (Fin (m-1)))
    (U : Matrix (Fin (m-1)) (Fin m) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (ξ : ℝ) (p k : ℕ) (hξ : 0 < ξ) (hk : 2 ≤ k)
    (hmetric : ∀ A B, A ≠ B → ‖q A-q B‖^2 =
      (circleColexDistance (epsilonOffset ξ m) A B)^2-
        2*(((128*(m : ℝ)*(k : ℝ)^2)^2+(128*(m : ℝ)*(k : ℝ)^2)^2)/(epsilonScale ξ k)^2))
    (hfactor : Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => (128*(m : ℝ)*(k : ℝ)^2)^2))
    (hproj : ∀ A B,
      (fun i => (q A-q B) i) ⬝ᵥ (fun i => U i A) =
        ((1+ξ)/(Real.sqrt ξ/(k : ℝ)))*
          ((if B.val < A.val then circleColexDistance (epsilonOffset ξ m) A B else 0) +
            ((1+ξ)*(k : ℝ))*(if A.val < B.val then
              circleColexDistance (epsilonOffset ξ m) A B else 0)))
    (A B : Fin m) (hAB : A.val < B.val) (i j : Fin k) :
    dist (epsilonPoint q U W ξ p k A i) (epsilonPoint q U W ξ p k B j) =
      epsilonCrossLength ξ k A B i.val j.val := by
  have h := twoCircle_colex_cross_distance q U W (epsilonOffset ξ m) (epsilonScale ξ k)
    (128*(m : ℝ)*(k : ℝ)^2) (128*(m : ℝ)*(k : ℝ)^2)
    (1+ξ) (Real.sqrt ξ/(k : ℝ)) (k : ℝ)
    (ne_of_gt (epsilon_scale_pos ξ k hξ hk)) hmetric hfactor hproj A B hAB
    ((Real.sqrt ξ/(k : ℝ))*((i : ℝ)-((k : ℝ)-1)/2))
    ((Real.sqrt ξ/(k : ℝ))*((j : ℝ)-((k : ℝ)-1)/2))
    ((epsilonRuler p k A.val i.val : ℝ)/(3*(p : ℝ)*(k : ℝ)))
    ((epsilonRuler p k B.val j.val : ℝ)/(3*(p : ℝ)*(k : ℝ)))
  exact h

#print axioms epsilonPoint_cross_distance
#print axioms epsilonPoint_local_distance
end Erdos670EpsilonFamily
