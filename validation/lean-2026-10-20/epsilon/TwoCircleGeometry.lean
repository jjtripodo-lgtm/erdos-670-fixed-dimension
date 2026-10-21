import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleGeometry

namespace Erdos670EpsilonFamily
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5

abbrev TwoCircleCoordinate (ι κ : Type*) :=
  CircleCoordinate ι κ ⊕ CircleCoordinate (Fin 0) κ

noncomputable def joinPoints {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℝ α) (y : EuclideanSpace ℝ β) :
    EuclideanSpace ℝ (α ⊕ β) := WithLp.toLp 2 (Sum.elim x y)

theorem joinPoints_dist_sq {α β : Type*} [Fintype α] [Fintype β]
    (x x' : EuclideanSpace ℝ α) (y y' : EuclideanSpace ℝ β) :
    dist (joinPoints x y) (joinPoints x' y') ^ 2 =
      dist x x' ^ 2 + dist y y' ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, joinPoints,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem private_factor {κ : Type*} [Fintype κ] [DecidableEq κ] (R : ℝ) :
    (0 : Matrix (Fin 0) κ ℝ)ᵀ * (0 : Matrix (Fin 0) κ ℝ) +
      (diagonal (fun _ : κ => R))ᵀ * diagonal (fun _ => R) =
      diagonal (fun _ => R ^ 2) := by
  simp [Matrix.diagonal_mul_diagonal, pow_two]

noncomputable def privatePoint {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℝ) (A : κ) (w : ℝ) : EuclideanSpace ℝ (CircleCoordinate (Fin 0) κ) :=
  circlePoint (fun _ _ => 0) 0 (diagonal (fun _ => R)) 0 R A w

noncomputable def twoCirclePoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ) (A : κ) (z w : ℝ) :
    EuclideanSpace ℝ (TwoCircleCoordinate ι κ) :=
  joinPoints (circlePoint q U W S R₀ A z) (privatePoint R₁ A w)

theorem twoCircle_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = diagonal (fun _ => R₀ ^ 2))
    (A : κ) (z z' w w' : ℝ) :
    dist (twoCirclePoint q U W S R₀ R₁ A z w)
      (twoCirclePoint q U W S R₀ R₁ A z' w') ^ 2 =
      (2 * R₀ * Real.sin ((z-z')/2)) ^ 2 +
      (2 * R₁ * Real.sin ((w-w')/2)) ^ 2 := by
  unfold twoCirclePoint privatePoint
  rw [joinPoints_dist_sq, circlePoint_same_square q U W S R₀ hfactor,
    circlePoint_same_square _ _ _ _ _ (private_factor R₁)]

theorem twoCircle_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R₀ R₁ : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = diagonal (fun _ => R₀ ^ 2))
    (A B : κ) (hAB : A ≠ B) (z z' w w' : ℝ) :
    dist (twoCirclePoint q U W S R₀ R₁ A z w)
      (twoCirclePoint q U W S R₀ R₁ B z' w') ^ 2 =
      S^2 * (∑ i, (q A i-q B i)^2) + 2*(R₀^2+R₁^2) +
      2*S*((q A-q B) ⬝ᵥ ((fun i => U i A*Real.sin z)-
        (fun i => U i B*Real.sin z'))) := by
  unfold twoCirclePoint privatePoint
  rw [joinPoints_dist_sq, circlePoint_cross_square q U W S R₀ hfactor A B hAB,
    circlePoint_cross_square _ _ _ _ _ (private_factor R₁) A B hAB]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add]
  ring

theorem coordinate_card (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (TwoCircleCoordinate (Fin (m-1)) (Fin m)) = 5*m-1 := by
  simp only [TwoCircleCoordinate, CircleCoordinate, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Exact cancellation with the sum of the two squared radii. -/
theorem two_radius_macro_cancellation (S R₀ R₁ D Q : ℝ) (hS : S ≠ 0)
    (hQ : Q = D^2-2*((R₀^2+R₁^2)/S^2)) :
    S^2*Q+2*(R₀^2+R₁^2) = (S*D)^2 := by
  rw [hQ]
  field_simp
  ring

#print axioms twoCircle_same_square
#print axioms twoCircle_cross_square
#print axioms coordinate_card
#print axioms two_radius_macro_cancellation
end Erdos670EpsilonFamily
