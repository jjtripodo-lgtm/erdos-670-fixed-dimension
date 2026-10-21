import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

open scoped Matrix BigOperators
namespace Erdos670R29

lemma gram_affine_identity {ι κ : Type*} [Fintype κ]
    (X Y : Matrix ι κ ℝ) (t : ℝ) :
    ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ =
      (1-t) • (X*Xᵀ) + t • (Y*Yᵀ) - (t*(1-t)) • ((Y-X)*(Y-X)ᵀ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Whole-matrix endpoint certificates control every point of the affine segment. -/
theorem completion_interpolation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℝ) (X Y : Matrix ι κ ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hX : (B-X*Xᵀ).PosSemidef) (hY : (B-Y*Yᵀ).PosSemidef) :
    (B - ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ).PosSemidef := by
  have hG : ((Y-X)*(Y-X)ᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (Y-X)
  have h := ((hX.smul (sub_nonneg.mpr ht1)).add (hY.smul ht0)).add
    (hG.smul (mul_nonneg ht0 (sub_nonneg.mpr ht1)))
  have heq : B - ((1-t) • X + t • Y) * ((1-t) • X + t • Y)ᵀ =
      (1-t) • (B-X*Xᵀ) + t • (B-Y*Yᵀ) + (t*(1-t)) • ((Y-X)*(Y-X)ᵀ) := by
    rw [gram_affine_identity]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact h

#print axioms completion_interpolation
end Erdos670R29
