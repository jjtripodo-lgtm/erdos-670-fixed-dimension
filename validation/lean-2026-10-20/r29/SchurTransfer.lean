import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

open scoped Matrix
namespace Erdos670R29

/-- The certified five-row budget is equivalent to the six-column residual budget. -/
theorem schur_transfer {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (T : Matrix ι κ ℝ) (hB : B.PosDef)
    (h : (B-T*Tᵀ).PosSemidef) :
    ((1 : Matrix κ κ ℝ)-Tᵀ*B⁻¹*T).PosSemidef := by
  letI := hB.isUnit.invertible
  letI : Invertible (1 : Matrix κ κ ℝ) := invertibleOne
  have hblock : (Matrix.fromBlocks B T Tᴴ (1 : Matrix κ κ ℝ)).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ B T Matrix.PosDef.one).2
    simpa only [inv_one, Matrix.mul_one,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hresult := (Matrix.PosDef.fromBlocks₁₁ T (1 : Matrix κ κ ℝ) hB).1 hblock
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hresult

#print axioms schur_transfer
end Erdos670R29
