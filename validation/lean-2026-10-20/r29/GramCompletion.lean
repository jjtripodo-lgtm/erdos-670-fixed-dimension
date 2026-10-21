import SchurTransfer
import Erdos488.Geometry.SeparatedDistances.FixedDimension.CompletionFactor

open scoped Matrix BigOperators
namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- A whole-matrix certificate constructs one shared macro/direction/residual family. -/
theorem gram_completion {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι ι ℝ) (T : Matrix ι κ ℝ) (hB : B.PosDef)
    (hbudget : (B-T*Tᵀ).PosSemidef) :
    ∃ Q : Matrix ι ι ℝ, ∃ U : Matrix ι κ ℝ, ∃ W : Matrix κ κ ℝ,
      Qᵀ*Q = B ∧ Qᵀ*U = T ∧ Uᵀ*U + Wᵀ*W = 1 := by
  obtain ⟨Q, hQ⟩ := psd_same_size_gram_factor B hB.posSemidef
  let U := Q*(B⁻¹*T)
  have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 hB.isUnit
  have hproj : Qᵀ*U = T := by
    dsimp [U]
    rw [← Matrix.mul_assoc, hQ, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv B hdet, Matrix.one_mul]
  have hBinv : (B⁻¹)ᵀ = B⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.inv.eq
  have hU : Uᵀ*U = Tᵀ*B⁻¹*T := by
    calc
      Uᵀ*U = (B⁻¹*T)ᵀ*(Qᵀ*U) := by
        change (Q*(B⁻¹*T))ᵀ*U = _
        rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Tᵀ*B⁻¹*T := by
        rw [hproj, Matrix.transpose_mul, hBinv]
  have hres : ((1 : Matrix κ κ ℝ)-Uᵀ*U).PosSemidef := by
    rw [hU]
    exact schur_transfer B T hB hbudget
  obtain ⟨W, hW⟩ := psd_same_size_gram_factor _ hres
  refine ⟨Q, U, W, hQ, hproj, ?_⟩
  rw [hW]
  abel

#print axioms gram_completion
end Erdos670R29
