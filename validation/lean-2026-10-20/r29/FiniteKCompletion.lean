import SourceMatrices
import GramCompletion

open scoped Matrix BigOperators
namespace Erdos670R29

lemma scale_factor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (h : Uᵀ*U + Wᵀ*W = 1) :
    (R • U)ᵀ*(R • U) + (R • W)ᵀ*(R • W) = Matrix.diagonal (fun _ => R^2) := by
  ext i j
  have hc := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hc
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  have hU : (∑ k, (R*U k i)*(R*U k j)) = R^2*(∑ k, U k i*U k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hW : (∑ k, (R*W k i)*(R*W k j)) = R^2*(∑ k, W k i*W k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hU, hW, ← mul_add, hc]
  by_cases hij : i=j <;> simp [hij]

/-- For every finite k≥100 one shared five-dimensional macro factor and six
completed directions realize the literal source potentials and radius budget. -/
theorem finite_k_completion (k : ℝ) (hk : 100 ≤ k) :
    ∃ Q : Matrix (Fin 5) (Fin 5) ℝ,
    ∃ U : Matrix (Fin 5) (Fin 6) ℝ,
    ∃ W : Matrix (Fin 6) (Fin 6) ℝ,
      Qᵀ*Q = sourceMacro ∧
      Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF) ∧
      Uᵀ*U + Wᵀ*W = Matrix.diagonal (fun _ => ((507/100 : ℝ)*k^2)^2) := by
  have hk0 : 0 < k := by linarith
  have hrec : (1/k : ℝ) ≤ 1/100 := one_div_le_one_div_of_le (by norm_num) hk
  obtain ⟨Q,U,W,hQ,hproj,hfactor⟩ := gram_completion sourceMacro
    (normalizedDirections (1/k)) sourceMacro_posDef
    (sourceCompletion_posSemidef (1/k) (by positivity) hrec)
  let R : ℝ := (507/100)*k^2
  refine ⟨Q,R • U,R • W,hQ,?_,scale_factor U W R hfactor⟩
  have hscale : Qᵀ*(R • U) = R • normalizedDirections (1/k) := by
    calc
      Qᵀ*(R • U) = R • (Qᵀ*U) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [hproj]
  rw [hscale]
  ext i j
  simp only [normalizedDirections, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, R]
  field_simp
  <;> ring

#print axioms finite_k_completion
end Erdos670R29
