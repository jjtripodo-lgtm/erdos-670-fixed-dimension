import MatrixCertificates
import MatrixInterpolation

set_option maxHeartbeats 3000000
open scoped Matrix BigOperators
noncomputable section
namespace Erdos670R29

def labels : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,3,5,7,14,15; 3,0,2,4,13,12; 5,2,0,1,11,10;
     7,4,1,0,9,8; 14,13,11,9,0,6; 15,12,10,8,6,0]
def sourceD (A B : Fin 6) : ℝ :=
  if A = B then 0 else 457/25 + (569/500)*labels A B
def sourceE (A B : Fin 6) : ℝ :=
  if A = B then 0 else (sourceD A B)^2 - 2*((507/100)^2+(1131/100)^2)
def sourceMacro : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (sourceE 0 i.succ + sourceE 0 j.succ - sourceE i.succ j.succ)/2
def PG (A B : Fin 6) : ℝ := if A.val < B.val then sourceD A B else 0
def PF (A B : Fin 6) : ℝ := sourceD A B - PG A B
def TG : Matrix (Fin 5) (Fin 6) ℝ := fun j A => PG A 0 - PG A j.succ
def TF : Matrix (Fin 5) (Fin 6) ℝ := fun j A => PF A 0 - PF A j.succ
def normalizedDirections (x : ℝ) : Matrix (Fin 5) (Fin 6) ℝ :=
  ((519/1000 : ℝ)*(507/100))⁻¹ • ((138/125 : ℝ) • TG + ((533/500)*x) • TF)
def sourceCompletion (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  sourceMacro - normalizedDirections x * (normalizedDirections x)ᵀ

theorem sourceMacro_eq : sourceMacro = macroGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.succ, sourceMacro, sourceE, sourceD, labels, macroGram]

theorem TG_entries : TG = !![(-10847/500 : ℝ), 0, 0, 0, 0, 0;
    (-2397/100 : ℝ), (-5139/250 : ℝ), 0, 0, 0, 0;
    (-13123/500 : ℝ), (-2854/125 : ℝ), (-9709/500 : ℝ), 0, 0, 0;
    (-8553/250 : ℝ), (-16537/500 : ℝ), (-15399/500 : ℝ), (-14261/500 : ℝ), 0, 0;
    (-707/20 : ℝ), (-3992/125 : ℝ), (-1483/50 : ℝ), (-3423/125 : ℝ), (-6277/250 : ℝ), 0] := by
  ext j A
  fin_cases j <;> fin_cases A <;>
    norm_num [Fin.succ, TG, PG, PF, sourceD, labels]

theorem TF_entries : TF = !![0, (10847/500 : ℝ), (1707/500 : ℝ), (1707/500 : ℝ), (569/500 : ℝ), (1707/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (1707/250 : ℝ), (1707/500 : ℝ), (569/100 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (569/100 : ℝ), (3983/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (8553/250 : ℝ), (5121/500 : ℝ);
    0, (10847/500 : ℝ), (2397/100 : ℝ), (13123/500 : ℝ), (8553/250 : ℝ), (707/20 : ℝ)] := by
  ext j A
  fin_cases j <;> fin_cases A <;>
    norm_num [Fin.succ, TF, PG, PF, sourceD, labels]

theorem sourceCompletion_zero : sourceCompletion 0 = completion_infinity := by
  ext i j
  change sourceMacro i j - (∑ k : Fin 6,
    normalizedDirections 0 i k * normalizedDirections 0 j k) = completion_infinity i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceCompletion, sourceMacro_eq, macroGram,
      normalizedDirections, TG_entries, TF_entries, completion_infinity,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.sum_univ_succ]

theorem sourceCompletion_endpoint : sourceCompletion (1/100) = completion_k0 := by
  ext i j
  change sourceMacro i j - (∑ k : Fin 6,
    normalizedDirections (1/100) i k * normalizedDirections (1/100) j k) = completion_k0 i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceCompletion, sourceMacro_eq, macroGram,
      normalizedDirections, TG_entries, TF_entries, completion_k0,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.sum_univ_succ]

theorem sourceMacro_posDef : sourceMacro.PosDef := by
  rw [sourceMacro_eq]
  exact macroGram_posDef

/-- The full actual source matrix budget holds throughout the finite-k interval. -/
theorem sourceCompletion_posSemidef (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/100) :
    (sourceCompletion x).PosSemidef := by
  have h0 : (sourceCompletion 0).PosSemidef := by
    rw [sourceCompletion_zero]
    exact completion_infinity_posDef.posSemidef
  have h1 : (sourceCompletion (1/100)).PosSemidef := by
    rw [sourceCompletion_endpoint]
    exact completion_k0_posDef.posSemidef
  have heq : (1-100*x) • normalizedDirections 0 +
      (100*x) • normalizedDirections (1/100) = normalizedDirections x := by
    ext i j
    simp only [normalizedDirections, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h := completion_interpolation sourceMacro (normalizedDirections 0)
    (normalizedDirections (1/100)) (100*x) (by positivity) (by linarith) h0 h1
  rw [heq] at h
  exact h

#print axioms sourceMacro_posDef
#print axioms sourceCompletion_posSemidef
end Erdos670R29
