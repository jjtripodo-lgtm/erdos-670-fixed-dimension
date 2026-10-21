import FiniteKCompletion
import TwoCircleGeometry

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

def anchor (Q : Matrix (Fin 5) (Fin 5) ℝ) (A : Fin 6) : Fin 5 → ℝ :=
  Fin.cases (fun _ => 0) (fun j i => Q i j) A

lemma sourceE_self (A : Fin 6) : sourceE A A = 0 := by simp [sourceE]
lemma sourceE_symm (A B : Fin 6) : sourceE A B = sourceE B A := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceE, sourceD, labels]
lemma sourceD_self (A : Fin 6) : sourceD A A = 0 := by simp [sourceD]
lemma PG_self (A : Fin 6) : PG A A = 0 := by simp [PG]
lemma PF_self (A : Fin 6) : PF A A = 0 := by simp [PF, PG_self, sourceD_self]

lemma anchor_dot (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (hQ : Qᵀ*Q = sourceMacro) (A B : Fin 6) :
    anchor Q A ⬝ᵥ anchor Q B =
      (sourceE 0 A + sourceE 0 B - sourceE A B)/2 := by
  refine Fin.cases ?_ (fun a => ?_) A
  · simp [anchor, dotProduct, sourceE_self]
  refine Fin.cases ?_ (fun b => ?_) B
  · simp [anchor, dotProduct, sourceE_self, sourceE_symm a.succ 0]
  have h := congrFun (congrFun hQ a) b
  simpa [anchor, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, sourceMacro] using h

lemma anchor_distance_square (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (hQ : Qᵀ*Q = sourceMacro) (A B : Fin 6) :
    (∑ i, (anchor Q A i-anchor Q B i)^2) = sourceE A B := by
  rw [sum_sq_sub]
  have hA := anchor_dot Q hQ A A
  have hB := anchor_dot Q hQ B B
  have hAB := anchor_dot Q hQ A B
  simp only [sourceE_self, sub_zero, dotProduct] at hA hB hAB
  simp only [pow_two, dotProduct]
  linarith

lemma anchor_projection (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A J : Fin 6) :
    anchor Q J ⬝ᵥ (fun i => U i A) =
      k/(519/1000) * ((138/125*k)*(PG A 0-PG A J)+(533/500)*(PF A 0-PF A J)) := by
  refine Fin.cases ?_ (fun j => ?_) J
  · simp [anchor, dotProduct]
  have h := congrFun (congrFun hp j) A
  simpa [anchor, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, TG, TF] using h

lemma anchored_projection (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A B : Fin 6) :
    (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A) =
      k/(519/1000) * ((138/125*k)*PG A B+(533/500)*PF A B) := by
  rw [sub_dotProduct, anchor_projection Q U k hp, anchor_projection Q U k hp]
  rw [PG_self, PF_self]
  ring

#print axioms anchor_distance_square
#print axioms anchored_projection
end Erdos670R29
