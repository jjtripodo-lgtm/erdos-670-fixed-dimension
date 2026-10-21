import ActualCoordinates
import LocalRuler
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossScalar

namespace Erdos670R29
open scoped Matrix BigOperators
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def angleZ (k i : ℕ) : ℝ := (519/1000)/(k : ℝ)*((i : ℝ)-((k : ℝ)-1)/2)
noncomputable def angleW (p k A i : ℕ) : ℝ :=
  (879/500)/(k : ℝ)*(pass5Ruler 2 p k A i : ℝ)/(2*(p : ℝ))
noncomputable def digit (k i : ℕ) : ℝ := (k : ℝ)/(519/1000)*Real.sin (angleZ k i)
noncomputable def crossLength (k : ℕ) (A B : Fin 6) (i j : ℕ) : ℝ :=
  pass5Phi ((k : ℝ)^2*sourceD A B) ((138/125)*(k : ℝ)*digit k i+(533/500)*digit k j)

noncomputable def pointFamily {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ) (A : Fin 6) (i : Fin k) :
    EuclideanSpace ℝ (TwoCircleCoordinate (Fin 5) (Fin 6)) :=
  twoCirclePoint (anchor Q) U W ((k : ℝ)^2) ((507/100)*(k : ℝ)^2)
    ((1131/100)*(k : ℝ)^2) A (angleZ k i.val) (angleW p k A.val i.val)

lemma angleZ_difference (k i j : ℕ) (hij : i ≤ j) :
    angleZ k j-angleZ k i = (519/1000)/(k : ℝ)*(j-i : ℕ) := by
  simp only [angleZ, Nat.cast_sub hij]
  ring
lemma angleW_difference (p k A i j : ℕ) (hij : i ≤ j) :
    angleW p k A j-angleW p k A i =
      (879/500)/(k : ℝ)*(pass5RulerGap 2 p k A i (j-i) : ℝ)/(2*(p : ℝ)) := by
  have he : i+(j-i)=j := Nat.add_sub_of_le hij
  simp only [angleW, pass5RulerGap, he, Int.cast_sub]
  ring

theorem pointFamily_local {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ)
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*(k : ℝ)^2)^2))
    (A : Fin 6) (i j : Fin k) (hij : i < j) :
    dist (pointFamily p Q U W A i) (pointFamily p Q U W A j) =
      localEdge p k A.val i.val j.val := by
  have hs := twoCircle_same_square (anchor Q) U W ((k : ℝ)^2)
    ((507/100)*(k : ℝ)^2) ((1131/100)*(k : ℝ)^2) hfactor A
    (angleZ k j.val) (angleZ k i.val) (angleW p k A.val j.val) (angleW p k A.val i.val)
  rw [angleZ_difference k i.val j.val hij.le, angleW_difference p k A.val i.val j.val hij.le] at hs
  have he : ((879/500)/(k : ℝ)*(pass5RulerGap 2 p k A.val i.val (j.val-i.val) : ℝ)/(2*p))/2 =
      ((879/500)/(k : ℝ))*(pass5RulerGap 2 p k A.val i.val (j.val-i.val) : ℝ)/(2*(2*p)) := by ring
  rw [he] at hs
  have hs' : dist (pointFamily p Q U W A j) (pointFamily p Q U W A i)^2 =
      (localH k ((j.val-i.val : ℕ) : ℝ))^2+(localB k p (pass5RulerGap 2 p k A.val i.val (j.val-i.val)))^2 := by
    simpa only [pointFamily, localH, localB, pass5Chord, mul_one] using hs
  unfold localEdge localLength
  rw [← hs', Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg, dist_comm]

theorem pointFamily_cross {k : ℕ} (p : ℕ)
    (Q : Matrix (Fin 5) (Fin 5) ℝ) (U : Matrix (Fin 5) (Fin 6) ℝ)
    (W : Matrix (Fin 6) (Fin 6) ℝ)
    (hQ : Qᵀ*Q = sourceMacro)
    (hp : Qᵀ*U = ((k : ℝ)/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*(k : ℝ)^2)^2))
    (A B : Fin 6) (hAB : A < B) (i j : Fin k) :
    dist (pointFamily p Q U W A i) (pointFamily p Q U W B j) = crossLength k A B i.val j.val := by
  have hs := actual_cross_square Q U W k hQ hp hfactor A B hAB
    (angleZ k i.val) (angleZ k j.val) (angleW p k A.val i.val) (angleW p k B.val j.val)
  have hs' : dist (pointFamily p Q U W A i) (pointFamily p Q U W B j)^2 =
      ((k : ℝ)^2*sourceD A B)^2+2*((k : ℝ)^2*sourceD A B)*
        ((138/125)*(k : ℝ)*digit k i.val+(533/500)*digit k j.val) := by
    simpa only [pointFamily, digit, mul_assoc] using hs
  unfold crossLength pass5Phi
  rw [← hs', Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]

#print axioms pointFamily_local
#print axioms pointFamily_cross
end Erdos670R29
