import AnchorInterface

namespace Erdos670R29
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma sourceD_symm (A B : Fin 6) : sourceD A B = sourceD B A := by
  fin_cases A <;> fin_cases B <;> norm_num [sourceD, labels]

lemma sourceE_offdiag (A B : Fin 6) (hAB : A ≠ B) :
    sourceE A B = (sourceD A B)^2 - 2*((507/100 : ℝ)^2+(1131/100 : ℝ)^2) := by
  simp [sourceE, hAB]

lemma oriented_projections (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (k : ℝ)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (A B : Fin 6) (hAB : A < B) :
    (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A) =
        k/(519/1000)*(138/125*k)*sourceD A B ∧
    (anchor Q B-anchor Q A) ⬝ᵥ (fun i => U i B) =
        k/(519/1000)*(533/500)*sourceD A B := by
  have hBA : ¬ B.val < A.val := by omega
  rw [anchored_projection Q U k hp, anchored_projection Q U k hp]
  simp only [PG, PF, show A.val < B.val from hAB, hBA, if_true, if_false,
    sub_self, mul_zero, add_zero, zero_add, sub_zero, sourceD_symm B A]
  constructor <;> ring

/-- Exact literal-coordinate cross identity for every ordered pair of anchors.
The private ruler angles are arbitrary: their contribution is exactly constant. -/
theorem actual_cross_square (Q : Matrix (Fin 5) (Fin 5) ℝ)
    (U : Matrix (Fin 5) (Fin 6) ℝ) (W : Matrix (Fin 6) (Fin 6) ℝ) (k : ℝ)
    (hQ : Qᵀ*Q = sourceMacro)
    (hp : Qᵀ*U = (k/(519/1000)) • (((138/125 : ℝ)*k) • TG + (533/500 : ℝ) • TF))
    (hfactor : Uᵀ*U+Wᵀ*W = diagonal (fun _ => ((507/100 : ℝ)*k^2)^2))
    (A B : Fin 6) (hAB : A < B) (z z' w w' : ℝ) :
    dist (twoCirclePoint (anchor Q) U W (k^2) ((507/100)*k^2) ((1131/100)*k^2) A z w)
      (twoCirclePoint (anchor Q) U W (k^2) ((507/100)*k^2) ((1131/100)*k^2) B z' w') ^ 2 =
      (k^2*sourceD A B)^2 + 2*(k^2*sourceD A B)*
        ((138/125*k)*(k/(519/1000)*Real.sin z)+(533/500)*(k/(519/1000)*Real.sin z')) := by
  rw [twoCircle_cross_square _ _ _ _ _ _ hfactor A B (ne_of_lt hAB),
    anchor_distance_square Q hQ, sourceE_offdiag A B (ne_of_lt hAB)]
  obtain ⟨ha,hb⟩ := oriented_projections Q U k hp A B hAB
  have hsA : (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A*Real.sin z) =
      ((anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i A))*Real.sin z := by
    simp only [dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsB : (anchor Q A-anchor Q B) ⬝ᵥ (fun i => U i B*Real.sin z') =
      -((anchor Q B-anchor Q A) ⬝ᵥ (fun i => U i B))*Real.sin z' := by
    simp only [dotProduct, Pi.sub_apply]
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [dotProduct_sub, hsA, hsB, ha, hb]
  ring

#print axioms actual_cross_square
end Erdos670R29
