import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleGeometry
import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceOperatorBridge

/-! The actual colex skeleton and the two whole-family incidence solves,
connected to the new orthogonal-circle completion. All imported source lemmas
retain their original statements; this file supplies generic new circle scales. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
namespace Pass5
open scoped BigOperators Matrix
open Matrix

/-- The single tilted direction used by the new circle construction. -/
noncomputable def circleDirection {n : ℕ} (s θ k : ℝ)
    (F G : Fin n → EuclideanSpace ℝ (Fin n)) (A : Fin (n+1)) :
    EuclideanSpace ℝ (Fin n) :=
  (s/θ) • (sourceFineShift F A + (s*k) • sourceCoarseShift G A)

/-- The 84-constant estimate controls all directions simultaneously. -/
theorem circleDirection_whole_bound {n : ℕ} {K s θ k : ℝ}
    (hK : 0 ≤ K) (hc : 1 ≤ s*k)
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • F a‖^2 ≤ 576*(K+(n : ℕ))*∑ a, t a^2)
    (hG : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • G a‖^2 ≤ 3600*(K+(n : ℕ))*∑ a, t a^2)
    (t : Fin (n+1) → ℝ) :
    ‖∑ A, t A • circleDirection s θ k F G A‖^2 ≤
      (7056*(s/θ)^2*(s*k)^2*(K+(n : ℕ)))*∑ A, t A^2 := by
  have h := source_shifted_sine_whole_bound hK hc F G hF hG t
  have he : (∑ A, t A • circleDirection s θ k F G A) =
      (s/θ) • (∑ A, t A • (sourceFineShift F A + (s*k) • sourceCoarseShift G A)) := by
    simp only [circleDirection, Finset.smul_sum, smul_smul]
    congr 1
    ext A
    rw [mul_comm]
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (s/θ))
  calc
    _ ≤ (s/θ)^2 * (7056*(s*k)^2*(K+(n : ℕ))*∑ A, t A^2) := hm
    _ = _ := by ring

/-- Literal direction matrix, with one column per macro vertex. -/
noncomputable def circleDirectionMatrix {n : ℕ} (s θ k : ℝ)
    (F G : Fin n → EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin (n+1)) ℝ :=
  fun i A => circleDirection s θ k F G A i

/-- The norm estimate is exactly the quadratic budget needed by completion. -/
theorem circleDirectionMatrix_budget {n : ℕ} {K s θ k R : ℝ}
    (hK : 0 ≤ K) (hc : 1 ≤ s*k)
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • F a‖^2 ≤ 576*(K+(n : ℕ))*∑ a, t a^2)
    (hG : ∀ t : Fin n → ℝ,
      ‖∑ a, t a • G a‖^2 ≤ 3600*(K+(n : ℕ))*∑ a, t a^2)
    (hR : 7056*(s/θ)^2*(s*k)^2*(K+(n : ℕ)) ≤ R^2)
    (t : Fin (n+1) → ℝ) :
    (∑ i, (circleDirectionMatrix s θ k F G *ᵥ t) i ^ 2) ≤ R^2*∑ A, t A^2 := by
  have h := circleDirection_whole_bound (θ := θ) hK hc F G hF hG t
  rw [euclidean_sum_norm_sq_eq] at h
  have hm := mul_le_mul_of_nonneg_right hR (Finset.sum_nonneg (s := Finset.univ) (fun A _ => sq_nonneg (t A)))
  simpa only [circleDirectionMatrix, Matrix.mulVec, dotProduct, mul_comm] using h.trans hm

/-- The exact coarse/fine anchor projections have no constant or quadratic slot. -/
theorem circleDirection_projection {n : ℕ} (K s θ k : ℝ)
    (p : Fin (n+1) → EuclideanSpace ℝ (Fin n))
    (F G : Fin n → EuclideanSpace ℝ (Fin n))
    (hF : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) = fineIncidence n K i a)
    (hG : ∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) = coarseIncidence n K i a)
    (A B : Fin (n+1)) :
    inner ℝ (p A-p B) (circleDirection s θ k F G A) =
      (s/θ)*((if B.val < A.val then colexDistance K A B else 0) +
        (s*k)*(if A.val < B.val then colexDistance K A B else 0)) := by
  rw [circleDirection, real_inner_smul_right, inner_add_right, real_inner_smul_right,
    sourceFineShift_anchor_projection K p F hF,
    sourceCoarseShift_anchor_projection K p G hG]

/-- Actual colex macro points, actual direction columns, and an actual same-size
residual matrix are produced from the scalar gates alone. This theorem does not
assume any of the final circle geometry or distance-separation conclusions. -/
theorem colex_circle_macro_exists {n : ℕ} (hn : 1 ≤ n) {K : ℝ}
    (hK : 10 ≤ K) (hlarge : 16384*(harmonic (n+2) : ℝ)^2 ≤ K)
    (hnK : (n+1 : ℕ) ≤ K) (S R s θ k : ℝ)
    (hr : (R/S)^2 ≤ K^2/16) (hc : 1 ≤ s*k)
    (hR : 7056*(s/θ)^2*(s*k)^2*(K+(n+1 : ℕ)) ≤ R^2) :
    ∃ p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ U : Matrix (Fin (n+1)) (Fin (n+2)) ℝ,
    ∃ W : Matrix (Fin (n+2)) (Fin (n+2)) ℝ,
      (∀ A B, A ≠ B → ‖p A-p B‖^2 = (colexDistance K A B)^2-2*(R/S)^2) ∧
      (Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => R^2)) ∧
      (∀ A B,
        (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
          (s/θ)*((if B.val < A.val then colexDistance K A B else 0) +
            (s*k)*(if A.val < B.val then colexDistance K A B else 0))) := by
  obtain ⟨p, _, hpd, _⟩ := flattened_colex_all_anchor_potentials hn hK hlarge ((R/S)^2) hr
  obtain ⟨F, G, hFproj, hGproj, hFbudget, hGbudget⟩ :=
    sourceFineCoarseCoefficients_exist hn hK hlarge ((R/S)^2) hr hnK p hpd
  let U := circleDirectionMatrix s θ k F G
  obtain ⟨W, hW⟩ := circle_completion_factor U R
    (circleDirectionMatrix_budget (by linarith : 0 ≤ K) hc F G hFbudget hGbudget hR)
  refine ⟨p, U, W, ?_, hW, ?_⟩
  · intro A B hAB
    have h := hpd B A
    simpa only [offDiagonalShift, Ne.symm hAB, if_false, colexSqData,
      colexDistance_symm K B A] using h
  · intro A B
    change (fun i => (p A-p B) i) ⬝ᵥ (fun i => circleDirection s θ k F G A i) = _
    rw [euclidean_dot_inner]
    exact circleDirection_projection K s θ k p F G hFproj hGproj A B

/-- The same colex distance formula, with a direct m-vertex index. -/
noncomputable def circleColexDistance {m : ℕ} (K : ℝ) (A B : Fin m) : ℝ :=
  if A.val < B.val then K + colexLabel A.val B.val
  else if B.val < A.val then K + colexLabel B.val A.val else 0

/-- Natural m-indexed wrapper, preserving the advertised m−1 macro dimension. -/
theorem colex_circle_macro_exists_m {m : ℕ} (hm : 3 ≤ m) {K : ℝ}
    (hK : 10 ≤ K) (hlarge : 16384*(harmonic m : ℝ)^2 ≤ K)
    (hmK : (m : ℝ) ≤ K) (S R s θ k : ℝ)
    (hr : (R/S)^2 ≤ K^2/16) (hc : 1 ≤ s*k)
    (hR : 7056*(s/θ)^2*(s*k)^2*(K+(m : ℝ)) ≤ R^2) :
    ∃ p : Fin m → EuclideanSpace ℝ (Fin (m-1)),
    ∃ U : Matrix (Fin (m-1)) (Fin m) ℝ,
    ∃ W : Matrix (Fin m) (Fin m) ℝ,
      (∀ A B, A ≠ B → ‖p A-p B‖^2 = (circleColexDistance K A B)^2-2*(R/S)^2) ∧
      (Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => R^2)) ∧
      (∀ A B,
        (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
          (s/θ)*((if B.val < A.val then circleColexDistance K A B else 0) +
            (s*k)*(if A.val < B.val then circleColexDistance K A B else 0))) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n+2 := ⟨m-2, by omega⟩
  rw [show n+2-1=n+1 by omega]
  have hn : 1 ≤ n := by omega
  have hnK : (n+1 : ℕ) ≤ K := by push_cast at *; linarith
  have hsmall : 7056*(s/θ)^2*(s*k)^2*(K+(n+1 : ℕ)) ≤ R^2 := by
    calc
      _ ≤ 7056*(s/θ)^2*(s*k)^2*(K+(n+2 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        push_cast
        linarith
      _ ≤ R^2 := hR
  simpa only [circleColexDistance, colexDistance] using colex_circle_macro_exists hn hK hlarge hnK S R s θ k hr hc hsmall

/-- Source C4, after the actual scale substitutions, supplies the quadratic
whole-matrix reserve. No additional analytic assumption is hidden here. -/
theorem circle_budget_of_C4 (C m s a k K : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hKm : 0 ≤ K+m) (hC4 : (84*s^2/a)*Real.sqrt (K+m) ≤ C*m) :
    7056*(s/(a/k))^2*(s*k)^2*(K+m) ≤ (C*m*k^2)^2 := by
  have hB : 0 ≤ (84*s^2/a)*Real.sqrt (K+m) := by positivity
  have hsq := mul_self_le_mul_self hB hC4
  have hsqrt := Real.sq_sqrt hKm
  have he : ((84*s^2/a)*Real.sqrt (K+m))^2 =
      7056*s^4/a^2*(K+m) := by rw [mul_pow, hsqrt]; ring
  have hsq' : 7056*s^4/a^2*(K+m) ≤ (C*m)^2 := by
    nlinarith only [hsq, he]
  have hmul := mul_le_mul_of_nonneg_right hsq' (sq_nonneg (k^2))
  have hleft : 7056*(s/(a/k))^2*(s*k)^2*(K+m) =
      (7056*s^4/a^2*(K+m))*(k^2)^2 := by field_simp
  rw [hleft]
  nlinarith only [hmul]

/-- The source C3 gate pays for the macro shortening at the actual scales. -/
theorem circle_shortening_of_C3 (C m s k K : ℝ) (hs : 0 < s) (hk : 0 < k)
    (hCm : 0 ≤ C*m) (hK : 0 ≤ K) (hC3 : 4*C*m/s^3 ≤ K) :
    ((C*m*k^2)/(s^3*k^2))^2 ≤ K^2/16 := by
  have he : C*m*k^2/(s^3*k^2) = C*m/s^3 := by field_simp
  rw [he]
  have hnonneg : 0 ≤ C*m/s^3 := div_nonneg hCm (by positivity)
  have hbound : C*m/s^3 ≤ K/4 := by
    rw [show 4*C*m/s^3 = 4*(C*m/s^3) by ring] at hC3
    linarith
  have hh := mul_self_le_mul_self hnonneg hbound
  nlinarith only [hh]

/-- Symmetry of the directly m-indexed colex distance. -/
theorem circleColexDistance_symm {m : ℕ} (K : ℝ) (A B : Fin m) :
    circleColexDistance K A B = circleColexDistance K B A := by
  by_cases hAB : A.val < B.val
  · have hBA : ¬B.val < A.val := by omega
    simp [circleColexDistance, hAB, hBA]
  · by_cases hBA : B.val < A.val <;> simp [circleColexDistance, hAB, hBA]

/-- The actual source projections specialize the general geometric identity
exactly to the new two-digit square-root formula. -/
theorem circlePoint_colex_cross_distance {m : ℕ}
    (p : Fin m → EuclideanSpace ℝ (Fin (m-1)))
    (U : Matrix (Fin (m-1)) (Fin m) ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (K S R s θ k : ℝ) (hS : S ≠ 0)
    (hmetric : ∀ A B, A ≠ B →
      ‖p A-p B‖^2 = (circleColexDistance K A B)^2-2*(R/S)^2)
    (hfactor : Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => R^2))
    (hproj : ∀ A B,
      (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
        (s/θ)*((if B.val < A.val then circleColexDistance K A B else 0) +
          (s*k)*(if A.val < B.val then circleColexDistance K A B else 0)))
    (A B : Fin m) (hAB : A.val < B.val) (z w : ℝ) :
    dist (circlePoint (fun A i => p A i) U W S R A z)
      (circlePoint (fun A i => p A i) U W S R B w) =
      Real.sqrt ((S*circleColexDistance K A B)^2 +
        2*(S*circleColexDistance K A B)*(s^2*k*(Real.sin z/θ)+s*(Real.sin w/θ))) := by
  have hne : A ≠ B := by intro h; subst B; omega
  have hBA : ¬B.val < A.val := by omega
  have hbase := shortened_macro_cancellation S R (circleColexDistance K A B)
    (‖p A-p B‖^2) hS (hmetric A B hne)
  have hbase' : S^2*(∑ i, (p A i-p B i)^2)+2*R^2 = (S*circleColexDistance K A B)^2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, WithLp.ofLp_sub, Pi.sub_apply] using hbase
  have hA := hproj A B
  have hB := hproj B A
  simp only [hAB, hBA, if_true, if_false, zero_add] at hA
  simp only [hAB, hBA, if_true, if_false, mul_zero, add_zero,
    circleColexDistance_symm K B A] at hB
  have hsine (v u : Fin (m-1) → ℝ) (t : ℝ) :
      v ⬝ᵥ (fun i => u i*Real.sin t) = (v ⬝ᵥ u)*Real.sin t := by
    simp only [dotProduct, Finset.sum_mul, mul_assoc]
  apply circlePoint_cross_distance (fun A i => p A i) U W S R
    (circleColexDistance K A B) (s^2*k*(Real.sin z/θ)) (s*(Real.sin w/θ))
    hfactor A B hne z w hbase'
  · change (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A*Real.sin z) = _
    rw [hsine, hA]
    ring
  · change (fun i => (p B-p A) i) ⬝ᵥ (fun i => U i B*Real.sin w) = _
    rw [hsine, hB]
    ring

end Pass5
end Erdos488.Geometry.SeparatedDistances.FixedDimension
