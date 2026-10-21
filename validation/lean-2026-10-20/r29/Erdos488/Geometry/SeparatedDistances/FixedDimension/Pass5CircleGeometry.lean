import Erdos488.Geometry.SeparatedDistances.FixedDimension.EuclideanCrossCoordinates

/-!
Orthogonal-circle geometry for the fifth-pass construction.
Source: consecutive-euclidean-distances, merge 1d8de6b,
candidate/fixed670-orthogonal-circles-pass5-20261013/orthogonal_circles.tex,
Lemma completion and equations cross-expansion and actual-point.

The old nine-block construction is not modified. The whole-matrix quadratic
budget below is the operator-norm hypothesis, not a columnwise substitute.
-/

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
namespace Pass5
open scoped BigOperators Matrix
open Matrix

/-- A norm budget for the entire direction matrix yields a same-size residual. -/
theorem circle_completion_factor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (R : ℝ)
    (hbudget : ∀ x : κ → ℝ, ∑ i, (U *ᵥ x) i ^ 2 ≤ R^2 * ∑ a, x a ^ 2) :
    ∃ W : Matrix κ κ ℝ, Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2) := by
  have hpsd : (Matrix.diagonal (fun _ : κ => R^2) - Uᵀ * U).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (Matrix.isHermitian_diagonal (fun _ : κ => R^2)).sub
        (by simpa using Matrix.isHermitian_conjTranspose_mul_self U)
    intro x
    have hgram : x ⬝ᵥ ((Uᵀ * U) *ᵥ x) = ∑ i, (U *ᵥ x) i ^ 2 := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      simp only [dotProduct, pow_two]
    have hdiag : x ⬝ᵥ ((Matrix.diagonal (fun _ : κ => R^2)) *ᵥ x) =
        R^2 * ∑ a, x a ^ 2 := by
      simp only [Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hgram, hdiag,
      sub_nonneg] using hbudget x
  obtain ⟨W, hW⟩ := psd_same_size_gram_factor _ hpsd
  refine ⟨W, ?_⟩
  rw [hW]
  abel

/-- Coordinate type of the new construction: macro space and two m-blocks. -/
abbrev CircleCoordinate (ι κ : Type*) := ι ⊕ (κ ⊕ κ)

/-- The literal circle perturbation, with the prescribed macro projection. -/
noncomputable def circlePerturbation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (R : ℝ) (A : κ) (z : ℝ) : CircleCoordinate ι κ → ℝ :=
  Sum.elim (fun i => U i A * Real.sin z)
    (Sum.elim (fun i => W i A * Real.sin z)
      (fun i => if i = A then R * Real.cos z else 0))

/-- Actual Euclidean coordinates; all points share the same three blocks. -/
noncomputable def circlePoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (A : κ) (z : ℝ) : EuclideanSpace ℝ (CircleCoordinate ι κ) :=
  WithLp.toLp 2 (Sum.elim (fun i => S * q A i + U i A * Real.sin z)
    (Sum.elim (fun i => W i A * Real.sin z)
      (fun i => if i = A then R * Real.cos z else 0)))

/-- The factor equation gives the exact pairwise column Gram matrix. -/
theorem completed_column_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2)) (A B : κ) :
    (∑ i, U i A * U i B) + (∑ i, W i A * W i B) =
      if A = B then R^2 else 0 := by
  have h := congrFun (congrFun hfactor A) B
  simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply] using h

/-- The circle planes for distinct anchors are genuinely orthogonal. -/
theorem circlePerturbation_dot {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (z w : ℝ) :
    circlePerturbation U W R A z ⬝ᵥ circlePerturbation U W R B w =
      if A = B then R^2 * (Real.sin z * Real.sin w + Real.cos z * Real.cos w)
      else 0 := by
  have hm (M : Matrix ι κ ℝ) :
      (∑ i, (M i A * Real.sin z) * (M i B * Real.sin w)) =
        (∑ i, M i A * M i B) * (Real.sin z * Real.sin w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hw : (∑ i, (W i A * Real.sin z) * (W i B * Real.sin w)) =
      (∑ i, W i A * W i B) * (Real.sin z * Real.sin w) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [circlePerturbation, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  rw [hm, hw]
  have hc := completed_column_dot U W R hfactor A B
  by_cases hAB : A = B
  · subst B
    simp only [ite_true] at hc ⊢
    have hp : (∑ i, (if i = A then R * Real.cos z else 0) *
        (if i = A then R * Real.cos w else 0)) =
        R^2 * (Real.cos z * Real.cos w) := by
      have he (i : κ) :
          (if i = A then R * Real.cos z else 0) *
            (if i = A then R * Real.cos w else 0) =
          if i = A then R^2 * (Real.cos z * Real.cos w) else 0 := by
        by_cases hi : i = A <;> simp [hi] <;> ring
      simp_rw [he]
      simp
    rw [hp]
    linear_combination (Real.sin z * Real.sin w) * hc
  · have hp : (∑ i, (if i = A then R * Real.cos z else 0) *
        (if i = B then R * Real.cos w else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = A
      · subst i
        simp [hAB]
      · simp [hi]
    rw [hp, if_neg hAB]
    rw [if_neg hAB] at hc
    linear_combination (Real.sin z * Real.sin w) * hc

/-- Every perturbation has the common squared norm R². -/
theorem circlePerturbation_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z : ℝ) :
    (∑ i, (circlePerturbation U W R A z i)^2) = R^2 := by
  have h := circlePerturbation_dot U W R hfactor A A z z
  simp only [ite_true, dotProduct, ← pow_two] at h
  rw [Real.sin_sq_add_cos_sq, mul_one] at h
  exact h

/-- Exact common-circle chord square, derived from the completed Gram matrix. -/
theorem circlePerturbation_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    (∑ i, (circlePerturbation U W R A z i - circlePerturbation U W R A w i)^2) =
      (2*R*Real.sin ((z-w)/2))^2 := by
  rw [sum_sq_sub, circlePerturbation_square U W R hfactor,
    circlePerturbation_square U W R hfactor, circlePerturbation_dot U W R hfactor]
  simp only [ite_true]
  have h := Real.sin_sq_eq_half_sub ((z-w)/2)
  rw [show 2*((z-w)/2)=z-w by ring, Real.cos_sub] at h
  nlinarith [congrArg (fun t : ℝ => R^2*t) h]

/-- Distinct circle planes contribute precisely 2R² to the squared distance. -/
theorem circlePerturbation_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ) (R : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ) :
    (∑ i, (circlePerturbation U W R A z i - circlePerturbation U W R B w i)^2) =
      2*R^2 := by
  rw [sum_sq_sub, circlePerturbation_square U W R hfactor,
    circlePerturbation_square U W R hfactor, circlePerturbation_dot U W R hfactor,
    if_neg hAB]
  ring

/-- Same-cluster distances are actual circle chords, with no extra correction. -/
theorem circlePoint_same_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R A w)^2 =
      (2*R*Real.sin ((z-w)/2))^2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simpa only [circlePoint, circlePerturbation, WithLp.ofLp_toLp,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Real.dist_eq, sq_abs,
    add_sub_add_left_eq_sub] using circlePerturbation_same_square U W R hfactor A z w

/-- The unsigned chord formula for actual points. -/
theorem circlePoint_same_distance {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hR : 0 ≤ R)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A : κ) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R A w) =
      2*R*|Real.sin ((z-w)/2)| := by
  have hsq := circlePoint_same_square q U W S R hfactor A z w
  have habs := sq_abs (Real.sin ((z-w)/2))
  have hd := dist_nonneg (x := circlePoint q U W S R A z)
    (y := circlePoint q U W S R A w)
  have hrhs : 0 ≤ 2*R*|Real.sin ((z-w)/2)| := by positivity
  nlinarith [congrArg (fun t : ℝ => (2*R)^2*t) habs]

/-- Exact cross expansion in the literal r+2m coordinate space. -/
theorem circlePoint_cross_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R : ℝ) (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R B w)^2 =
      S^2*(∑ i, (q A i-q B i)^2) + 2*R^2 +
        2*S*((q A-q B) ⬝ᵥ ((fun i => U i A*Real.sin z)-(fun i => U i B*Real.sin w))) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [circlePoint, WithLp.ofLp_toLp, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Real.dist_eq, sq_abs]
  rw [macro_coordinate_expansion]
  have hp := circlePerturbation_cross_square U W R hfactor A B hAB z w
  simp only [circlePerturbation, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hp
  linarith

/-- The shortened macro metric and the two directed projections give the exact
new cross metric. This is linear in both digits; no quadratic feature is used. -/
theorem circlePoint_cross_metric_square {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R D α β : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ)
    (hbase : S^2*(∑ i, (q A i-q B i)^2)+2*R^2 = (S*D)^2)
    (hprojA : (q A-q B) ⬝ᵥ (fun i => U i A*Real.sin z) = D*α)
    (hprojB : (q B-q A) ⬝ᵥ (fun i => U i B*Real.sin w) = D*β) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R B w)^2 =
      (S*D)^2 + 2*(S*D)*(α+β) := by
  have h := circlePoint_cross_square q U W S R hfactor A B hAB z w
  have hneg : (q A-q B) ⬝ᵥ (fun i => U i B*Real.sin w) = -(D*β) := by
    rw [show q A-q B = -(q B-q A) by abel, neg_dotProduct, hprojB]
  rw [dotProduct_sub, hprojA, hneg] at h
  nlinarith only [h, hbase]

/-- The exact square-root cross-length formula for actual points. -/
theorem circlePoint_cross_distance {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (q : κ → ι → ℝ) (U : Matrix ι κ ℝ) (W : Matrix κ κ ℝ)
    (S R D α β : ℝ)
    (hfactor : Uᵀ * U + Wᵀ * W = Matrix.diagonal (fun _ => R^2))
    (A B : κ) (hAB : A ≠ B) (z w : ℝ)
    (hbase : S^2*(∑ i, (q A i-q B i)^2)+2*R^2 = (S*D)^2)
    (hprojA : (q A-q B) ⬝ᵥ (fun i => U i A*Real.sin z) = D*α)
    (hprojB : (q B-q A) ⬝ᵥ (fun i => U i B*Real.sin w) = D*β) :
    dist (circlePoint q U W S R A z) (circlePoint q U W S R B w) =
      Real.sqrt ((S*D)^2 + 2*(S*D)*(α+β)) := by
  rw [← circlePoint_cross_metric_square q U W S R D α β hfactor A B hAB z w
    hbase hprojA hprojB, Real.sqrt_sq (dist_nonneg)]

/-- Source shortening cancels the entire common radius contribution. -/
theorem shortened_macro_cancellation (S R D Q : ℝ) (hS : S ≠ 0)
    (hQ : Q = D^2 - 2*(R/S)^2) :
    S^2*Q + 2*R^2 = (S*D)^2 := by
  rw [hQ]
  field_simp [hS]
  <;> ring

/-- Exact dimension of the new coordinate family. -/
theorem circleCoordinate_card (m : ℕ) (hm : 0 < m) :
    Fintype.card (CircleCoordinate (Fin (m-1)) (Fin m)) = 3*m-1 := by
  simp only [CircleCoordinate, Fintype.card_sum, Fintype.card_fin]
  omega

end Pass5
end Erdos488.Geometry.SeparatedDistances.FixedDimension
