import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Local

namespace Erdos670R29

/-- Three angle doublings sharpen the elementary quadratic cosine bound.
This avoids adding an unformalized Taylor remainder estimate. -/
theorem cos_ruler_lower : (255/400 : ℝ) ≤ Real.cos (879/1000) := by
  have h0 := Real.one_sub_sq_div_two_le_cos (x := (879/8000 : ℝ))
  have h0' : (993963/1000000 : ℝ) ≤ Real.cos (879/8000) := by norm_num at h0 ⊢; linarith
  have e1 := Real.cos_two_mul (879/8000 : ℝ)
  have e2 := Real.cos_two_mul (879/4000 : ℝ)
  have e3 := Real.cos_two_mul (879/2000 : ℝ)
  norm_num at e1 e2 e3
  have h1 : (975924/1000000 : ℝ) ≤ Real.cos (879/4000) := by
    nlinarith [sq_nonneg (Real.cos (879/8000)-(993963/1000000 : ℝ))]
  have h2 : (904855/1000000 : ℝ) ≤ Real.cos (879/2000) := by
    nlinarith [sq_nonneg (Real.cos (879/4000)-(975924/1000000 : ℝ))]
  nlinarith [sq_nonneg (Real.cos (879/2000)-(904855/1000000 : ℝ))]

theorem sin_ruler_lower : (7658/10000 : ℝ) ≤ Real.sin (879/1000) := by
  have h := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 879/1000)
  norm_num at h ⊢
  linarith

theorem sin_ruler_upper : Real.sin (879/1000) ≤ (78/100 : ℝ) := by
  have h := Real.sin_sq_add_cos_sq (879/1000 : ℝ)
  have hc := cos_ruler_lower
  nlinarith [sq_nonneg (Real.cos (879/1000)-(255/400 : ℝ))]

#print axioms cos_ruler_lower
#print axioms sin_ruler_lower
#print axioms sin_ruler_upper
end Erdos670R29
