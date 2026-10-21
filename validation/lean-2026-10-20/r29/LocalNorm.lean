import TrigBounds

namespace Erdos670R29

/-- A denominator-free lower secant bound for a two-coordinate norm. -/
theorem norm_secant_lower (H x y lam : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hbudget : lam^2*H^2 ≤ (1-lam^2)*x^2) :
    lam*(y-x) ≤ Real.sqrt (H^2+y^2)-Real.sqrt (H^2+x^2) := by
  let X := Real.sqrt (H^2+x^2)
  let Y := Real.sqrt (H^2+y^2)
  have hX : X^2 = H^2+x^2 := Real.sq_sqrt (by positivity)
  have hY : Y^2 = H^2+y^2 := Real.sq_sqrt (by positivity)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hxy2 : x^2 ≤ y^2 := sq_le_sq₀ hx (hx.trans hxy) |>.2 hxy
  have hl2 : 0 ≤ 1-lam^2 := by nlinarith
  have hby := mul_le_mul_of_nonneg_left hxy2 hl2
  have hlX : lam*X ≤ x := by nlinarith [mul_nonneg hlam hX0]
  have hlY : lam*Y ≤ y := by nlinarith [mul_nonneg hlam hY0]
  have hmono : X ≤ Y := Real.sqrt_le_sqrt (by nlinarith)
  by_cases hsum : X+Y=0
  · have : X=0 ∧ Y=0 := by constructor <;> linarith
    rcases this with ⟨hxx,hyy⟩
    have hxz : x=0 := by nlinarith [sq_nonneg H]
    have hyz : y=0 := by nlinarith [sq_nonneg H]
    change lam*(y-x) ≤ Y-X
    rw [hxz,hyz,hxx,hyy]
    simp
  have hsumpos : 0 < X+Y := by positivity
  change lam*(y-x) ≤ Y-X
  apply (mul_le_mul_iff_of_pos_right hsumpos).mp
  have hm := mul_le_mul_of_nonneg_right (add_le_add hlX hlY) (sub_nonneg.mpr hxy)
  nlinarith only [hm,hX,hY]

/-- A simple ray bound is sufficient for the local ratio budget. -/
theorem sin_ruler_ray (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 879/1000) :
    (87/100 : ℝ)*x ≤ Real.sin x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x; simp
  have hs := Real.sin_gt_sub_cube h
  have hx2 : x^2 ≤ (879/1000 : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hx2 hx
  nlinarith

#print axioms norm_secant_lower
#print axioms sin_ruler_ray
end Erdos670R29
