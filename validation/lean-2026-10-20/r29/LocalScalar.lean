import LocalNorm

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def localH (k d : ℝ) : ℝ :=
  pass5Chord ((507/100)*k^2) ((519/1000)/k) 1 d
noncomputable def localB (k p g : ℝ) : ℝ :=
  pass5Chord ((1131/100)*k^2) ((879/500)/k) (2*p) g
noncomputable def localLength (k p d g : ℝ) : ℝ :=
  Real.sqrt ((localH k d)^2+(localB k p g)^2)

lemma chord_lower_cos (R θ D Y x y : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hD : 0 < D)
    (hscale : θ*Y ≤ (879/500)*D) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    (R*θ/D)*(255/400)*(y-x) ≤ pass5Chord R θ D y-pass5Chord R θ D x := by
  have hd (z : ℝ) := hasDerivAt_pass5Chord R θ D z hD.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  have harg0 : 0 ≤ θ*z/(2*D) := div_nonneg (mul_nonneg hθ.le hz'.1) (by positivity)
  have harg : θ*z/(2*D) ≤ (879/1000 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*D)).2
    nlinarith [mul_le_mul_of_nonneg_left hz'.2 hθ.le]
  have hpi : (879/1000 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  have hcos := cos_ruler_lower.trans (Real.cos_le_cos_of_nonneg_of_le_pi harg0 hpi harg)
  rw [(hd z).deriv]
  exact mul_le_mul_of_nonneg_left hcos (by positivity)

lemma localB_slope (k p x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2*p*k) :
    (5229/5000 : ℝ)*(y-x) ≤ localB k p y-localB k p x := by
  have hs : ((879/500)/k)*(2*p*k) = (879/500)*(2*p) := by field_simp <;> ring
  have h := chord_lower_cos ((1131/100)*k^2) ((879/500)/k) (2*p) (2*p*k) x y
    (by positivity) (by positivity) (by positivity) hs.le hx hxy hy
  have he : (((1131/100)*k^2)*((879/500)/k)/(2*p))*(255/400) =
      (50701599/8000000 : ℝ)*k/p := by field_simp <;> ring
  rw [he] at h
  have hl : (5229/5000 : ℝ) ≤ (50701599/8000000 : ℝ)*k/p := by
    apply (le_div_iff₀ hp).2
    nlinarith
  exact (mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hxy)).trans h

lemma localH_bounds (k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hdk : d ≤ k) :
    0 ≤ localH k d ∧ localH k d ≤ (263133/100000 : ℝ)*k*d := by
  have harg0 : 0 ≤ ((519/1000)/k)*d/(2*1) := by positivity
  have harg : ((519/1000)/k)*d/(2*1) ≤ (519/2000 : ℝ) := by
    field_simp
    nlinarith
  constructor
  · unfold localH pass5Chord
    apply mul_nonneg (by positivity)
    exact Real.sin_nonneg_of_nonneg_of_le_pi harg0 (harg.trans (by linarith [Real.two_le_pi]))
  · have h := pass5Chord_upper ((507/100)*k^2) ((519/1000)/k) 1 d
      (by positivity) (by positivity) (by norm_num) hd
    have he : ((507/100)*k^2)*((519/1000)/k)/1*d = (263133/100000 : ℝ)*k*d := by
      field_simp; ring
    simpa only [he, localH] using h

lemma localB_ray (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    (86490963/10000000 : ℝ)*k*d ≤ localB k p g := by
  have hg0 : 0 ≤ g := (mul_nonneg hp.le hd).trans hg
  have harg0 : 0 ≤ ((879/500)/k)*g/(2*(2*p)) := by positivity
  have he : ((879/500)/k)*g/(2*(2*p)) = (879/2000)*g/(p*k) := by field_simp <;> ring
  have harg : ((879/500)/k)*g/(2*(2*p)) ≤ (879/1000 : ℝ) := by
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < p*k)).2
    nlinarith
  have h := sin_ruler_ray _ harg0 harg
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*((1131/100 : ℝ)*k^2) by positivity)
  have hs : 2*((1131/100 : ℝ)*k^2)*((87/100)*(((879/500)/k)*g/(2*(2*p)))) =
      (86490963/10000000 : ℝ)*k*g/p := by field_simp <;> ring
  rw [hs] at hm
  have hl : (86490963/10000000 : ℝ)*k*d ≤ (86490963/10000000 : ℝ)*k*g/p := by
    apply (le_div_iff₀ hp).2
    nlinarith [mul_le_mul_of_nonneg_left hg (show 0 ≤ (86490963/10000000 : ℝ)*k by positivity)]
  exact hl.trans hm

#print axioms localB_slope
#print axioms localH_bounds
#print axioms localB_ray
end Erdos670R29
