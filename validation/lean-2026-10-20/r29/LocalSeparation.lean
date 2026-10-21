import LocalScalar

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma local_ratio_budget (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hdk : d ≤ k) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    (2391/2500 : ℝ)^2*(localH k d)^2 ≤
      (1-(2391/2500 : ℝ)^2)*(localB k p g)^2 := by
  obtain ⟨hH0,hH⟩ := localH_bounds k d hk hd hdk
  have hB := localB_ray k p d g hk hp hd hg hgup
  have hkd : 0 ≤ k*d := mul_nonneg hk.le hd
  have hHsq : (localH k d)^2 ≤ ((263133/100000 : ℝ)*(k*d))^2 := by
    apply (sq_le_sq₀ hH0 (by positivity)).2
    nlinarith only [hH]
  have hBsq : ((86490963/10000000 : ℝ)*(k*d))^2 ≤ (localB k p g)^2 := by
    apply (sq_le_sq₀ (by positivity) (by nlinarith only [hB,hkd])).2
    nlinarith only [hB]
  nlinarith [sq_nonneg (k*d)]

/-- Strict unit separation follows from an integer-sized ruler increment. -/
theorem local_fixed_lag_gap (k p d x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hd : 0 ≤ d) (hdk : d ≤ k)
    (hx : p*d ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 2*p*k) :
    1 < localLength k p d y-localLength k p d x := by
  have hxy : x ≤ y := by linarith
  have hx0 : 0 ≤ x := (mul_nonneg hp.le hd).trans hx
  have hs := localB_slope k p x y hk hp hpk hx0 hxy hy
  have hbx := localB_ray k p d x hk hp hd hx (hxy.trans hy)
  have hb0 : 0 ≤ localB k p x := by nlinarith [mul_nonneg hk.le hd]
  have hbxy : localB k p x ≤ localB k p y := by linarith
  have hb := local_ratio_budget k p d x hk hp hd hdk hx (hxy.trans hy)
  have hnorm := norm_secant_lower (localH k d) (localB k p x) (localB k p y)
    (2391/2500) hb0 hbxy (by norm_num) (by norm_num) hb
  unfold localLength
  nlinarith

lemma localH_monotone (k d e : ℝ) (hk : 0 < k)
    (hd : 0 ≤ d) (hde : d ≤ e) (hek : e ≤ k) : localH k d ≤ localH k e := by
  have hscale : ((519/1000)/k)*k ≤ (519/1000 : ℝ)*1 := by
    field_simp <;> norm_num
  have h := pass5Chord_lower_difference ((507/100)*k^2) ((519/1000)/k) 1
    (519/1000) k d e (by positivity) (by positivity) (by norm_num) (by norm_num)
    hscale hd hde hek
  have hcoef : 0 ≤ (((507/100)*k^2)*((519/1000)/k)/1)*(1-(519/1000 : ℝ)^2/8) := by
    apply mul_nonneg (by positivity)
    norm_num
  have hm := mul_nonneg hcoef (sub_nonneg.mpr hde)
  exact le_of_sub_nonneg (hm.trans h)

/-- The full real local comparison permits a nondecreasing lag. -/
theorem local_ordered_gap (k p d e x y : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hpk : p ≤ (303/50)*k) (hd : 0 ≤ d) (hde : d ≤ e) (hek : e ≤ k)
    (hx : p*d ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 2*p*k) :
    1 < localLength k p e y-localLength k p d x := by
  have h := local_fixed_lag_gap k p d x y hk hp hpk hd (hde.trans hek) hx hgap hy
  have hH := localH_monotone k d e hk hd hde hek
  have hH0 := (localH_bounds k d hk hd (hde.trans hek)).1
  have hs : (localH k d)^2 ≤ (localH k e)^2 := (sq_le_sq₀ hH0 (hH0.trans hH)).2 hH
  have hmono : localLength k p d y ≤ localLength k p e y :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

#print axioms local_ordered_gap
end Erdos670R29
