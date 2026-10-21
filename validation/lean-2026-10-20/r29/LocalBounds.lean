import LocalSeparation

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma localB_bounds (k p g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hg : 0 ≤ g) (hgup : g ≤ 2*p*k) :
    0 ≤ localB k p g ∧ localB k p g ≤ (44109/2500 : ℝ)*k^2 := by
  have harg0 : 0 ≤ ((879/500)/k)*g/(2*(2*p)) := by positivity
  have he : ((879/500)/k)*g/(2*(2*p)) = (879/2000)*g/(p*k) := by field_simp <;> ring
  have harg : ((879/500)/k)*g/(2*(2*p)) ≤ (879/1000 : ℝ) := by
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < p*k)).2
    nlinarith
  have hpi : (879/1000 : ℝ) ≤ Real.pi/2 := by linarith [Real.two_le_pi]
  have hs := (Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ ((879/500)/k)*g/(2*(2*p)) by linarith [Real.pi_pos]) hpi harg).trans sin_ruler_upper
  constructor
  · unfold localB pass5Chord
    apply mul_nonneg (by positivity)
    exact Real.sin_nonneg_of_nonneg_of_le_pi harg0 (by linarith [Real.pi_pos])
  · have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*((1131/100 : ℝ)*k^2) by positivity)
    dsimp [localB,pass5Chord]
    nlinarith only [hm]

theorem localLength_upper (k p d g : ℝ) (hk : 0 < k) (hp : 0 < p)
    (hd : 0 ≤ d) (hdk : d ≤ k) (hg : 0 ≤ g) (hgup : g ≤ 2*p*k) :
    localLength k p d g < 18*k^2 := by
  obtain ⟨hH0,hH⟩ := localH_bounds k d hk hd hdk
  obtain ⟨hB0,hB⟩ := localB_bounds k p g hk hp hg hgup
  have hH' : localH k d ≤ (263133/100000 : ℝ)*k^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hdk hk.le]
  have hHsq : (localH k d)^2 ≤ ((263133/100000 : ℝ)*k^2)^2 :=
    (sq_le_sq₀ hH0 (by positivity)).2 hH'
  have hBsq : (localB k p g)^2 ≤ ((44109/2500 : ℝ)*k^2)^2 :=
    (sq_le_sq₀ hB0 (by positivity)).2 hB
  have hroot : (localLength k p d g)^2 = (localH k d)^2+(localB k p g)^2 :=
    Real.sq_sqrt (by positivity)
  have hpos : 0 < k^4 := pow_pos hk 4
  have hk2 : 0 < k^2 := sq_pos_of_pos hk
  nlinarith

theorem localLength_min (k p d g : ℝ) (hk : 100 ≤ k) (hp : 0 < p)
    (hd : 1 ≤ d) (hg : p*d ≤ g) (hgup : g ≤ 2*p*k) :
    1 < localLength k p d g := by
  have hk0 : 0 < k := by linarith
  have hb := localB_ray k p d g hk0 hp (by linarith) hg hgup
  have hkd : k ≤ k*d := by nlinarith
  have hs : (localLength k p d g)^2 = (localH k d)^2+(localB k p g)^2 :=
    Real.sq_sqrt (by positivity)
  have hn : 0 ≤ localLength k p d g := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (localH k d)]

#print axioms localLength_upper
#print axioms localLength_min
end Erdos670R29
