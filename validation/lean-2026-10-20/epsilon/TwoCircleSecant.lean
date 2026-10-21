import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace EuclideanEpsilonResearch

/-- Adding a monotone orthogonal component costs at most a factor two in a
ruler secant, if the first component is in the explicit cone. This is the
new local bridge, not an existence theorem for Euclidean configurations. -/
theorem two_circle_secant
    (h₁ h₂ b₁ b₂ : ℝ)
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂)
    (hcone : h₁^2 ≤ 3*b₁^2) :
    (b₂-b₁)/2 ≤ Real.sqrt (h₂^2+b₂^2)-Real.sqrt (h₁^2+b₁^2) := by
  have hb₂ : 0 < b₂ := hb₁.trans_le hb
  have hs₁ := Real.sq_sqrt (show 0 ≤ h₁^2+b₁^2 by positivity)
  have hs₂ := Real.sq_sqrt (show 0 ≤ h₁^2+b₂^2 by positivity)
  have hs₁0 := Real.sqrt_nonneg (h₁^2+b₁^2)
  have hs₂0 := Real.sqrt_nonneg (h₁^2+b₂^2)
  have hbSq : b₁^2 ≤ b₂^2 := by nlinarith
  have hs₁le : Real.sqrt (h₁^2+b₁^2) ≤ 2*b₁ := by nlinarith
  have hs₂le : Real.sqrt (h₁^2+b₂^2) ≤ 2*b₂ := by nlinarith
  have hmono : Real.sqrt (h₁^2+b₁^2) ≤ Real.sqrt (h₁^2+b₂^2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hprod := mul_le_mul_of_nonneg_left (add_le_add hs₁le hs₂le)
    (show 0 ≤ Real.sqrt (h₁^2+b₂^2)-Real.sqrt (h₁^2+b₁^2) by linarith)
  have hsec : (b₂-b₁)/2 ≤ Real.sqrt (h₁^2+b₂^2)-Real.sqrt (h₁^2+b₁^2) := by
    nlinarith
  have hlast : Real.sqrt (h₁^2+b₂^2) ≤ Real.sqrt (h₂^2+b₂^2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- Uniform sine secants on the ruler half-arc. -/
theorem sine_half_arc_secant (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1/2) : (7/8 : ℝ)*(y-x) ≤ Real.sin y-Real.sin x := by
  apply (convex_Icc (0 : ℝ) (1/2)).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (Real.hasDerivAt_sin z).continuousAt.continuousWithinAt)
    (fun z _ => (Real.hasDerivAt_sin z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) (1/2) := interior_subset hz
  rw [(Real.hasDerivAt_sin z).deriv]
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  nlinarith [hz'.1, hz'.2, mul_nonneg hz'.1 (sub_nonneg.mpr hz'.2)]

/-- The literal square-root sum of two circle chords. -/
noncomputable def twoCircleLength (R h u : ℝ) : ℝ :=
  Real.sqrt ((2*R*Real.sin h)^2+(2*R*Real.sin u)^2)

/-- Quantitative local comparison for independent digit and ruler circles.
The smaller digit half-angle may be up to 3/2 of the smaller ruler half-angle.
No macro, numerical tolerance, or asymptotic assumption is hidden here. -/
theorem two_circle_chord_gap (R h₁ h₂ u₁ u₂ : ℝ)
    (hR : 0 < R) (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (hh₂ : h₂ ≤ 1/2)
    (hu₁ : 0 < u₁) (hu : u₁ ≤ u₂) (hu₂ : u₂ ≤ 1/2)
    (hcone : h₁ ≤ (3/2)*u₁) :
    (7*R/8)*(u₂-u₁) ≤ twoCircleLength R h₂ u₂-twoCircleLength R h₁ u₁ := by
  have hu₁b : u₁ ≤ 1/2 := hu.trans hu₂
  have hslo := sine_half_arc_secant 0 u₁ (by norm_num) hu₁.le hu₁b
  simp only [Real.sin_zero, sub_zero] at hslo
  have hsu₁ : 0 < Real.sin u₁ := by nlinarith
  have hsugap := sine_half_arc_secant u₁ u₂ hu₁.le hu hu₂
  have hsumono : Real.sin u₁ ≤ Real.sin u₂ := by nlinarith
  have hsh₁ := sine_half_arc_secant 0 h₁ (by norm_num) hh₁ (hh.trans hh₂)
  simp only [Real.sin_zero, sub_zero] at hsh₁
  have hsh₁0 : 0 ≤ Real.sin h₁ := by nlinarith
  have hshgap := sine_half_arc_secant h₁ h₂ hh₁ hh hh₂
  have hshmono : Real.sin h₁ ≤ Real.sin h₂ := by nlinarith
  have hshupper := Real.sin_le hh₁
  have hcone' : Real.sin h₁ ≤ (12/7)*Real.sin u₁ := by nlinarith
  have hconeSq : (Real.sin h₁)^2 ≤ 3*(Real.sin u₁)^2 := by nlinarith
  have hconeScaled : (2*R*Real.sin h₁)^2 ≤ 3*(2*R*Real.sin u₁)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (2*R)) (show 0 ≤ 3*(Real.sin u₁)^2-(Real.sin h₁)^2 by linarith)]
  have h := two_circle_secant (2*R*Real.sin h₁) (2*R*Real.sin h₂)
    (2*R*Real.sin u₁) (2*R*Real.sin u₂) (by positivity)
    (mul_le_mul_of_nonneg_left hshmono (by positivity)) (by positivity)
    (mul_le_mul_of_nonneg_left hsumono (by positivity)) hconeScaled
  have hs := mul_le_mul_of_nonneg_left hsugap hR.le
  dsimp [twoCircleLength]
  nlinarith only [h, hs]

#print axioms two_circle_secant
#print axioms sine_half_arc_secant
#print axioms two_circle_chord_gap
end EuclideanEpsilonResearch

