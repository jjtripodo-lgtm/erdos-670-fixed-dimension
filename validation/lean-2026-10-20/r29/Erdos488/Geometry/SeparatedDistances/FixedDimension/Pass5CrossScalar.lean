import Erdos488.Geometry.SeparatedDistances.FixedDimension.SpectrumSeparation

/-! The exact square-root metric used by the fifth-pass orthogonal circles.
All slope estimates below are algebraic secant estimates; no differentiability
or approximation error is assumed. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Phi (ν T : ℝ) : ℝ := Real.sqrt (ν^2 + 2*ν*T)

/-- The digit budget implies strict positivity of the exact radicand. -/
theorem pass5Phi_radicand_pos (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    0 < ν^2 + 2*ν*T := by
  have hlow := (abs_le.mp hT).1
  have hb := mul_le_mul_of_nonneg_left hbudget hν.le
  have ht := mul_le_mul_of_nonneg_left hlow hν.le
  have hp : 0 < (τ*ν)^2 := sq_pos_of_pos (mul_pos hτ hν)
  nlinarith

/-- The exact metric has the square prescribed by the geometry. -/
theorem pass5Phi_sq (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    (pass5Phi ν T)^2 = ν^2 + 2*ν*T := by
  exact Real.sq_sqrt (pass5Phi_radicand_pos ν τ H T hν hτ hT hbudget).le

/-- The root lies between τν and ν/τ, with the upper bound denominator-cleared. -/
theorem pass5Phi_range (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    τ*ν ≤ pass5Phi ν T ∧ τ*pass5Phi ν T ≤ ν := by
  have hsq := pass5Phi_sq ν τ H T hν hτ hT hbudget
  have hnonneg : 0 ≤ pass5Phi ν T := Real.sqrt_nonneg _
  have hlo := (abs_le.mp hT).1
  have hhi := (abs_le.mp hT).2
  have hb := mul_le_mul_of_nonneg_left hbudget hν.le
  have hl := mul_le_mul_of_nonneg_left hlo hν.le
  have hu := mul_le_mul_of_nonneg_left hhi hν.le
  have hrootlo : (τ*ν)^2 ≤ (pass5Phi ν T)^2 := by nlinarith
  have hrootup : (pass5Phi ν T)^2 ≤ (2-τ^2)*ν^2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hrootup (sq_nonneg τ)
  have hrem : 0 ≤ ((1-τ^2)*ν)^2 := sq_nonneg _
  constructor
  · nlinarith [mul_pos hτ hν]
  · have hs : (τ*pass5Phi ν T)^2 ≤ ν^2 := by nlinarith only [ht, hrem]
    nlinarith [mul_nonneg hτ.le hnonneg]

/-- Uniform lower and upper secant slopes on the entire digit interval. -/
theorem pass5Phi_secant (ν τ H u v : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hu : |u| ≤ H) (hv : |v| ≤ H)
    (hbudget : 2*H ≤ (1-τ^2)*ν) (huv : u ≤ v) :
    τ*(v-u) ≤ pass5Phi ν v-pass5Phi ν u ∧
      pass5Phi ν v-pass5Phi ν u ≤ (v-u)/τ := by
  have huSq := pass5Phi_sq ν τ H u hν hτ hu hbudget
  have hvSq := pass5Phi_sq ν τ H v hν hτ hv hbudget
  obtain ⟨huLo, huHi⟩ := pass5Phi_range ν τ H u hν hτ hτ1 hu hbudget
  obtain ⟨hvLo, hvHi⟩ := pass5Phi_range ν τ H v hν hτ hτ1 hv hbudget
  have hp : 0 < τ*ν := mul_pos hτ hν
  have hmono : pass5Phi ν u ≤ pass5Phi ν v := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hid : (pass5Phi ν v-pass5Phi ν u)*(pass5Phi ν v+pass5Phi ν u) =
      2*ν*(v-u) := by nlinarith only [huSq, hvSq]
  have hsum : 0 < pass5Phi ν v+pass5Phi ν u := by linarith
  constructor
  · apply (mul_le_mul_iff_of_pos_right hsum).mp
    have hb := mul_le_mul_of_nonneg_right (show
      τ*(pass5Phi ν v+pass5Phi ν u) ≤ 2*ν by linarith) (sub_nonneg.mpr huv)
    nlinarith only [hb, hid]
  · apply (le_div_iff₀ hτ).mpr
    have hb := mul_le_mul_of_nonneg_right (show
      2*τ*ν ≤ pass5Phi ν v+pass5Phi ν u by linarith) (sub_nonneg.mpr hmono)
    have hm : (2*ν)*((pass5Phi ν v-pass5Phi ν u)*τ) ≤ (2*ν)*(v-u) := by
      nlinarith only [hb, hid]
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2*ν)).mp hm

@[simp] theorem pass5Phi_zero (ν : ℝ) (hν : 0 ≤ ν) : pass5Phi ν 0 = ν := by
  simp [pass5Phi, Real.sqrt_sq_eq_abs, abs_of_nonneg hν]

/-- The exact baseline-displacement bound, uniform in all digit values. -/
theorem pass5Phi_displacement (ν τ H T : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hT : |T| ≤ H) (hbudget : 2*H ≤ (1-τ^2)*ν) :
    |pass5Phi ν T-ν| ≤ H/τ := by
  have hH : 0 ≤ H := (abs_nonneg T).trans hT
  have hz : |(0 : ℝ)| ≤ H := by simpa using hH
  by_cases ht : 0 ≤ T
  · have hs := (pass5Phi_secant ν τ H 0 T hν hτ hτ1 hz hT hbudget ht).2
    rw [pass5Phi_zero ν hν.le] at hs
    have hmono : ν ≤ pass5Phi ν T := by
      have hl := (pass5Phi_secant ν τ H 0 T hν hτ hτ1 hz hT hbudget ht).1
      rw [pass5Phi_zero ν hν.le] at hl
      nlinarith [mul_nonneg hτ.le ht]
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    have hTH := (abs_le.mp hT).2
    exact hs.trans (div_le_div_of_nonneg_right (by linarith : T-0 ≤ H) hτ.le)
  · have hs := (pass5Phi_secant ν τ H T 0 hν hτ hτ1 hT hz hbudget (by linarith)).2
    rw [pass5Phi_zero ν hν.le] at hs
    have hmono : pass5Phi ν T ≤ ν := by
      have hl := (pass5Phi_secant ν τ H T 0 hν hτ hτ1 hT hz hbudget (by linarith)).1
      rw [pass5Phi_zero ν hν.le] at hl
      nlinarith [mul_nonneg hτ.le (show 0 ≤ -T by linarith)]
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    have hTH := (abs_le.mp hT).1
    have hd := div_le_div_of_nonneg_right (show 0-T ≤ H by linarith) hτ.le
    linarith

#print axioms pass5Phi_secant
#print axioms pass5Phi_displacement
end Erdos488.Geometry.SeparatedDistances.FixedDimension
