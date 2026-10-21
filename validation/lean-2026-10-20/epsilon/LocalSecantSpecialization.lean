import TwoCircleSecant
import Mathlib.Tactic

namespace EuclideanEpsilonResearch

/-- Literal local-ruler specialization of the existing two-circle secant lemma.
The ruler's arithmetic uniqueness and lag order are explicit hypotheses here. -/
theorem local_ruler_chord_gap
    (m k p a d₁ d₂ g₁ g₂ : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hp : 0 < p)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hd1 : 1 ≤ d₁) (hdd : d₁ ≤ d₂) (hd2 : d₂ < k)
    (hg1 : (3*d₁-1)*p < g₁) (hg2 : g₂ < 3*p*k)
    (hgap : 1 ≤ g₂-g₁) (hpmax : p < 4*m*k) :
    (14/3 : ℝ) <
      twoCircleLength (128*m*k^2) (a*d₂/(2*k)) (g₂/(6*p*k)) -
      twoCircleLength (128*m*k^2) (a*d₁/(2*k)) (g₁/(6*p*k)) := by
  have hden : 0 < 6*p*k := by positivity
  have hden2 : 0 < 2*k := by positivity
  have hd10 : 0 < d₁ := by linarith
  have hd20 : 0 < d₂ := hd10.trans_le hdd
  have hg10 : 0 < g₁ := by
    have : 0 < (3*d₁-1)*p := mul_pos (by linarith) hp
    exact this.trans hg1
  have hg12 : g₁ ≤ g₂ := by linarith
  have hh1 : 0 ≤ a*d₁/(2*k) := by positivity
  have hhh : a*d₁/(2*k) ≤ a*d₂/(2*k) := by
    apply div_le_div_of_nonneg_right _ hden2.le
    exact mul_le_mul_of_nonneg_left hdd ha
  have hh2 : a*d₂/(2*k) ≤ 1/2 := by
    rw [div_le_iff₀ hden2]
    have : a*d₂ ≤ d₂ := by nlinarith
    linarith
  have hu1 : 0 < g₁/(6*p*k) := div_pos hg10 hden
  have huu : g₁/(6*p*k) ≤ g₂/(6*p*k) :=
    div_le_div_of_nonneg_right hg12 hden.le
  have hu2 : g₂/(6*p*k) ≤ 1/2 := by
    rw [div_le_iff₀ hden]
    linarith
  have hcone0 : a*d₁*2*p ≤ g₁ := by
    have h1 : a*d₁ ≤ d₁ := by nlinarith
    have h2 : a*d₁*(2*p) ≤ d₁*(2*p) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 2*d₁*p ≤ (3*d₁-1)*p := by nlinarith
    nlinarith
  have hcone : a*d₁/(2*k) ≤ (3/2)*(g₁/(6*p*k)) := by
    apply (div_le_iff₀ hden2).2
    have he : (3/2)*(g₁/(6*p*k))*(2*k) = g₁/(2*p) := by
      field_simp
      ring
    rw [he]
    apply (le_div_iff₀ (show 0 < 2*p by positivity)).2
    nlinarith
  have hsec := two_circle_chord_gap (128*m*k^2)
    (a*d₁/(2*k)) (a*d₂/(2*k)) (g₁/(6*p*k)) (g₂/(6*p*k))
    (by positivity) hh1 hhh hh2 hu1 huu hu2 hcone
  have he : (7*(128*m*k^2)/8)*(g₂/(6*p*k)-g₁/(6*p*k)) =
      (56*m*k/(3*p))*(g₂-g₁) := by
    field_simp
    ring
  rw [he] at hsec
  have hcoeff : (14/3 : ℝ) < 56*m*k/(3*p) := by
    rw [lt_div_iff₀ (show 0 < 3*p by positivity)]
    nlinarith
  have hscaled : 56*m*k/(3*p) ≤ (56*m*k/(3*p))*(g₂-g₁) := by
    have : 0 ≤ 56*m*k/(3*p) := by positivity
    nlinarith
  exact hcoeff.trans_le (hscaled.trans hsec)

#print axioms local_ruler_chord_gap
end EuclideanEpsilonResearch
