import LocalSecantSpecialization
import Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRuler

namespace EuclideanEpsilonResearch
open Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The unscaled deterministic integer ruler. The epsilon construction uses linear coefficient 3. -/
def epsilonRuler (p k A i : ℕ) : ℤ :=
  3 * (p : ℤ) * (i : ℤ) + ((i^2 + 2*k*A*i) % p : ℕ)

/-- A positive-lag difference, kept in the integers so subtraction never truncates. -/
def epsilonRulerGap (p k A i δ : ℕ) : ℤ :=
  epsilonRuler p k A (i + δ) - epsilonRuler p k A i

/-- Every actual ruler difference lies in its strict lag window. -/
theorem epsilonRulerGap_window (p k A i δ : ℕ) (hp : 0 < p) :
    (3 * (δ : ℤ) - 1) * p < epsilonRulerGap p k A i δ ∧
      epsilonRulerGap p k A i δ < (3 * (δ : ℤ) + 1) * p := by
  have h₀ : (0 : ℤ) ≤ ((i^2 + 2*k*A*i) % p : ℕ) := by positivity
  have h₁ : (0 : ℤ) ≤ (((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) := by positivity
  have h₂ : (((i^2 + 2*k*A*i) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  have h₃ : ((((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  dsimp [epsilonRulerGap, epsilonRuler]
  push_cast at *
  constructor <;> nlinarith

/-- Strictly positive lags give positive actual ruler gaps. -/
theorem epsilonRulerGap_pos (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ) :
    0 < epsilonRulerGap p k A i δ := by
  have hw := (epsilonRulerGap_window p k A i δ hp).1
  have hδ' : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  nlinarith

/-- Different lag windows are strictly ordered, with a gap greater than p. -/
theorem epsilonRulerGap_different_lag (p k A B i j δ ε : ℕ)
    (hp : 0 < p) (hδε : δ < ε) :
    (p : ℤ) < epsilonRulerGap p k B j ε - epsilonRulerGap p k A i δ := by
  have h₀ := (epsilonRulerGap_window p k A i δ hp).2
  have h₁ := (epsilonRulerGap_window p k B j ε hp).1
  have hδε' : (δ : ℤ) + 1 ≤ ε := by exact_mod_cast hδε
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  nlinarith

/-- The actual ruler difference has exactly the stated quadratic residue. -/
theorem epsilonRulerGap_residue (p k A i δ : ℕ) :
    epsilonRulerGap p k A i δ % (p : ℤ) =
      ((δ * (2*i + δ + 2*k*A) : ℕ) : ℤ) % (p : ℤ) := by
  have hpoly : (((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
      ((i^2 + 2*k*A*i : ℕ) : ℤ) = ((δ*(2*i+δ+2*k*A) : ℕ) : ℤ) := by
    push_cast
    ring
  calc
    epsilonRulerGap p k A i δ % (p : ℤ) =
        ((((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
          ((i^2 + 2*k*A*i : ℕ) : ℤ)) % (p : ℤ) := by
      simp [epsilonRulerGap, epsilonRuler, Int.add_emod, Int.sub_emod,
        Int.mul_emod, Int.natCast_emod]
    _ = _ := congrArg (fun z : ℤ => z % (p : ℤ)) hpoly

/-- Equal same-lag *actual* gaps force the same cluster and starting index. -/
theorem epsilonRulerGap_same_lag_injective (p m k δ A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hδp : δ < p) (hsize : 2*m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : epsilonRulerGap p k A i δ = epsilonRulerGap p k B j δ) : A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [epsilonRulerGap_residue, epsilonRulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective p m k δ A B i j hp hδ hδp hsize hA hB hi hj hnat

/-- Exhaustive uniqueness of all positive actual ruler gaps, across all clusters.
Different lags use disjoint windows; equal lags use prime cancellation. -/
theorem epsilonRulerGap_injective (p m k δ ε A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k)
    (heq : epsilonRulerGap p k A i δ = epsilonRulerGap p k B j ε) :
    A = B ∧ i = j ∧ δ = ε := by
  have hδε : δ = ε := by
    rcases lt_trichotomy δ ε with hlt | he | hgt
    · have h := epsilonRulerGap_different_lag p k A B i j δ ε hp.pos hlt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
    · exact he
    · have h := epsilonRulerGap_different_lag p k B A j i ε δ hp.pos hgt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
  subst ε
  obtain ⟨hAB,hij⟩ := epsilonRulerGap_same_lag_injective p m k δ A B i j
    hp hδ hδp hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩



/-- Literal local lengths, with the actual integer ruler and positive lag. -/
noncomputable def epsilonLocalLength (p m k A i δ : ℕ) (a : ℝ) : ℝ :=
  twoCircleLength (128*(m:ℝ)*(k:ℝ)^2) (a*(δ:ℝ)/(2*(k:ℝ)))
    ((epsilonRulerGap p k A i δ : ℝ)/(6*(p:ℝ)*(k:ℝ)))

theorem epsilonRulerGap_order_lag (p k A B i j δ ε : ℕ)
    (hp : 0 < p)
    (hgap : epsilonRulerGap p k A i δ < epsilonRulerGap p k B j ε) : δ ≤ ε := by
  by_contra h
  have hrev := epsilonRulerGap_different_lag p k B A j i ε δ hp (by omega)
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  omega

/-- Ordered actual ruler gaps imply strict ordered local chord lengths. -/
theorem epsilonLocalLength_ordered (p m k A B i j δ ε : ℕ) (a : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hp : 0 < p)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hδ : 0 < δ) (_hε : 0 < ε) (_hi : i+δ < k) (hj : j+ε < k)
    (hpmax : p < 4*m*k)
    (hg : epsilonRulerGap p k A i δ < epsilonRulerGap p k B j ε) :
    (14/3 : ℝ) < epsilonLocalLength p m k B j ε a-epsilonLocalLength p m k A i δ a := by
  have horder := epsilonRulerGap_order_lag p k A B i j δ ε hp hg
  have hw1 := (epsilonRulerGap_window p k A i δ hp).1
  have hw2 := (epsilonRulerGap_window p k B j ε hp).2
  have hgmax : epsilonRulerGap p k B j ε < 3*(p:ℤ)*k := by
    have he : (ε:ℤ)+1 ≤ k := by exact_mod_cast (show ε < k by omega)
    have hp' : (0:ℤ) < p := by exact_mod_cast hp
    nlinarith
  have hgstep : (1:ℤ) ≤ epsilonRulerGap p k B j ε-epsilonRulerGap p k A i δ := by omega
  exact local_ruler_chord_gap (m:ℝ) (k:ℝ) (p:ℝ) a (δ:ℝ) (ε:ℝ)
    (epsilonRulerGap p k A i δ : ℝ) (epsilonRulerGap p k B j ε : ℝ)
    (by exact_mod_cast hm) (by exact_mod_cast hk) (by exact_mod_cast hp) ha ha1
    (by exact_mod_cast hδ) (by exact_mod_cast horder) (by exact_mod_cast (show ε < k by omega))
    (by exact_mod_cast hw1) (by exact_mod_cast hgmax) (by exact_mod_cast hgstep)
    (by exact_mod_cast hpmax)

/-- Every genuinely different local edge has a strictly separated length.
The hypotheses concern indices and the prime, not an assumed separation. -/
theorem epsilonLocalLength_separated (p m k A B i j δ ε : ℕ) (a : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hk : 0 < k)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hδ : 0 < δ) (hε : 0 < ε) (hi : i+δ < k) (hj : j+ε < k)
    (hsize : 2*m*k < p) (hpmax : p < 4*m*k)
    (hA : A < m) (hB : B < m)
    (hne : ¬ (A = B ∧ i = j ∧ δ = ε)) :
    (14/3 : ℝ) < |epsilonLocalLength p m k A i δ a-epsilonLocalLength p m k B j ε a| := by
  have hkp : k < p := by nlinarith
  have hneq : epsilonRulerGap p k A i δ ≠ epsilonRulerGap p k B j ε := by
    intro h
    exact hne (epsilonRulerGap_injective p m k δ ε A B i j hp hδ hε
      (by omega) (by omega) hsize hA hB hi hj h)
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have h := epsilonLocalLength_ordered p m k A B i j δ ε a hm hk hp.pos ha ha1
      hδ hε hi hj hpmax hlt
    have habs := le_abs_self (epsilonLocalLength p m k B j ε a-epsilonLocalLength p m k A i δ a)
    rw [abs_sub_comm] at habs
    exact h.trans_le habs
  · exact (epsilonLocalLength_ordered p m k B A j i ε δ a hm hk hp.pos ha ha1
      hε hδ hj hi hpmax hgt).trans_le (le_abs_self _)

#print axioms epsilonRulerGap_injective
#print axioms epsilonLocalLength_ordered
#print axioms epsilonLocalLength_separated

/-- Every positive-lag local chord has length strictly greater than one. -/
theorem epsilonLocalLength_min (p m k A i δ : ℕ) (a : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hp : 0 < p)
    (hδ : 0 < δ) (hi : i+δ < k) :
    1 < epsilonLocalLength p m k A i δ a := by
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hd' : (1:ℝ) ≤ δ := by exact_mod_cast hδ
  have hw := epsilonRulerGap_window p k A i δ hp
  have hlo : (3*(δ:ℝ)-1)*(p:ℝ) < (epsilonRulerGap p k A i δ : ℝ) := by
    exact_mod_cast hw.1
  have hhi : (epsilonRulerGap p k A i δ : ℝ) < (3*(δ:ℝ)+1)*(p:ℝ) := by
    exact_mod_cast hw.2
  have hdk : (δ:ℝ)+1 ≤ k := by exact_mod_cast (show δ < k by omega)
  let u : ℝ := (epsilonRulerGap p k A i δ : ℝ)/(6*(p:ℝ)*(k:ℝ))
  let R : ℝ := 128*(m:ℝ)*(k:ℝ)^2
  have hR : 0 < R := by dsimp [R]; positivity
  have hden : 0 < 6*(p:ℝ)*(k:ℝ) := by positivity
  have hu0 : 0 < u := by
    apply div_pos _ hden
    nlinarith
  have hu2 : u ≤ 1/2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hulow : 1/(3*(k:ℝ)) ≤ u := by
    dsimp [u]
    apply (le_div_iff₀ hden).2
    have he : (1/(3*(k:ℝ)))*(6*(p:ℝ)*(k:ℝ)) = 2*(p:ℝ) := by
      field_simp
      ring
    rw [he]
    nlinarith
  have hs := sine_half_arc_secant 0 u (by norm_num) hu0.le hu2
  simp only [Real.sin_zero, sub_zero] at hs
  have hsin : (7/8:ℝ)*(1/(3*(k:ℝ))) ≤ Real.sin u := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 2*R by positivity)
  have he : 2*R*((7/8:ℝ)*(1/(3*(k:ℝ)))) = (224/3:ℝ)*(m:ℝ)*(k:ℝ) := by
    dsimp [R]
    field_simp
    ring
  rw [he] at hmul
  have hmk : (1:ℝ) ≤ (m:ℝ)*(k:ℝ) := by nlinarith
  have hb : 1 < 2*R*Real.sin u := by nlinarith
  have hsq := Real.sq_sqrt (show 0 ≤ (2*R*Real.sin (a*(δ:ℝ)/(2*(k:ℝ))))^2+
      (2*R*Real.sin u)^2 by positivity)
  have hnon := Real.sqrt_nonneg ((2*R*Real.sin (a*(δ:ℝ)/(2*(k:ℝ))))^2+
      (2*R*Real.sin u)^2)
  change 1 < Real.sqrt ((2*R*Real.sin (a*(δ:ℝ)/(2*(k:ℝ))))^2+(2*R*Real.sin u)^2)
  nlinarith [sq_nonneg (2*R*Real.sin (a*(δ:ℝ)/(2*(k:ℝ))))]

#print axioms epsilonLocalLength_min

/-- Source local-band ceiling for a squared digit angle at most 1/8. -/
theorem epsilonLocalLength_upper (p m k A i δ : ℕ) (a : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hp : 0 < p)
    (ha : 0 ≤ a) (hasq : a^2 ≤ 1/8)
    (hδ : 0 < δ) (hi : i+δ < k) :
    epsilonLocalLength p m k A i δ a < 144*(m:ℝ)*(k:ℝ)^2 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hd0 : (0:ℝ) < δ := by exact_mod_cast hδ
  have hdk : (δ:ℝ)+1 ≤ k := by exact_mod_cast (show δ < k by omega)
  let h : ℝ := a*(δ:ℝ)/(2*(k:ℝ))
  let u : ℝ := (epsilonRulerGap p k A i δ : ℝ)/(6*(p:ℝ)*(k:ℝ))
  let R : ℝ := 128*(m:ℝ)*(k:ℝ)^2
  have hR : 0 < R := by dsimp [R]; positivity
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh : h ≤ a/2 := by
    apply (div_le_iff₀ (show 0 < 2*(k:ℝ) by positivity)).2
    nlinarith
  have hw := epsilonRulerGap_window p k A i δ hp
  have hu0 : 0 ≤ u := by
    apply div_nonneg _ (by positivity)
    exact_mod_cast (epsilonRulerGap_pos p k A i δ hp hδ).le
  have hu : u ≤ 1/2 := by
    apply (div_le_iff₀ (show 0 < 6*(p:ℝ)*(k:ℝ) by positivity)).2
    have hhi : (epsilonRulerGap p k A i δ : ℝ) < (3*(δ:ℝ)+1)*(p:ℝ) := by
      exact_mod_cast hw.2
    nlinarith
  have hhsq : h^2 ≤ a^2/4 := by nlinarith
  have husq : u^2 ≤ 1/4 := by nlinarith
  have hsinh : (Real.sin h)^2 ≤ a^2/4 := Real.sin_sq_le_sq.trans hhsq
  have hsinu : (Real.sin u)^2 ≤ 1/4 := Real.sin_sq_le_sq.trans husq
  have h1 := mul_le_mul_of_nonneg_left hsinh (sq_nonneg (2*R))
  have h2 := mul_le_mul_of_nonneg_left hsinu (sq_nonneg (2*R))
  have h3 := mul_le_mul_of_nonneg_left hasq (sq_nonneg R)
  have hb : (2*R*Real.sin h)^2+(2*R*Real.sin u)^2 ≤ (9/8:ℝ)*R^2 := by
    nlinarith only [h1,h2,h3]
  have hr := Real.sq_sqrt (show 0 ≤ (2*R*Real.sin h)^2+(2*R*Real.sin u)^2 by positivity)
  have ht : 0 < 144*(m:ℝ)*(k:ℝ)^2 := by positivity
  have hstrict : (9/8:ℝ)*R^2 < (144*(m:ℝ)*(k:ℝ)^2)^2 := by
    have hR0 : 0 < R^2 := sq_pos_of_pos hR
    have he : (144*(m:ℝ)*(k:ℝ)^2)^2 = (81/64:ℝ)*R^2 := by dsimp [R]; ring
    rw [he]
    linarith
  change Real.sqrt ((2*R*Real.sin h)^2+(2*R*Real.sin u)^2) < _
  nlinarith

#print axioms epsilonLocalLength_upper
end EuclideanEpsilonResearch
