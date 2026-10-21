import Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRuler
import Erdos488.Geometry.SeparatedDistances.FixedDimension.SineDigits

/-! Exact integer-ruler layer. Unlike a residue-only statement, these theorems
refer to the actual differences of the explicit ruler positions. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The fifth-pass ruler, with the linear spacing parameter L explicit. -/
def pass5Ruler (L p k A i : ℕ) : ℤ :=
  (L : ℤ) * (p : ℤ) * (i : ℤ) + ((i^2 + 2*k*A*i) % p : ℕ)

/-- A positive-lag difference, kept in the integers so subtraction never truncates. -/
def pass5RulerGap (L p k A i δ : ℕ) : ℤ :=
  pass5Ruler L p k A (i + δ) - pass5Ruler L p k A i

/-- Every actual ruler difference lies in its strict lag window. -/
theorem pass5RulerGap_window (L p k A i δ : ℕ) (hp : 0 < p) :
    ((L : ℤ) * (δ : ℤ) - 1) * p < pass5RulerGap L p k A i δ ∧
      pass5RulerGap L p k A i δ < ((L : ℤ) * (δ : ℤ) + 1) * p := by
  have h₀ : (0 : ℤ) ≤ ((i^2 + 2*k*A*i) % p : ℕ) := by positivity
  have h₁ : (0 : ℤ) ≤ (((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) := by positivity
  have h₂ : (((i^2 + 2*k*A*i) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  have h₃ : ((((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  dsimp [pass5RulerGap, pass5Ruler]
  push_cast at *
  constructor <;> nlinarith

/-- Strictly positive lags give positive actual ruler gaps. -/
theorem pass5RulerGap_pos (L p k A i δ : ℕ) (hp : 0 < p) (hL : 2 ≤ L) (hδ : 0 < δ) :
    0 < pass5RulerGap L p k A i δ := by
  have hw := (pass5RulerGap_window L p k A i δ hp).1
  have hδ' : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hL' : (2 : ℤ) ≤ L := by exact_mod_cast hL
  nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ L-2) (by omega : (0 : ℤ) ≤ δ)]

/-- Different lag windows are strictly ordered for every L ≥ 2. -/
theorem pass5RulerGap_different_lag (L p k A B i j δ ε : ℕ)
    (hp : 0 < p) (hL : 2 ≤ L) (hδε : δ < ε) :
    0 < pass5RulerGap L p k B j ε - pass5RulerGap L p k A i δ := by
  have h₀ := (pass5RulerGap_window L p k A i δ hp).2
  have h₁ := (pass5RulerGap_window L p k B j ε hp).1
  have hδε' : (δ : ℤ) + 1 ≤ ε := by exact_mod_cast hδε
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hL' : (2 : ℤ) ≤ L := by exact_mod_cast hL
  have hd : (L : ℤ) * δ + 2 ≤ (L : ℤ) * ε := by
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ L) (by omega : (0 : ℤ) ≤ ε-δ-1)]
  nlinarith

/-- The actual ruler difference has exactly the stated quadratic residue. -/
theorem pass5RulerGap_residue (L p k A i δ : ℕ) :
    pass5RulerGap L p k A i δ % (p : ℤ) =
      ((δ * (2*i + δ + 2*k*A) : ℕ) : ℤ) % (p : ℤ) := by
  have hpoly : (((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
      ((i^2 + 2*k*A*i : ℕ) : ℤ) = ((δ*(2*i+δ+2*k*A) : ℕ) : ℤ) := by
    push_cast
    ring
  calc
    pass5RulerGap L p k A i δ % (p : ℤ) =
        ((((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
          ((i^2 + 2*k*A*i : ℕ) : ℤ)) % (p : ℤ) := by
      simp [pass5RulerGap, pass5Ruler, Int.add_emod, Int.sub_emod,
        Int.mul_emod, Int.natCast_emod]
    _ = _ := congrArg (fun z : ℤ => z % (p : ℤ)) hpoly

/-- Equal same-lag *actual* gaps force the same cluster and starting index. -/
theorem pass5RulerGap_same_lag_injective (L p m k δ A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hδp : δ < p) (hsize : 2*m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : pass5RulerGap L p k A i δ = pass5RulerGap L p k B j δ) : A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [pass5RulerGap_residue, pass5RulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective p m k δ A B i j hp hδ hδp hsize hA hB hi hj hnat

/-- Exhaustive uniqueness of all positive actual ruler gaps, across all clusters.
Different lags use disjoint windows; equal lags use prime cancellation. -/
theorem pass5RulerGap_injective (L p m k δ ε A B i j : ℕ)
    (hp : p.Prime) (hL : 2 ≤ L) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k)
    (heq : pass5RulerGap L p k A i δ = pass5RulerGap L p k B j ε) :
    A = B ∧ i = j ∧ δ = ε := by
  have hδε : δ = ε := by
    rcases lt_trichotomy δ ε with hlt | he | hgt
    · have h := pass5RulerGap_different_lag L p k A B i j δ ε hp.pos hL hlt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
    · exact he
    · have h := pass5RulerGap_different_lag L p k B A j i ε δ hp.pos hL hgt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
  subst ε
  obtain ⟨hAB,hij⟩ := pass5RulerGap_same_lag_injective L p m k δ A B i j
    hp hδ hδp hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩



/-- The uncentered normalized ruler coordinate. -/
noncomputable def pass5Raw (L p k A i : ℕ) : ℝ :=
  (pass5Ruler L p k A i : ℝ) / ((L : ℝ) * p)

/-- Every normalized coordinate lies in the same short interval. -/
theorem pass5Raw_bounds (L p k A i : ℕ) (hL : 2 ≤ L) (hp : 0 < p) (hi : i < k) :
    0 ≤ pass5Raw L p k A i ∧ pass5Raw L p k A i < (k : ℝ) - (1 - 1/(L : ℝ)) := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hi' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
  have hr0 : (0 : ℝ) ≤ ((i^2+2*k*A*i)%p : ℕ) := by positivity
  have hr1 : (((i^2+2*k*A*i)%p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt _ hp
  have hd : 0 < (L : ℝ)*p := by positivity
  unfold pass5Raw pass5Ruler
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  constructor
  · positivity
  · apply (div_lt_iff₀ hd).2
    have hLi : (L : ℝ)*(i+1) ≤ (L : ℝ)*k :=
      mul_le_mul_of_nonneg_left hi' (by positivity)
    have hLip := mul_le_mul_of_nonneg_right hLi hp'.le
    have he : ((k : ℝ)-(1-1/(L : ℝ)))*((L : ℝ)*p) =
        (L : ℝ)*p*(k-1)+p := by field_simp <;> ring
    rw [he]
    nlinarith

/-- The exact raw adjacent step exceeds kappa=1−1/L. -/
theorem pass5Raw_step (L p k A i : ℕ) (hL : 2 ≤ L) (hp : 0 < p) :
    1-1/(L : ℝ) < pass5Raw L p k A (i+1)-pass5Raw L p k A i := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hd : 0 < (L : ℝ)*p := by positivity
  have hw := (pass5RulerGap_window L p k A i 1 hp).1
  norm_num only [Nat.cast_one, mul_one] at hw
  have hw' : ((L : ℝ)-1)*p < (pass5RulerGap L p k A i 1 : ℝ) := by
    exact_mod_cast hw
  have he : pass5Raw L p k A (i+1)-pass5Raw L p k A i =
      (pass5RulerGap L p k A i 1 : ℝ) / ((L : ℝ)*p) := by
    unfold pass5Raw pass5RulerGap
    push_cast
    ring
  rw [he]
  apply (lt_div_iff₀ hd).2
  have he' : (1-1/(L : ℝ))*((L : ℝ)*p)=((L : ℝ)-1)*p := by field_simp <;> ring
  rw [he']
  exact hw'

/-- Centering the ruler gives the paper's position and angular envelope. -/
theorem pass5_position_bounds (L p k A i : ℕ) (hL : 2 ≤ L) (hp : 0 < p)
    (hi : i < k) :
    |pass5Raw L p k A i - ((k : ℝ)-(1-1/(L : ℝ)))/2| ≤
      ((k : ℝ)-(1-1/(L : ℝ)))/2 ∧
    ((k : ℝ)-(1-1/(L : ℝ)))/2 < (k : ℝ)/2 := by
  obtain ⟨h0,h1⟩ := pass5Raw_bounds L p k A i hL hp hi
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hrec : 1/(L : ℝ) ≤ (1/2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hL'
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩

/-- A generic sine-digit lower step on the paper's small-angle interval.
All premises are explicit raw-coordinate bounds, so this can be instantiated
with the normalized clustered ruler without any approximation axiom. -/
theorem pass5_sine_digit_step (a k h κ x y : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hk : 0 < k) (hh : 0 ≤ h) (hhk : h ≤ k/2)
    (hκ : 0 ≤ κ) (hx : 0 ≤ x) (hy : y ≤ 2*h) (hgap : κ < y-x) :
    κ*(1-a^2/8) < sineDigit (a/k) h y - sineDigit (a/k) h x := by
  have hθ : 0 < a/k := div_pos ha hk
  have hxy : x ≤ y := by linarith
  have hbase := sineDigit_lower_difference (a/k) h x y hθ hx hxy hy
  have harg : (a/k)*h ≤ a/2 := by
    have he : (a/k)*h = (a*h)/k := by ring
    rw [he]
    apply (div_le_iff₀ hk).2
    nlinarith [mul_le_mul_of_nonneg_left hhk ha.le]
  have harg0 : 0 ≤ (a/k)*h := mul_nonneg hθ.le hh
  have hs : ((a/k)*h)^2 ≤ a^2/4 := by nlinarith
  have hγ : 0 < 1-a^2/8 := by nlinarith
  have hmul := mul_nonneg (show 0 ≤ (1-((a/k)*h)^2/2)-(1-a^2/8) by nlinarith)
    (show 0 ≤ y-x by linarith)
  have hstrict := mul_lt_mul_of_pos_right hgap hγ
  nlinarith


noncomputable def pass5H (k : ℕ) : ℝ := ((k : ℝ)-(1-1/(12 : ℝ)))/2
noncomputable def pass5Theta (k : ℕ) : ℝ := (49/100 : ℝ)/(k : ℝ)
noncomputable def pass5Digit (p k A i : ℕ) : ℝ :=
  sineDigit (pass5Theta k) (pass5H k) (pass5Raw 12 p k A i)

theorem pass5H_pos (k : ℕ) (hk : 2 ≤ k) : 0 < pass5H k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  unfold pass5H
  linarith

theorem pass5Theta_pos (k : ℕ) (hk : 0 < k) : 0 < pass5Theta k := by
  unfold pass5Theta
  positivity

theorem pass5Digit_abs_le (p k A i : ℕ) (hp : 0 < p) (hi : i < k) :
    |pass5Digit p k A i| ≤ pass5H k := by
  obtain ⟨h0,h1⟩ := pass5Raw_bounds 12 p k A i (by norm_num) hp hi
  apply sineDigit_centered_bound _ _ _ (pass5Theta_pos k (by omega)) h0
  unfold pass5H
  linarith

theorem pass5Digit_step (p k A i : ℕ) (hp : 0 < p) (hi : i+1 < k) :
    (853589/960000 : ℝ) < pass5Digit p k A (i+1)-pass5Digit p k A i := by
  have hk : 2 ≤ k := by omega
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨hx0,hx1⟩ := pass5Raw_bounds 12 p k A i (by norm_num) hp (by omega)
  obtain ⟨hy0,hy1⟩ := pass5Raw_bounds 12 p k A (i+1) (by norm_num) hp hi
  have hgap := pass5Raw_step 12 p k A i (by norm_num) hp
  have hh0 := (pass5H_pos k hk).le
  have hh1 : pass5H k ≤ (k : ℝ)/2 := by unfold pass5H; linarith
  have hy : pass5Raw 12 p k A (i+1) ≤ 2*pass5H k := by unfold pass5H; linarith
  have h := pass5_sine_digit_step (49/100) (k : ℝ) (pass5H k) (1-1/12)
    (pass5Raw 12 p k A i) (pass5Raw 12 p k A (i+1))
    (by norm_num) (by norm_num) hk' hh0 hh1 (by norm_num) hx0 hy hgap
  norm_num only [show (1-1/(12 : ℝ))*(1-(49/100 : ℝ)^2/8) = 853589/960000 by norm_num] at h
  exact h

/-- The upper sine derivative never exceeds one. -/
theorem pass5_sineDigit_upper_difference (θ h x y : ℝ) (hθ : θ ≠ 0) (hxy : x ≤ y) :
    sineDigit θ h y-sineDigit θ h x ≤ y-x := by
  have hd (z : ℝ) := hasDerivAt_sineDigit θ h z hθ
  have hh := image_sub_le_mul_sub_of_deriv_le (fun z => (hd z).differentiableAt)
    (fun z => by rw [(hd z).deriv]; exact Real.cos_le_one _) hxy
  simpa using hh

theorem pass5Digit_span (p k A : ℕ) (hp : 0 < p) (hk : 2 ≤ k) :
    pass5Digit p k A (k-1)-pass5Digit p k A 0 < (k : ℝ)-11/12 := by
  have hx : pass5Raw 12 p k A 0 = 0 := by simp [pass5Raw, pass5Ruler]
  obtain ⟨hy0,hy1⟩ := pass5Raw_bounds 12 p k A (k-1) (by norm_num) hp (by omega)
  have hxy : pass5Raw 12 p k A 0 ≤ pass5Raw 12 p k A (k-1) := by rw [hx]; exact hy0
  have h := pass5_sineDigit_upper_difference (pass5Theta k) (pass5H k)
    (pass5Raw 12 p k A 0) (pass5Raw 12 p k A (k-1))
    (pass5Theta_pos k (by omega)).ne' hxy
  unfold pass5Digit
  rw [hx] at h ⊢
  linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
