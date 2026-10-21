import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Ruler
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5GeometryParameters

/-! Exact local-circle length bounds for the fifth-pass parameters. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5Chord (R θ D x : ℝ) : ℝ := 2*R*Real.sin (θ*x/(2*D))

theorem hasDerivAt_pass5Chord (R θ D x : ℝ) (hD : D ≠ 0) :
    HasDerivAt (pass5Chord R θ D)
      (R*θ/D*Real.cos (θ*x/(2*D))) x := by
  have h := ((((hasDerivAt_id x).const_mul θ).div_const (2*D)).sin).const_mul (2*R)
  have he : 2*R*(Real.cos (θ*x/(2*D))*(θ*1/(2*D))) =
      R*θ/D*Real.cos (θ*x/(2*D)) := by field_simp <;> ring
  convert h using 1 <;> first | rfl | exact he.symm

theorem pass5Chord_lower_difference (R θ D a Y x y : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hD : 0 < D) (ha : 0 ≤ a)
    (hscale : θ*Y ≤ a*D) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Y) :
    (R*θ/D)*(1-a^2/8)*(y-x) ≤ pass5Chord R θ D y-pass5Chord R θ D x := by
  have hd (z : ℝ) := hasDerivAt_pass5Chord R θ D z hD.ne'
  apply (convex_Icc (0 : ℝ) Y).mul_sub_le_image_sub_of_le_deriv
    (fun z _ => (hd z).continuousAt.continuousWithinAt)
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt)
    ?_ x ⟨hx,hxy.trans hy⟩ y ⟨hx.trans hxy,hy⟩ hxy
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) Y := interior_subset hz
  have harg0 : 0 ≤ θ*z/(2*D) :=
    div_nonneg (mul_nonneg hθ.le hz'.1) (by positivity)
  have harg : θ*z/(2*D) ≤ a/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*D)).2
    nlinarith [mul_le_mul_of_nonneg_left hz'.2 hθ.le]
  have harg2 : (θ*z/(2*D))^2 ≤ a^2/4 := by nlinarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ*z/(2*D))
  have hcos' : 1-a^2/8 ≤ Real.cos (θ*z/(2*D)) := by nlinarith
  rw [(hd z).deriv]
  exact mul_le_mul_of_nonneg_left hcos' (by positivity)

theorem pass5Chord_upper (R θ D x : ℝ) (hR : 0 < R) (hθ : 0 < θ)
    (hD : 0 < D) (hx : 0 ≤ x) : pass5Chord R θ D x ≤ (R*θ/D)*x := by
  have h := Real.sin_le (show 0 ≤ θ*x/(2*D) by positivity)
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*R by positivity)
  have he : 2*R*(θ*x/(2*D)) = (R*θ/D)*x := by field_simp <;> ring
  simpa only [pass5Chord, he] using hh

noncomputable def pass5LocalLength (m k p A i δ : ℕ) : ℝ :=
  pass5Chord (pass5Radius m k) (pass5Theta k) (12*(p : ℝ))
    (pass5RulerGap 12 p k A i δ : ℝ)

theorem pass5Radius_pos (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    0 < pass5Radius m k := by unfold pass5Radius; positivity

/-- The tiny strict C5 margin is retained exactly. -/
theorem pass5_local_slope_gt_one (m k p : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) :
    1 < (pass5Radius m k * pass5Theta k / (12*(p : ℝ))) * (1-(49/100 : ℝ)^2/8) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hup : (p : ℝ) < 4*(m : ℝ)*(k : ℝ) := by exact_mod_cast hpup
  have he : (pass5Radius m k * pass5Theta k / (12*(p : ℝ))) *
      (1-(49/100 : ℝ)^2/8) =
      (384037451/8000000 : ℝ) * ((m : ℝ)*k) / (12*(p : ℝ)) := by
    unfold pass5Radius pass5Theta
    field_simp <;> ring
  rw [he]
  apply (lt_div_iff₀ (by positivity : 0 < 12*(p : ℝ))).2
  nlinarith [mul_pos hm' hk']

theorem pass5_ruler_gap_bounds (p k A i δ : ℕ) (hp : 0 < p)
    (hδ : 0 < δ) (hi : i+δ < k) :
    1 ≤ (pass5RulerGap 12 p k A i δ : ℝ) ∧
    (pass5RulerGap 12 p k A i δ : ℝ) < 12*(p : ℝ)*k := by
  have hpos := pass5RulerGap_pos 12 p k A i δ hp (by norm_num) hδ
  have h1 : (1 : ℤ) ≤ pass5RulerGap 12 p k A i δ := by omega
  have hup := (pass5RulerGap_window 12 p k A i δ hp).2
  have hup' : (pass5RulerGap 12 p k A i δ : ℝ) < (12*(δ : ℝ)+1)*p := by
    exact_mod_cast hup
  have hδ' : (δ : ℝ)+1 ≤ k := by exact_mod_cast (show δ+1 ≤ k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  exact ⟨by exact_mod_cast h1, by nlinarith⟩

/-- Every source chord increases by more than one over a real gap of at least one. -/
theorem pass5_source_chord_gap (m k p : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) (x y : ℝ)
    (hx : 0 ≤ x) (hgap : 1 ≤ y-x) (hy : y ≤ 12*(p : ℝ)*k) :
    1 < pass5Chord (pass5Radius m k) (pass5Theta k) (12*(p : ℝ)) y -
      pass5Chord (pass5Radius m k) (pass5Theta k) (12*(p : ℝ)) x := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hs : pass5Theta k * (12*(p : ℝ)*k) = (49/100 : ℝ)*(12*(p : ℝ)) := by
    unfold pass5Theta
    field_simp <;> ring
  have h := pass5Chord_lower_difference (pass5Radius m k) (pass5Theta k)
    (12*(p : ℝ)) (49/100) (12*(p : ℝ)*k) x y
    (pass5Radius_pos m k hm hk) (pass5Theta_pos k hk) (by positivity) (by norm_num)
    hs.le hx (by linarith) hy
  have hslope := pass5_local_slope_gt_one m k p hm hk hp hpup
  nlinarith

/-- Every local edge has length strictly greater than one. -/
theorem pass5LocalLength_gt_one (m k p A i δ : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) (hδ : 0 < δ) (hi : i+δ < k) :
    1 < pass5LocalLength m k p A i δ := by
  obtain ⟨hlo,hup⟩ := pass5_ruler_gap_bounds p k A i δ hp hδ hi
  have h := pass5_source_chord_gap m k p hm hk hp hpup 0
    (pass5RulerGap 12 p k A i δ : ℝ) (by norm_num) (by simpa using hlo) hup.le
  simpa [pass5LocalLength, pass5Chord] using h

/-- Source local lengths lie below the local-versus-cross guard. -/
theorem pass5LocalLength_upper (m k p A i δ : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hδ : 0 < δ) (hi : i+δ < k) :
    pass5LocalLength m k p A i δ < (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2 := by
  obtain ⟨hlo,hup⟩ := pass5_ruler_gap_bounds p k A i δ hp hδ hi
  have hR := pass5Radius_pos m k hm hk
  have hθ := pass5Theta_pos k hk
  have hD : 0 < 12*(p : ℝ) := by positivity
  have h := pass5Chord_upper (pass5Radius m k) (pass5Theta k) (12*(p : ℝ))
    (pass5RulerGap 12 p k A i δ : ℝ) hR hθ hD (by linarith)
  have hh := mul_lt_mul_of_pos_left hup (show 0 < pass5Radius m k*pass5Theta k/(12*(p : ℝ)) by positivity)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have he : (pass5Radius m k*pass5Theta k/(12*(p : ℝ))) * (12*(p : ℝ)*k) =
      (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2 := by
    unfold pass5Radius pass5Theta
    field_simp <;> ring
  rw [he] at hh
  exact h.trans_lt hh

/-- Local/local separation across all clusters, using actual prime-ruler uniqueness. -/
theorem pass5LocalLength_separated (m k p A B i j δ ε : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hp : p.Prime)
    (hsize : 2*m*k < p) (hpup : p < 4*m*k)
    (hA : A < m) (hB : B < m) (hδ : 0 < δ) (hε : 0 < ε)
    (hδp : δ < p) (hεp : ε < p) (hi : i+δ < k) (hj : j+ε < k)
    (hne : ¬ (A=B ∧ i=j ∧ δ=ε)) :
    1 < |pass5LocalLength m k p A i δ-pass5LocalLength m k p B j ε| := by
  have hneq : pass5RulerGap 12 p k A i δ ≠ pass5RulerGap 12 p k B j ε := by
    intro he
    exact hne (pass5RulerGap_injective 12 p m k δ ε A B i j hp (by norm_num)
      hδ hε hδp hεp hsize hA hB hi hj he)
  obtain ⟨hlo1,hup1⟩ := pass5_ruler_gap_bounds p k A i δ hp.pos hδ hi
  obtain ⟨hlo2,hup2⟩ := pass5_ruler_gap_bounds p k B j ε hp.pos hε hj
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hd : (1 : ℤ) ≤ pass5RulerGap 12 p k B j ε-pass5RulerGap 12 p k A i δ := by omega
    have hd' : (1 : ℝ) ≤ (pass5RulerGap 12 p k B j ε : ℝ)-
        (pass5RulerGap 12 p k A i δ : ℝ) := by exact_mod_cast hd
    have h := pass5_source_chord_gap m k p hm hk hp.pos hpup _ _ (by linarith) hd' hup2.le
    change 1 < pass5LocalLength m k p B j ε-pass5LocalLength m k p A i δ at h
    have hh := le_abs_self (pass5LocalLength m k p B j ε-pass5LocalLength m k p A i δ)
    rw [abs_sub_comm] at hh
    exact h.trans_le hh
  · have hd : (1 : ℤ) ≤ pass5RulerGap 12 p k A i δ-pass5RulerGap 12 p k B j ε := by omega
    have hd' : (1 : ℝ) ≤ (pass5RulerGap 12 p k A i δ : ℝ)-
        (pass5RulerGap 12 p k B j ε : ℝ) := by exact_mod_cast hd
    have h := pass5_source_chord_gap m k p hm hk hp.pos hpup _ _ (by linarith) hd' hup1.le
    exact h.trans_le (le_abs_self _)


/-- The actual source angle on each circle. -/
noncomputable def pass5Angle (p k A i : ℕ) : ℝ :=
  pass5Theta k * (pass5Raw 12 p k A i-pass5H k)

theorem pass5Angle_sine (p k A i : ℕ) (hk : 0 < k) :
    Real.sin (pass5Angle p k A i) = pass5Theta k*pass5Digit p k A i := by
  have hθ := (pass5Theta_pos k hk).ne'
  unfold pass5Angle pass5Digit sineDigit
  field_simp

theorem pass5Angle_difference (p k A i δ : ℕ) :
    (pass5Angle p k A (i+δ)-pass5Angle p k A i)/2 =
      pass5Theta k*(pass5RulerGap 12 p k A i δ : ℝ)/(2*(12*(p : ℝ))) := by
  unfold pass5Angle pass5Raw pass5RulerGap
  push_cast
  ring

/-- The positive local chord agrees with the absolute-sine distance identity
returned by the Euclidean circle geometry module. -/
theorem pass5LocalLength_eq_abs_chord (m k p A i δ : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hp : 0 < p) (hpup : p < 4*m*k)
    (hδ : 0 < δ) (hi : i+δ < k) :
    2*pass5Radius m k*|Real.sin ((pass5Angle p k A (i+δ)-pass5Angle p k A i)/2)| =
      pass5LocalLength m k p A i δ := by
  have hmin := pass5LocalLength_gt_one m k p A i δ hm hk hp hpup hδ hi
  have hR := pass5Radius_pos m k hm hk
  have hsin : 0 < Real.sin (pass5Theta k*(pass5RulerGap 12 p k A i δ : ℝ)/(2*(12*(p : ℝ)))) := by
    apply (mul_pos_iff_of_pos_left (show 0 < 2*pass5Radius m k by positivity)).1
    exact lt_trans zero_lt_one hmin
  rw [pass5Angle_difference, abs_of_pos hsin]
  rfl

end Erdos488.Geometry.SeparatedDistances.FixedDimension
