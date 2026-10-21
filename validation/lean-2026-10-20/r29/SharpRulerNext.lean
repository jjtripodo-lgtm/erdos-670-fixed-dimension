import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Ruler

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Prime cancellation needs p > m*k, with the odd prime condition explicit. -/
theorem same_lag_residue_injective_sharp
    (p m k δ A B i j : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hδ : 0 < δ) (hδp : δ < p) (hsize : m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p) :
    A = B ∧ i = j := by
  have hcop : p.Coprime δ := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hδ hδp)
  have hmod : 2*i+δ+2*k*A ≡ 2*j+δ+2*k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hcop heq
  have hmod' : 2*(i+k*A)+δ ≡ 2*(j+k*B)+δ [MOD p] := by
    have hleft : 2*(i+k*A)+δ = 2*i+δ+2*k*A := by ring
    have hright : 2*(j+k*B)+δ = 2*j+δ+2*k*B := by ring
    simpa only [hleft, hright] using hmod
  have htwo : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) hp2)
  have hs : i+k*A ≡ j+k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime htwo (Nat.ModEq.add_right_cancel' δ hmod')
  have hleft : i+k*A < p := by
    have hh := Nat.mul_le_mul_left k (show A+1 ≤ m by omega)
    nlinarith
  have hright : j+k*B < p := by
    have hh := Nat.mul_le_mul_left k (show B+1 ≤ m by omega)
    nlinarith
  have he := hs.eq_of_lt_of_lt hleft hright
  have hab : A = B := by
    rcases lt_trichotomy A B with h | h | h
    · have hh := Nat.mul_le_mul_left k (show A+1 ≤ B by omega)
      nlinarith
    · exact h
    · have hh := Nat.mul_le_mul_left k (show B+1 ≤ A by omega)
      nlinarith
  exact ⟨hab, by subst B; omega⟩

/-- The actual integer gaps inherit the sharp prime-size condition. -/
theorem rulerGap_same_lag_injective_sharp (L p m k δ A B i j : ℕ)
    (hp : p.Prime) (hp2 : 2 < p) (hδ : 0 < δ) (hδp : δ < p)
    (hsize : m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+δ < k)
    (heq : pass5RulerGap L p k A i δ = pass5RulerGap L p k B j δ) :
    A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [pass5RulerGap_residue, pass5RulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective_sharp p m k δ A B i j hp hp2 hδ hδp hsize
    hA hB hi hj hnat

#print axioms same_lag_residue_injective_sharp
#print axioms rulerGap_same_lag_injective_sharp
end Erdos488.Geometry.SeparatedDistances.FixedDimension
