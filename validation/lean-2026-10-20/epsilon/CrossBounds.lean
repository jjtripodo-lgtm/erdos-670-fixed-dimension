import CrossSpectrum

namespace Erdos670EpsilonFamily
open Erdos488.Geometry.SeparatedDistances.FixedDimension

theorem epsilonCrossLength_displacement {m k : ℕ} (ξ : ℝ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k)
    (A B : Fin m) (hAB : A.val < B.val) (i j : ℕ) (hi : i < k) (hj : j < k) :
    |epsilonCrossLength ξ k A B i j-epsilonColexBaseline ξ k (epsilonOffset ξ m) A B| ≤
      epsilonDigitBudget ξ k/epsilonTau ξ m := by
  obtain ⟨ht,ht1,_,_,_,_⟩ := epsilon_cross_guards ξ m k hξ hξsmall hm hk
  obtain ⟨hf,_⟩ := uniform_sine_digits ξ k hξ hk
  have hK : 0 ≤ epsilonOffset ξ m := by unfold epsilonOffset; positivity
  have hb := pass5CrossDigit_bound (1+ξ) (epsilonHalfSpan k) k
    (epsilonDigit ξ k) (epsilonDigit ξ k) i j (by linarith) (hf i hi) (hf j hj)
  exact pass5Phi_displacement _ _ _ _
    (epsilonColexBaseline_pos ξ hξ hk _ hK A B hAB) ht ht1 hb
    (epsilon_digit_domain ξ m k hξ hξsmall hm hk _
      (epsilonColexBaseline_lower ξ hξ hk _ A B hAB))

theorem epsilonCrossLength_lower {m k : ℕ} (ξ : ℝ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k)
    (A B : Fin m) (hAB : A.val < B.val) (i j : ℕ) (hi : i < k) (hj : j < k) :
    epsilonScale ξ k*epsilonOffset ξ m+1 < epsilonCrossLength ξ k A B i j := by
  have hd := (abs_le.mp (epsilonCrossLength_displacement ξ hξ hξsmall hm hk A B hAB i j hi hj)).1
  have hn := epsilonColexBaseline_lower ξ hξ hk (epsilonOffset ξ m) A B hAB
  obtain ⟨ht,_,_,_,_,hmacro⟩ := epsilon_cross_guards ξ m k hξ hξsmall hm hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hspan : (0 : ℝ) ≤ (k : ℝ)-1 := by linarith
  have hH : 0 ≤ epsilonDigitBudget ξ k := by
    unfold epsilonDigitBudget pass5DigitBudget epsilonHalfSpan
    positivity
  have hdiv := div_nonneg hH ht.le
  rw [show 2*epsilonDigitBudget ξ k/epsilonTau ξ m =
    2*(epsilonDigitBudget ξ k/epsilonTau ξ m) by ring] at hmacro
  nlinarith only [hd,hn,hmacro,hdiv]

theorem epsilonCrossLength_upper {m k : ℕ} (ξ : ℝ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k)
    (A B : Fin m) (hAB : A.val < B.val) (i j : ℕ) (hi : i < k) (hj : j < k) :
    epsilonCrossLength ξ k A B i j ≤
      epsilonScale ξ k*(epsilonOffset ξ m+(m.choose 2 : ℝ))+
        epsilonDigitBudget ξ k/epsilonTau ξ m := by
  have hd := (abs_le.mp (epsilonCrossLength_displacement ξ hξ hξsmall hm hk A B hAB i j hi hj)).2
  have hn := epsilonColexBaseline_upper ξ hξ hk (epsilonOffset ξ m) A B hAB
  linarith

#print axioms epsilonCrossLength_lower
#print axioms epsilonCrossLength_upper
end Erdos670EpsilonFamily
