import CrossParameters
import StrictCrossSeparation
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5ActualCrossSeparation

namespace Erdos670EpsilonFamily
open Erdos488.Geometry.SeparatedDistances
open Erdos488.Geometry.SeparatedDistances.FixedDimension
open EuclideanEpsilonResearch

theorem epsilon_scale_pos (ξ : ℝ) (k : ℕ) (hξ : 0 < ξ) (hk : 2 ≤ k) :
    0 < epsilonScale ξ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold epsilonScale
  positivity

noncomputable def epsilonColexBaseline {m : ℕ} (ξ : ℝ) (k : ℕ) (K : ℝ) (A B : Fin m) : ℝ :=
  epsilonScale ξ k * Pass5.circleColexDistance K A B

theorem epsilonColexBaseline_eq {m : ℕ} (ξ : ℝ) (k : ℕ) (K : ℝ) (A B : Fin m)
    (hAB : A.val < B.val) :
    epsilonColexBaseline ξ k K A B = epsilonScale ξ k*(K+(pass5PairCode A B : ℝ)+1) := by
  simp [epsilonColexBaseline, Pass5.circleColexDistance, hAB, pass5PairCode,
    colexLabel, Nat.cast_add, add_assoc]

theorem epsilonColexBaseline_lower {m k : ℕ} (ξ : ℝ) (hξ : 0 < ξ) (hk : 2 ≤ k) (K : ℝ) (A B : Fin m)
    (hAB : A.val < B.val) :
    epsilonScale ξ k*(K+1) ≤ epsilonColexBaseline ξ k K A B := by
  rw [epsilonColexBaseline_eq ξ k K A B hAB]
  apply mul_le_mul_of_nonneg_left _ (epsilon_scale_pos ξ k hξ hk).le
  have : (0 : ℝ) ≤ (pass5PairCode A B : ℝ) := by positivity
  linarith

theorem epsilonColexBaseline_upper {m k : ℕ} (ξ : ℝ) (hξ : 0 < ξ) (hk : 2 ≤ k) (K : ℝ) (A B : Fin m)
    (hAB : A.val < B.val) :
    epsilonColexBaseline ξ k K A B ≤ epsilonScale ξ k*(K+(m.choose 2 : ℝ)) := by
  rw [epsilonColexBaseline_eq ξ k K A B hAB]
  apply mul_le_mul_of_nonneg_left _ (epsilon_scale_pos ξ k hξ hk).le
  have hh : (pass5PairCode A B : ℝ)+1 ≤ (m.choose 2 : ℝ) := by
    exact_mod_cast pass5PairCode_lt_choose A B hAB
  linarith

theorem epsilonColexBaseline_pos {m k : ℕ} (ξ : ℝ) (hξ : 0 < ξ) (hk : 2 ≤ k) (K : ℝ) (hK : 0 ≤ K)
    (A B : Fin m) (hAB : A.val < B.val) : 0 < epsilonColexBaseline ξ k K A B := by
  have h := epsilonColexBaseline_lower ξ hξ hk K A B hAB
  have hp : 0 < epsilonScale ξ k*(K+1) := mul_pos (epsilon_scale_pos ξ k hξ hk) (by linarith)
  linarith

theorem epsilonColexBaseline_separated {m k : ℕ} (ξ : ℝ) (hξ : 0 < ξ) (hk : 2 ≤ k) (K : ℝ)
    (A B C D : Fin m) (hAB : A.val < B.val) (hCD : C.val < D.val)
    (hne : (A,B) ≠ (C,D)) :
    epsilonScale ξ k ≤ |epsilonColexBaseline ξ k K A B-epsilonColexBaseline ξ k K C D| := by
  rw [epsilonColexBaseline_eq ξ k K A B hAB, epsilonColexBaseline_eq ξ k K C D hCD]
  apply pass5_integer_baselines_separated _ _ _ _ (epsilon_scale_pos ξ k hξ hk).le
  intro hh
  obtain ⟨rfl,rfl⟩ := pass5PairCode_ordered_injective A B C D hAB hCD hh
  exact hne rfl


noncomputable def epsilonDigit (ξ : ℝ) (k : ℕ) (i : ℕ) : ℝ :=
  sineDigit (Real.sqrt ξ/(k : ℝ)) (((k : ℝ)-1)/2) i

noncomputable def epsilonCrossLength {m : ℕ} (ξ : ℝ) (k : ℕ)
    (A B : Fin m) (i j : ℕ) : ℝ :=
  pass5Phi (epsilonColexBaseline ξ k (epsilonOffset ξ m) A B)
    (pass5CrossDigit (1+ξ) k (epsilonDigit ξ k) (epsilonDigit ξ k) i j)

/-- All distinct ordered cross edges, with every scalar guard discharged. -/
theorem epsilon_cross_pairs_strict {m k : ℕ} (ξ : ℝ)
    (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k)
    (A B C D : Fin m) (hAB : A.val < B.val) (hCD : C.val < D.val)
    (i j u v : Fin k) (hne : (A,B,i,j) ≠ (C,D,u,v)) :
    1 < |epsilonCrossLength ξ k A B i.val j.val-epsilonCrossLength ξ k C D u.val v.val| := by
  obtain ⟨ht,ht1,hg,hfine,hcarry,hmacro⟩ := epsilon_cross_guards ξ m k hξ hξsmall hm hk
  obtain ⟨hf,hfstep⟩ := uniform_sine_digits ξ k hξ hk
  have hK : 0 ≤ epsilonOffset ξ m := by unfold epsilonOffset; positivity
  have hν := epsilonColexBaseline_pos ξ hξ hk (epsilonOffset ξ m) hK A B hAB
  have hμ := epsilonColexBaseline_pos ξ hξ hk (epsilonOffset ξ m) hK C D hCD
  have hbν := epsilon_digit_domain ξ m k hξ hξsmall hm hk _
    (epsilonColexBaseline_lower ξ hξ hk (epsilonOffset ξ m) A B hAB)
  have hbμ := epsilon_digit_domain ξ m k hξ hξsmall hm hk _
    (epsilonColexBaseline_lower ξ hξ hk (epsilonOffset ξ m) C D hCD)
  apply pass5_cross_pairs_separated_strict (fun _ : Fin m => epsilonDigit ξ k)
    (epsilonColexBaseline ξ k (epsilonOffset ξ m)) (1+ξ) (epsilonTau ξ m)
    (epsilonHalfSpan k) (1-ξ/8) (epsilonScale ξ k) k
    (by omega) (by linarith) ht ht1 hg (fun _ => hf) (fun _ i hi => by simpa [epsilonDigit] using hfstep i hi)
    hfine hcarry hmacro A B C D hν hμ hbν hbμ
    (epsilonColexBaseline_separated ξ hξ hk _ A B C D hAB hCD) i.isLt j.isLt u.isLt v.isLt
  intro heq
  apply hne
  have hA : A=C := congrArg Prod.fst heq
  have hB : B=D := congrArg (fun q => q.2.1) heq
  have hi : i.val=u.val := congrArg (fun q => q.2.2.1) heq
  have hj : j.val=v.val := congrArg (fun q => q.2.2.2) heq
  simp only [hA,hB,Fin.ext hi,Fin.ext hj]

#print axioms epsilon_cross_pairs_strict
end Erdos670EpsilonFamily
