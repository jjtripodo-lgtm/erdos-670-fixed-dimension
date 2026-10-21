import ActualGeometry
import DiameterCoefficient
import ExactNEmbedding
import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourcePrime

namespace Erdos670EpsilonFamily
open Erdos488.Geometry.SeparatedDistances
open Erdos488.Geometry.SeparatedDistances.FixedDimension
open EuclideanEpsilonResearch

/-- All local, cross and mixed edge classes refer to the same actual metric. -/
theorem epsilon_metric_properties {m k p : ℕ} {E : Type*} [PseudoMetricSpace E]
    (ξ : ℝ) (hξ : 0 < ξ) (hξsmall : ξ ≤ 1/8) (hm : 1024/ξ ≤ (m : ℝ)) (hk : 2 ≤ k)
    (hp : p.Prime) (hsize : 2*m*k < p) (hpmax : p < 4*m*k)
    (P : Fin m × Fin k → E)
    (hlocal : ∀ (A : Fin m) (i j : Fin k), i < j →
      dist (P (A,i)) (P (A,j)) =
        epsilonLocalLength p m k A.val i.val (j.val-i.val) (Real.sqrt ξ))
    (hcross : ∀ (A B : Fin m), A < B → ∀ (i j : Fin k),
      dist (P (A,i)) (P (B,j)) = epsilonCrossLength ξ k A B i.val j.val) :
    (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
    StrictSeparatedConfiguration P ∧
    (∀ a b, dist (P a) (P b) ≤ (1/2+4*ξ)*((m : ℝ)*(k : ℝ))^2) := by
  obtain ⟨hm8192,_,_⟩ := epsilon_parameter_bounds ξ m hξ hξsmall hm
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hm' : (8192 : ℝ) ≤ m := by exact_mod_cast hm8192
  have ha0 : 0 ≤ Real.sqrt ξ := Real.sqrt_nonneg _
  have ha2 : (Real.sqrt ξ)^2 = ξ := Real.sq_sqrt hξ.le
  have ha1 : Real.sqrt ξ ≤ 1 := by nlinarith
  have localMin (A : Fin m) (i j : Fin k) (hij : i < j) :
      1 ≤ dist (P (A,i)) (P (A,j)) := by
    rw [hlocal A i j hij]
    exact (epsilonLocalLength_min p m k A.val i.val (j.val-i.val) (Real.sqrt ξ)
      hm0 hk0 hp.pos (by exact Nat.sub_pos_of_lt hij) (by omega)).le
  have localUpper (A : Fin m) (i j : Fin k) (hij : i < j) :
      dist (P (A,i)) (P (A,j)) < 144*(m : ℝ)*(k : ℝ)^2 := by
    rw [hlocal A i j hij]
    exact epsilonLocalLength_upper p m k A.val i.val (j.val-i.val) (Real.sqrt ξ)
      hm0 hk0 hp.pos ha0 (by rw [ha2]; exact hξsmall) (by exact Nat.sub_pos_of_lt hij) (by omega)
  have crossLower (A B : Fin m) (hAB : A < B) (i j : Fin k) :
      1024*(m : ℝ)*(k : ℝ)^2+1 < dist (P (A,i)) (P (B,j)) := by
    rw [hcross A B hAB i j]
    have h := epsilonCrossLength_lower ξ hξ hξsmall hm hk A B hAB i.val j.val i.isLt j.isLt
    have hc := epsilon_cross_center_lower ξ m k hξ hξsmall hm
    linarith
  have crossMin (A B : Fin m) (i j : Fin k) (hAB : A < B) :
      1 ≤ dist (P (A,i)) (P (B,j)) := by
    have h := crossLower A B hAB i j
    have hn : 0 ≤ 1024*(m : ℝ)*(k : ℝ)^2 := by positivity
    linarith
  have hmin := cluster_minimum_distance P localMin crossMin
  have hsep : StrictSeparatedConfiguration P := by
    apply strictSeparatedConfiguration_of_cluster_gaps P
    · intro A i j B u v hij huv hne
      rw [hlocal A i j hij, hlocal B u v huv]
      have h := epsilonLocalLength_separated p m k A.val B.val i.val u.val
        (j.val-i.val) (v.val-u.val) (Real.sqrt ξ) hp hm0 hk0 ha0 ha1
        (by exact Nat.sub_pos_of_lt hij) (by exact Nat.sub_pos_of_lt huv)
        (by omega) (by omega) hsize hpmax A.isLt B.isLt ?_
      · linarith
      · rintro ⟨hA,hi,hgap⟩
        have hAe : A=B := Fin.ext hA
        have hie : i=u := Fin.ext hi
        have hje : j=v := Fin.ext (by omega)
        exact hne (by simp only [hAe,hie,hje])
    · intro A B i j C D u v hAB hCD hne
      rw [hcross A B hAB i j, hcross C D hCD u v]
      exact epsilon_cross_pairs_strict ξ hξ hξsmall hm hk A B C D hAB hCD i j u v hne
    · intro A i j B C u v hij hBC
      have hl := localUpper A i j hij
      have hc := crossLower B C hBC u v
      have hmkn : 0 ≤ (m : ℝ)*(k : ℝ)^2 := by positivity
      nlinarith only [hl,hc,hmkn]
  have localDiam (A : Fin m) (i j : Fin k) (hij : i < j) :
      dist (P (A,i)) (P (A,j)) ≤ (1/2+4*ξ)*((m : ℝ)*(k : ℝ))^2 := by
    have hl := localUpper A i j hij
    have hsmall : 144*(m : ℝ) ≤ (m : ℝ)^2/2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (k : ℝ))
    have hnonneg : 0 ≤ 4*ξ*((m : ℝ)*(k : ℝ))^2 := by positivity
    nlinarith only [hl,hmul,hnonneg]
  have crossDiam (A B : Fin m) (hAB : A < B) (i j : Fin k) :
      dist (P (A,i)) (P (B,j)) ≤ (1/2+4*ξ)*((m : ℝ)*(k : ℝ))^2 := by
    rw [hcross A B hAB i j]
    exact epsilon_cross_diameter_bound ξ hξ hξsmall hm hk A B hAB i.val j.val i.isLt j.isLt
  refine ⟨hmin,hsep,?_⟩
  rintro ⟨A,i⟩ ⟨B,j⟩
  rcases lt_trichotomy A B with hAB | hAB | hBA
  · exact crossDiam A B hAB i j
  · subst B
    rcases lt_trichotomy i j with hij | hij | hji
    · exact localDiam A i j hij
    · subst j
      rw [dist_self]
      positivity
    · simpa only [dist_comm] using localDiam A j i hji
  · simpa only [dist_comm] using crossDiam B A hBA j i

#print axioms epsilon_metric_properties
end Erdos670EpsilonFamily
