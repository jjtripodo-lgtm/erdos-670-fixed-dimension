import CrossSpectrum
import Erdos488.Geometry.SeparatedDistances.FixedDimension.ClusterEdgeAssembly
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Padding

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

lemma localEdge_min (p k A i j : ℕ) (hk : 100 ≤ k) (hp : 0 < p)
    (hij : i < j) (hj : j < k) : 1 < localEdge p k A i j := by
  have hd : 0 < j-i := by omega
  have hdi : i+(j-i) < k := by omega
  obtain ⟨hl,hu⟩ := ruler_window_real p k A i (j-i) hp hd hdi
  exact localLength_min k p (j-i : ℕ) _ (by exact_mod_cast hk) (by exact_mod_cast hp)
    (by exact_mod_cast hd) hl hu

lemma localEdge_upper (p k A i j : ℕ) (hk : 100 ≤ k) (hp : 0 < p)
    (hij : i < j) (hj : j < k) : localEdge p k A i j < 18*(k : ℝ)^2 := by
  have hd : 0 < j-i := by omega
  have hdi : i+(j-i) < k := by omega
  obtain ⟨hl,hu⟩ := ruler_window_real p k A i (j-i) hp hd hdi
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  exact localLength_upper k p (j-i : ℕ) _ (by exact_mod_cast (show 0 < k by omega)) hp'
    (by positivity) (by exact_mod_cast (show j-i ≤ k by omega))
    ((by positivity : (0 : ℝ) ≤ (p : ℝ)*(j-i : ℕ)).trans hl) hu

theorem metric_properties {k p : ℕ} {E : Type*} [PseudoMetricSpace E]
    (hk : 100 ≤ k) (hp : p.Prime) (hsize : 6*k < p) (hpup : 100*p ≤ 606*k)
    (P : Fin 6 × Fin k → E)
    (hlocal : ∀ (A : Fin 6) (i j : Fin k), i < j →
      dist (P (A,i)) (P (A,j)) = localEdge p k A.val i.val j.val)
    (hcross : ∀ (A B : Fin 6), A < B → ∀ (i j : Fin k),
      dist (P (A,i)) (P (B,j)) = crossLength k A B i.val j.val) :
    (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
    (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*(6*(k : ℝ))^2) := by
  have hk' : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hksq : 10000 ≤ (k : ℝ)^2 := by nlinarith
  have localMin (A : Fin 6) (i j : Fin k) (hij : i < j) : 1 ≤ dist (P (A,i)) (P (A,j)) := by
    rw [hlocal A i j hij]
    exact (localEdge_min p k A.val i.val j.val hk hp.pos hij j.isLt).le
  have crossMin (A B : Fin 6) (i j : Fin k) (hAB : A < B) : 1 ≤ dist (P (A,i)) (P (B,j)) := by
    rw [hcross A B hAB i j]
    have h := cross_lower k hk A B hAB i.val j.val i.isLt j.isLt
    nlinarith
  refine ⟨cluster_minimum_distance P localMin crossMin, ?_, ?_⟩
  · apply separatedConfiguration_of_cluster_gaps P
    · intro A i j B u v hij huv hne
      rw [hlocal A i j hij, hlocal B u v huv]
      apply (local_edges_separated p k A.val B.val i.val j.val u.val v.val hp hk hsize hpup
        A.isLt B.isLt hij huv j.isLt v.isLt ?_).le
      rintro ⟨hA,hi,hj⟩
      exact hne (Prod.ext (Fin.ext hA) (Prod.ext (Fin.ext hi) (Fin.ext hj)))
    · intro A B i j C D u v hAB hCD hne
      rw [hcross A B hAB i j, hcross C D hCD u v]
      exact cross_edges_separated k hk A B C D hAB hCD i j u v hne
    · intro A i j B C u v hij hBC
      rw [hlocal A i j hij, hcross B C hBC u v]
      have hl := localEdge_upper p k A.val i.val j.val hk hp.pos hij j.isLt
      have hc := cross_lower k hk B C hBC u.val v.val u.isLt v.isLt
      nlinarith
  · have localDiam (A : Fin 6) (i j : Fin k) (hij : i < j) :
        dist (P (A,i)) (P (A,j)) < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
      rw [hlocal A i j hij]
      have h := localEdge_upper p k A.val i.val j.val hk hp.pos hij j.isLt
      nlinarith
    have crossDiam (A B : Fin 6) (hAB : A < B) (i j : Fin k) :
        dist (P (A,i)) (P (B,j)) < (499/500 : ℝ)*(6*(k : ℝ))^2 := by
      rw [hcross A B hAB i j]
      exact cross_upper k hk A B hAB i.val j.val i.isLt j.isLt
    rintro ⟨A,i⟩ ⟨B,j⟩
    rcases lt_trichotomy A B with hAB | hAB | hBA
    · exact crossDiam A B hAB i j
    · subst B
      rcases lt_trichotomy i j with hij | hij | hji
      · exact localDiam A i j hij
      · subst j
        rw [dist_self]
        positivity
      · rw [dist_comm]; exact localDiam A j i hji
    · rw [dist_comm]; exact crossDiam B A hBA j i

#print axioms metric_properties
end Erdos670R29
