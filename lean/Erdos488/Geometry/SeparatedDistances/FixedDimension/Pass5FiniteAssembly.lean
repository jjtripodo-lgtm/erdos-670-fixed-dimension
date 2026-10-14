import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5ActualConfiguration
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5ActualCrossSeparation
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5LocalEdges
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Padding
import Erdos488.Geometry.SeparatedDistances.FixedDimension.ClusterEdgeAssembly
import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourcePrime

/-! End-to-end finite assembly for the orthogonal-circle fifth pass.
All edge classes refer to the same literal Euclidean point family. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

/-- Local chords and exact cross lengths imply all three metric properties.
Every scalar gate is discharged at the actual fifth-pass parameters. -/
theorem pass5_metric_properties {m k p : ℕ} {E : Type*} [PseudoMetricSpace E]
    (hm : 18177 ≤ m) (hk : 2 ≤ k) (hp : p.Prime)
    (hsize : 2*m*k < p) (hpup : p < 4*m*k)
    (P : Fin m × Fin k → E)
    (hlocal : ∀ (A : Fin m) (i j : Fin k), i < j →
      dist (P (A,i)) (P (A,j)) = pass5LocalEdge p A i j)
    (hcross : ∀ (A B : Fin m), A < B → ∀ (i j : Fin k),
      dist (P (A,i)) (P (B,j)) = pass5CrossLength p k A B i.val j.val) :
    (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
    SeparatedConfiguration P ∧
    (∀ a b, dist (P a) (P b) < (24057/32768 : ℝ)*((m : ℝ)*k)^2) := by
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have crossMin (A B : Fin m) (hAB : A < B) (i j : Fin k) :
      1 ≤ dist (P (A,i)) (P (B,j)) := by
    rw [hcross A B hAB i j]
    have h := pass5_mixed_scalar hm hk
      (pass5ColexBaseline k (pass5Offset m : ℝ) A B)
      (pass5CrossLength p k A B i.val j.val) 0
      (pass5ColexBaseline_lower hk _ A B hAB)
      (pass5CrossLength_displacement hm hp.pos hk A B hAB i.val j.val i.isLt j.isLt)
      (by positivity)
    simpa only [sub_zero] using h
  have localMin (A : Fin m) (i j : Fin k) (hij : i < j) :
      1 ≤ dist (P (A,i)) (P (A,j)) := by
    rw [hlocal A i j hij]
    exact (pass5LocalEdge_min hm0 hk0 hp.pos hpup A i j hij).le
  have hmin := cluster_minimum_distance P localMin
    (fun A B i j hAB => crossMin A B hAB i j)
  have hsep : SeparatedConfiguration P := by
    apply separatedConfiguration_of_cluster_gaps P
    · intro A i j B u v hij huv hne
      rw [hlocal A i j hij, hlocal B u v huv]
      exact (pass5LocalEdge_separated hm0 hk0 hp hsize hpup A B i j u v hij huv hne).le
    · intro A B i j C D u v hAB hCD hne
      rw [hcross A B hAB i j, hcross C D hCD u v]
      exact pass5_concrete_cross_pairs_separated hm hp.pos hk A B C D hAB hCD i j u v hne
    · intro A i j B C u v hij hBC
      rw [hlocal A i j hij, hcross B C hBC u v]
      exact pass5_mixed_scalar hm hk
        (pass5ColexBaseline k (pass5Offset m : ℝ) B C)
        (pass5CrossLength p k B C u.val v.val) (pass5LocalEdge p A i j)
        (pass5ColexBaseline_lower hk _ B C hBC)
        (pass5CrossLength_displacement hm hp.pos hk B C hBC u.val v.val u.isLt v.isLt)
        (pass5LocalEdge_upper hm0 hk0 hp.pos A i j hij).le
  have localDiam (A : Fin m) (i j : Fin k) (hij : i < j) :
      dist (P (A,i)) (P (A,j)) < (24057/32768 : ℝ)*((m : ℝ)*k)^2 := by
    rw [hlocal A i j hij]
    exact pass5_local_diameter_scalar hm hk _ (pass5LocalEdge_upper hm0 hk0 hp.pos A i j hij).le
  have crossDiam (A B : Fin m) (hAB : A < B) (i j : Fin k) :
      dist (P (A,i)) (P (B,j)) < (24057/32768 : ℝ)*((m : ℝ)*k)^2 := by
    rw [hcross A B hAB i j]
    exact pass5_cross_diameter_scalar hm hk
      (pass5ColexBaseline k (pass5Offset m : ℝ) A B)
      (pass5CrossLength p k A B i.val j.val)
      (pass5ColexBaseline_upper hk _ A B hAB)
      (pass5CrossLength_displacement hm hp.pos hk A B hAB i.val j.val i.isLt j.isLt)
  refine ⟨hmin, hsep, ?_⟩
  rintro ⟨A,i⟩ ⟨B,j⟩
  rcases lt_trichotomy A B with hAB | hAB | hBA
  · exact crossDiam A B hAB i j
  · subst B
    rcases lt_trichotomy i j with hij | hij | hji
    · exact localDiam A i j hij
    · subst j
      rw [dist_self]
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
      positivity
    · rw [dist_comm]
      exact localDiam A j i hji
  · rw [dist_comm]
    exact crossDiam B A hBA j i

/-- Unconditional finite source: actual separated mk-point configurations
in exactly the advertised 3m−1 coordinates. -/
theorem pass5_finite_configuration_exists (m k : ℕ)
    (hm : 18177 ≤ m) (hk : 2 ≤ k) :
    ∃ P : Fin m × Fin k → EuclideanSpace ℝ (Fin (3*m-1)),
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
      SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (24057/32768 : ℝ)*((m : ℝ)*k)^2) := by
  obtain ⟨p,hp,hsize,hpup⟩ := source_ruler_prime_exists m k (by omega) (by omega)
  obtain ⟨P,hlocal,hcross⟩ := pass5_actual_configuration_exists m k p hm hk hp hpup
  have hlocal' : ∀ (A : Fin m) (i j : Fin k), i < j →
      dist (P (A,i)) (P (A,j)) = pass5LocalEdge p A i j := hlocal
  have hcross' : ∀ (A B : Fin m), A < B → ∀ (i j : Fin k),
      dist (P (A,i)) (P (B,j)) = pass5CrossLength p k A B i.val j.val := hcross
  obtain ⟨hmin,hsep,hdiam⟩ := pass5_metric_properties hm hk hp hsize hpup P hlocal' hcross'
  have hc : Fintype.card (Pass5.CircleCoordinate (Fin (m-1)) (Fin m)) ≤ 3*m-1 :=
    (Pass5.circleCoordinate_card m (by omega)).le
  let Q := sourcePadCoordinates hc ∘ P
  obtain ⟨hminQ,hsepQ,_⟩ := source_pad_properties hc P hmin hsep
    ((24057/32768 : ℝ)*((m : ℝ)*k)^2) (fun a b => (hdiam a b).le)
  refine ⟨Q, hminQ, hsepQ, ?_⟩
  intro a b
  change dist (sourcePadCoordinates hc (P a)) (sourcePadCoordinates hc (P b)) < _
  rw [sourcePadCoordinates_dist]
  exact hdiam a b

end Erdos488.Geometry.SeparatedDistances.FixedDimension
