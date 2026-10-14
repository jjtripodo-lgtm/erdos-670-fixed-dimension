import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleConstruction
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Local
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossSeparation

/-! One actual finite Euclidean configuration, with the numerical parameters,
the literal single prime ruler, and both local/cross metric formulas attached
to the same points. Separation and final all-n padding are proved separately. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open Pass5

/-- At the concrete source parameters, the very same mk points realize both
the local-ruler chords and the exact two-digit square-root cross spectrum. -/
theorem pass5_actual_configuration_exists (m k p : ℕ)
    (hm : 18177 ≤ m) (hk : 2 ≤ k) (hp : p.Prime) (hpup : p < 4*m*k) :
    ∃ P : Fin m × Fin k →
        EuclideanSpace ℝ (CircleCoordinate (Fin (m-1)) (Fin m)),
      (∀ (A : Fin m) (i j : Fin k), i.val < j.val →
        dist (P (A,i)) (P (A,j)) =
          pass5LocalLength m k p A.val i.val (j.val-i.val)) ∧
      (∀ (A B : Fin m), A.val < B.val → ∀ (i j : Fin k),
        dist (P (A,i)) (P (B,j)) =
          pass5Phi (pass5Scale k*circleColexDistance (pass5Offset m : ℝ) A B)
            (pass5CrossDigit (9/8 : ℝ) k (pass5Digit p k A.val) (pass5Digit p k B.val)
              i.val j.val)) := by
  obtain ⟨_, _, _, hC2, hC3, hC4, _⟩ := pass5_five_conditions m hm
  have hmreal : (18177 : ℝ) ≤ m := by exact_mod_cast hm
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hmK : (m : ℝ) ≤ (pass5Offset m : ℝ) := (le_max_left _ _).trans hC2
  have hlarge : 16384*(harmonic m : ℝ)^2 ≤ (pass5Offset m : ℝ) :=
    (le_max_right _ _).trans hC2
  have hK : (10 : ℝ) ≤ pass5Offset m := by linarith
  have hk0 : 0 < k := by omega
  have hm0 : 0 < m := by omega
  obtain ⟨F, hlocal, hcross⟩ := circle_points_from_scalar_gates (by omega : 3 ≤ m)
    (pass5Offset m : ℝ) 101 (9/8) (49/100) (k : ℝ)
    (by norm_num) (by norm_num) (by positivity) (by norm_num)
    hK hlarge hmK (by nlinarith) hC3 hC4
  let P : Fin m × Fin k → EuclideanSpace ℝ (CircleCoordinate (Fin (m-1)) (Fin m)) :=
    fun x => F x.1 (pass5Angle p k x.1.val x.2.val)
  refine ⟨P, ?_, ?_⟩
  · intro A i j hij
    have he : i.val+(j.val-i.val) = j.val := by omega
    have hδ : 0 < j.val-i.val := by omega
    have hrange : i.val+(j.val-i.val) < k := by omega
    have hchord := pass5LocalLength_eq_abs_chord m k p A.val i.val (j.val-i.val)
      hm0 hk0 hp.pos hpup hδ hrange
    rw [he] at hchord
    change dist (F A (pass5Angle p k A.val i.val)) (F A (pass5Angle p k A.val j.val)) = _
    rw [dist_comm, hlocal]
    simpa only [pass5Radius] using hchord
  · intro A B hAB i j
    simpa only [P, pass5Phi, pass5Scale, pass5CrossDigit, pass5Digit, sineDigit,
      pass5Angle, pass5Theta] using
      hcross A B hAB (pass5Angle p k A.val i.val) (pass5Angle p k B.val j.val)

end Erdos488.Geometry.SeparatedDistances.FixedDimension
