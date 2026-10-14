import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleMacro

/-! Actual continuous circle families from scalar macro and radius gates.
This theorem constructs every point from one common colex realization and one
common residual factor. Ruler angles and edge-separation bounds remain separate. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
namespace Pass5
open scoped BigOperators Matrix

/-- Scalar macro gates and C3/C4 produce the advertised actual circle family,
with both local and cross metric formulas for these very same points. -/
theorem circle_points_from_scalar_gates {m : ℕ} (hm : 3 ≤ m)
    (K C s a k : ℝ) (hs : 0 < s) (ha : 0 < a) (hk : 0 < k) (hC : 0 ≤ C)
    (hK : 10 ≤ K) (hlarge : 16384*(harmonic m : ℝ)^2 ≤ K)
    (hmK : (m : ℝ) ≤ K) (hc : 1 ≤ s*k)
    (hC3 : 4*C*(m : ℝ)/s^3 ≤ K)
    (hC4 : (84*s^2/a)*Real.sqrt (K+(m : ℝ)) ≤ C*(m : ℝ)) :
    ∃ P : Fin m → ℝ → EuclideanSpace ℝ (CircleCoordinate (Fin (m-1)) (Fin m)),
      (∀ A z w, dist (P A z) (P A w) =
        2*(C*(m : ℝ)*k^2)*|Real.sin ((z-w)/2)|) ∧
      (∀ A B, A.val < B.val → ∀ z w,
        dist (P A z) (P B w) =
          Real.sqrt (((s^3*k^2)*circleColexDistance K A B)^2 +
            2*((s^3*k^2)*circleColexDistance K A B)*
              (s^2*k*(Real.sin z/(a/k))+s*(Real.sin w/(a/k))))) := by
  have hK0 : 0 ≤ K := by linarith
  have hr := circle_shortening_of_C3 C (m : ℝ) s k K hs hk (by positivity) hK0 hC3
  have hbudget := circle_budget_of_C4 C (m : ℝ) s a k K ha hk (by positivity) hC4
  obtain ⟨p, U, W, hmetric, hfactor, hproj⟩ := colex_circle_macro_exists_m hm
    hK hlarge hmK (s^3*k^2) (C*(m : ℝ)*k^2) s (a/k) k hr hc hbudget
  let P : Fin m → ℝ → EuclideanSpace ℝ (CircleCoordinate (Fin (m-1)) (Fin m)) :=
    fun A z => circlePoint (fun A i => p A i) U W (s^3*k^2) (C*(m : ℝ)*k^2) A z
  refine ⟨P, ?_, ?_⟩
  · intro A z w
    exact circlePoint_same_distance (fun A i => p A i) U W (s^3*k^2)
      (C*(m : ℝ)*k^2) (by positivity) hfactor A z w
  · intro A B hAB z w
    exact circlePoint_colex_cross_distance p U W K (s^3*k^2) (C*(m : ℝ)*k^2)
      s (a/k) k (by positivity) hmetric hfactor hproj A B hAB z w

end Pass5
end Erdos488.Geometry.SeparatedDistances.FixedDimension
