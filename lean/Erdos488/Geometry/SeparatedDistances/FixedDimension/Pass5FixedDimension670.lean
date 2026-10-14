import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5FiniteAssembly

/-! The unconditional concrete endpoint of the fifth-pass orthogonal-circle
construction. The previous fixed-dimension theorem remains unchanged. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

private theorem pass5_finite_range_diam_lt {ι E : Type*}
    [Fintype ι] [Nonempty ι] [PseudoMetricSpace E]
    (P : ι → E) (C : ℝ) (h : ∀ a b, dist (P a) (P b) < C) :
    Metric.diam (Set.range P) < C := by
  let s : Finset (ι × ι) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  let B := s.sup' hs (fun ab => dist (P ab.1) (P ab.2))
  have hB (a b : ι) : dist (P a) (P b) ≤ B := by
    exact Finset.le_sup' (s := s) (f := fun ab => dist (P ab.1) (P ab.2))
      (Finset.mem_univ (a,b))
  have hBpos : 0 ≤ B := by
    let a : ι := Classical.choice inferInstance
    exact (dist_nonneg : 0 ≤ dist (P a) (P a)).trans (hB a a)
  have hBlt : B < C := by
    apply (Finset.sup'_lt_iff (s := s) hs).2
    intro ab hab
    exact h ab.1 ab.2
  have hdiam : Metric.diam (Set.range P) ≤ B := by
    apply Metric.diam_le_of_forall_dist_le hBpos
    intro x hx y hy
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact hB a b
  exact hdiam.trans_lt hBlt

/-- For every n ≥ 36354, one fixed Euclidean space of dimension 81794
contains n injectively indexed points, with unit minimum distance, pairwise
unit-separated unordered edge lengths, and actual diameter < (147/200)n². -/
theorem pass5_fixed_dimension_erdos_670 (n : ℕ) (hn : 36354 ≤ n) :
    ∃ P : Fin n → EuclideanSpace ℝ (Fin 81794),
      Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
      SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (147/200 : ℝ)*(n : ℝ)^2) ∧
      Metric.diam (Set.range P) < (147/200 : ℝ)*(n : ℝ)^2 := by
  have hsource : ∀ m k : ℕ, 18177 ≤ m → m ≤ 27265 → 2 ≤ k →
      ∃ P : Fin m × Fin k → EuclideanSpace ℝ (Fin (3*m-1)),
        (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
        SeparatedConfiguration P ∧
        (∀ a b, dist (P a) (P b) < (24057/32768 : ℝ)*((m : ℝ)*k)^2) := by
    intro m k hm _ hk
    exact pass5_finite_configuration_exists m k hm hk
  obtain ⟨P,hmin,hsep,hdiam⟩ := pass5_all_n_of_finite_sources hsource n hn
  have hinj : Function.Injective P := injective_of_unit_minimum_distance P hmin
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact ⟨P,hinj,hmin,hsep,hdiam,pass5_finite_range_diam_lt P _ hdiam⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension
