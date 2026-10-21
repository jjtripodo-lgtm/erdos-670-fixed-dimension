import FiniteAssembly
import PrimeFirst

namespace Erdos670R29
open scoped Matrix BigOperators
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances

/-- Every admissible prime gives one actual separated configuration in R^29. -/
theorem finite_configuration (k p : ℕ) (hk : 100 ≤ k) (hp : p.Prime)
    (hsize : 6*k < p) (hpup : 100*p ≤ 606*k) :
    ∃ P : Fin (6*k) → EuclideanSpace ℝ (Fin 29),
      Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*((6*k : ℕ) : ℝ)^2) := by
  obtain ⟨Q,U,W,hQ,hproj,hfactor⟩ := finite_k_completion (k : ℝ) (by exact_mod_cast hk)
  let P₀ : Fin 6 × Fin k → EuclideanSpace ℝ (TwoCircleCoordinate (Fin 5) (Fin 6)) :=
    fun ai => pointFamily p Q U W ai.1 ai.2
  obtain ⟨hmin,hsep,hdiam⟩ := metric_properties hk hp hsize hpup P₀
    (fun A i j hij => pointFamily_local p Q U W hfactor A i j hij)
    (fun A B hAB i j => pointFamily_cross p Q U W hQ hproj hfactor A B hAB i j)
  have hc : Fintype.card (TwoCircleCoordinate (Fin 5) (Fin 6)) ≤ 29 := coordinate_card.le
  let P₁ := sourcePadCoordinates hc ∘ P₀
  obtain ⟨hmin₁,hsep₁,_⟩ := source_pad_properties hc P₀ hmin hsep
    ((499/500 : ℝ)*(6*(k : ℝ))^2) (fun a b => (hdiam a b).le)
  let f : Fin (6*k) → Fin 6 × Fin k := sourceDeletionEmbedding (le_refl (6*k))
  have hf : Function.Injective f := sourceDeletionEmbedding_injective _
  let P := P₁ ∘ f
  have hminP : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b) := source_minimum_restrict P₁ f hf hmin₁
  refine ⟨P,injective_of_unit_minimum_distance P hminP,hminP,
    source_separated_restrict P₁ f hf hsep₁,?_⟩
  intro a b
  dsimp [P,P₁]
  rw [sourcePadCoordinates_dist]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hdiam (f a) (f b)

lemma finite_range_diam_lt {ι E : Type*} [Fintype ι] [Nonempty ι] [PseudoMetricSpace E]
    (P : ι → E) (C : ℝ) (h : ∀ a b, dist (P a) (P b) < C) :
    Metric.diam (Set.range P) < C := by
  let s : Finset (ι × ι) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  let B := s.sup' hs (fun ab => dist (P ab.1) (P ab.2))
  have hB (a b : ι) : dist (P a) (P b) ≤ B :=
    Finset.le_sup' (s := s) (f := fun ab => dist (P ab.1) (P ab.2)) (Finset.mem_univ (a,b))
  have hBpos : 0 ≤ B := by
    let a : ι := Classical.choice inferInstance
    exact (dist_nonneg : 0 ≤ dist (P a) (P a)).trans (hB a a)
  have hBlt : B < C := by
    apply (Finset.sup'_lt_iff (s := s) hs).2
    intro ab _
    exact h ab.1 ab.2
  apply lt_of_le_of_lt ?_ hBlt
  apply Metric.diam_le_of_forall_dist_le hBpos
  intro x hx y hy
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact hB a b

/-- Prime-first endpoint: arbitrarily large finite configurations in the same R^29,
with unit minimum distance, separated unordered-edge lengths and diameter < .998 n². -/
theorem r29_unbounded_counterexamples (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 600 ≤ n ∧
    ∃ P : Fin n → EuclideanSpace ℝ (Fin 29), Function.Injective P ∧
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧ SeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) < (499/500 : ℝ)*(n : ℝ)^2) ∧
      Metric.diam (Set.range P) < (499/500 : ℝ)*(n : ℝ)^2 := by
  obtain ⟨k,p,hk,hp,hsize,hpup⟩ := admissible_prime_sizes_unbounded N
  have hk100 : 100 ≤ k := (le_max_left 100 N).trans hk
  have hkN : N ≤ k := (le_max_right 100 N).trans hk
  obtain ⟨P,hinj,hmin,hsep,hdiam⟩ := finite_configuration k p hk100 hp hsize (by omega)
  haveI : Nonempty (Fin (6*k)) := ⟨⟨0,by omega⟩⟩
  exact ⟨6*k,by omega,by omega,P,hinj,hmin,hsep,hdiam,finite_range_diam_lt P _ hdiam⟩

#print axioms finite_configuration
#print axioms r29_unbounded_counterexamples
end Erdos670R29
