import MetricAssembly
import EpsilonEndpoint

namespace Erdos670EpsilonFamily
open Erdos488.Geometry.SeparatedDistances
open Erdos488.Geometry.SeparatedDistances.FixedDimension
open EuclideanEpsilonResearch

/-- The literal two-circle construction supplies the finite source without any
residual geometry, separation, operator, or budget assumption. -/
theorem epsilon_cluster_source : EpsilonClusterSource := by
  intro ξ hξ hξsmall m k hm hk
  obtain ⟨hm8192,_,_⟩ := epsilon_parameter_bounds ξ m hξ hξsmall hm
  obtain ⟨p,hp,hsize,hpmax⟩ := source_ruler_prime_exists m k (by omega) (by omega)
  obtain ⟨q,U,W,hmetric,hfactor,hproj⟩ := uniform_macro_exists ξ m k hξ hξsmall hm hk
  let P : Fin m × Fin k → EuclideanSpace ℝ (TwoCircleCoordinate (Fin (m-1)) (Fin m)) :=
    fun x => epsilonPoint q U W ξ p k x.1 x.2
  obtain ⟨hmin,hsep,hdiam⟩ := epsilon_metric_properties ξ hξ hξsmall hm hk hp hsize hpmax P
    (fun A i j hij => epsilonPoint_local_distance q U W ξ p k hfactor A i j hij)
    (fun A B hAB i j => epsilonPoint_cross_distance q U W ξ p k hξ hk hmetric hfactor hproj A B hAB i j)
  have hc : Fintype.card (TwoCircleCoordinate (Fin (m-1)) (Fin m)) ≤ 5*m-1 :=
    le_of_eq (coordinate_card m (by omega))
  let f : Fin (m*k) → Fin m × Fin k := sourceDeletionEmbedding (le_refl (m*k))
  have hf : Function.Injective f := sourceDeletionEmbedding_injective _
  let Q : Fin (m*k) → EuclideanSpace ℝ (Fin (5*m-1)) := fun a => sourcePadCoordinates hc (P (f a))
  have hd (a b : Fin (m*k)) : dist (Q a) (Q b) = dist (P (f a)) (P (f b)) :=
    sourcePadCoordinates_dist hc _ _
  refine ⟨Q,?_,?_,?_⟩
  · intro a b hab
    rw [hd]
    exact hmin _ _ (fun h => hab (hf h))
  · apply (strictSeparatedConfiguration_iff_four_points Q).2
    intro a b c d hab hcd hne
    rw [hd,hd]
    apply (strictSeparatedConfiguration_iff_four_points P).1 hsep
    · exact fun h => hab (hf h)
    · exact fun h => hcd (hf h)
    · intro h
      apply hne
      rcases h with ⟨hac,hbd⟩ | ⟨had,hbc⟩
      · exact Or.inl ⟨hf hac,hf hbd⟩
      · exact Or.inr ⟨hf had,hf hbc⟩
  · intro a b
    rw [hd]
    exact hdiam _ _

/-- Full epsilon family, including literal distinct unordered edges and actual diameter. -/
theorem epsilon_family (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1/2)
    (n : ℕ) (hn : 4*⌈(8192:ℝ)/ε⌉₊ ≤ n) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin (10*⌈(8192:ℝ)/ε⌉₊-1)),
      Function.Injective Q ∧
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      StrictSeparatedConfiguration Q ∧
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
        1 < |dist (Q a) (Q b)-dist (Q c) (Q d)|) ∧
      (∀ a b, dist (Q a) (Q b) < (1/2+ε)*(n:ℝ)^2) ∧
      Metric.diam (Set.range Q) < (1/2+ε)*(n:ℝ)^2 :=
  epsilon_all_n_of_cluster_sources epsilon_cluster_source ε hε hε2 n hn

/-- Uniform dimension and point-count bound from the same literal construction. -/
theorem uniform_family
    (d n : ℕ) (hd : 163840 ≤ d) (hn : 65536 ≤ n) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin d),
      Function.Injective Q ∧
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      StrictSeparatedConfiguration Q ∧
      (∀ a b c e, a ≠ b → c ≠ e → ¬ ((a=c ∧ b=e) ∨ (a=e ∧ b=c)) →
        1 < |dist (Q a) (Q b)-dist (Q c) (Q e)|) ∧
      (∀ a b, dist (Q a) (Q b) <
        (1/2+(102400:ℝ)/(d:ℝ)+(40960:ℝ)/(n:ℝ))*(n:ℝ)^2) ∧
      Metric.diam (Set.range Q) <
        (1/2+(102400:ℝ)/(d:ℝ)+(40960:ℝ)/(n:ℝ))*(n:ℝ)^2 :=
  uniform_all_n_of_cluster_sources epsilon_cluster_source d n hd hn

#print axioms uniform_family
#print axioms epsilon_cluster_source
#print axioms epsilon_family
end Erdos670EpsilonFamily
