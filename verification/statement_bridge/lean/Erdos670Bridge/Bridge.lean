import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5FixedDimension670
import Erdos670Bridge.Statement

/-! Adapter to the exact fixed-dimension proposition of Formal Conjectures
at commit c77fdd446d23539302aa73bcfae4a9fa962b8382. The upstream theorem,
which has an unproved body, is never imported. -/

open Filter
open Erdos488.Geometry.SeparatedDistances
open Erdos488.Geometry.SeparatedDistances.FixedDimension

namespace Erdos670Bridge

/-- Index-edge separation implies the upstream point-pair predicate. -/
theorem hasSeparatedDistances_image {ι E : Type*} [Fintype ι]
    [MetricSpace E] [DecidableEq E] (P : ι → E) (hsep : SeparatedConfiguration P) :
    Erdos670.HasSeparatedDistances (Finset.univ.image P) := by
  classical
  intro a ha b hb c hc e he hab hce hpairs
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp he
  have hij : i ≠ j := fun h => hab (congrArg P h)
  have hkl : k ≠ l := fun h => hce (congrArg P h)
  let u : Edge ι := ⟨s(i, j), by simpa only [Sym2.isDiag_iff_proj_eq] using hij⟩
  let v : Edge ι := ⟨s(k, l), by simpa only [Sym2.isDiag_iff_proj_eq] using hkl⟩
  have huv : u ≠ v := by
    intro h
    have huv' : s(i, j) = s(k, l) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp huv' with ⟨hik, hjl⟩ | ⟨hil, hjk⟩
    · apply hpairs
      rw [hik, hjl]
    · apply hpairs
      rw [hil, hjk]
      exact Sym2.eq_swap
  simpa only [u, v, edgeDistance, Sym2.lift_mk] using hsep u v huv

/-- The finite image and range represent exactly the same point set. -/
theorem coe_univ_image_eq_range {ι E : Type*} [Fintype ι]
    [DecidableEq E] (P : ι → E) :
    (Finset.univ.image P : Set E) = Set.range P := by
  ext x
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]

/-- A counterexample in dimension 81794 for every size at least 36354,
using the exact upstream separation predicate and finite-set diameter. -/
theorem finite_counterexample (n : ℕ) (hn : 36354 ≤ n) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 81794)),
      A.card = n ∧ Erdos670.HasSeparatedDistances A ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 81794))) <
        (147 / 200 : ℝ) * (n : ℝ) ^ 2 := by
  classical
  obtain ⟨P, hinj, _, hsep, _, hdiam⟩ := pass5_fixed_dimension_erdos_670 n hn
  refine ⟨Finset.univ.image P, ?_, hasSeparatedDistances_image P hsep, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ hinj
  · rw [coe_univ_image_eq_range]
    exact hdiam

/-- Negation of the exact extracted fixed-dimension proposition. -/
theorem not_fixedDimensionStatement : ¬ Erdos670.FixedDimensionStatement := by
  intro h
  have hevent := h 81794 (by norm_num) (1 / 4) (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let n := max N 36354
  obtain ⟨A, hcard, hsep, hdiam⟩ := finite_counterexample n (le_max_right _ _)
  have hlower := hN n (le_max_left _ _) A hcard hsep
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by dsimp [n]; omega)
  have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  norm_num at hlower
  nlinarith

/-- The result with the full upstream proposition displayed in its type. -/
theorem erdos_670_negated :
    ¬ (∀ d : ℕ, 1 ≤ d → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n → Erdos670.HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d)))) :=
  not_fixedDimensionStatement

end Erdos670Bridge
