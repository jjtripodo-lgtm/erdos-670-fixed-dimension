import R29Endpoint
import Erdos670Bridge.Statement

/-! Independent lightweight adapter. It preserves the exact extracted upstream
statement and uses the new R29 endpoint directly, without importing the old
81794-dimensional counterexample theorem or its full bridge module. -/
namespace Erdos670R29Minimal
open Filter Erdos488.Geometry.SeparatedDistances

theorem finite_set_counterexamples (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 600 ≤ n ∧
    ∃ A : Finset (EuclideanSpace ℝ (Fin 29)), A.card=n ∧
      Erdos670.HasSeparatedDistances A ∧
      Metric.diam (A : Set (EuclideanSpace ℝ (Fin 29))) < (499/500 : ℝ)*(n : ℝ)^2 := by
  classical
  obtain ⟨n,hN,hn,P,hinj,_,hsep,_,hdiam⟩ := Erdos670R29.r29_unbounded_counterexamples N
  refine ⟨n,hN,hn,Finset.univ.image P,?_,?_,?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ hinj
  · intro a ha b hb c hc e he hab hce hpairs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp he
    have hij : i ≠ j := fun h => hab (congrArg P h)
    have hkl : k ≠ l := fun h => hce (congrArg P h)
    let u : Edge (Fin n) := ⟨s(i,j), by simpa only [Sym2.isDiag_iff_proj_eq] using hij⟩
    let v : Edge (Fin n) := ⟨s(k,l), by simpa only [Sym2.isDiag_iff_proj_eq] using hkl⟩
    have huv : u ≠ v := by
      intro h
      have huv' : s(i,j) = s(k,l) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp huv' with ⟨hik,hjl⟩ | ⟨hil,hjk⟩
      · apply hpairs
        rw [hik,hjl]
      · apply hpairs
        rw [hil,hjk]
        exact Sym2.eq_swap
    simpa only [u,v,edgeDistance,Sym2.lift_mk] using hsep u v huv
  · have heq : (Finset.univ.image P : Set (EuclideanSpace ℝ (Fin 29))) = Set.range P := by
      ext x
      simp only [Finset.mem_coe,Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range]
    rw [heq]
    exact hdiam

theorem not_fixedDimensionStatement_r29 : ¬ Erdos670.FixedDimensionStatement := by
  intro h
  have hevent := h 29 (by norm_num) (1/1000) (by norm_num)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨n,hn,hn600,A,hcard,hsep,hdiam⟩ := finite_set_counterexamples N
  have hlower := hN n hn A hcard hsep
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2pos : 0 < (n : ℝ)^2 := sq_pos_of_pos hnpos
  norm_num at hlower
  nlinarith

#print axioms finite_set_counterexamples
#print axioms not_fixedDimensionStatement_r29
end Erdos670R29Minimal
