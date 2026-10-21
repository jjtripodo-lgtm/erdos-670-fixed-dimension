import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceAllNEmbedding
import Erdos488.Geometry.SeparatedDistances.FixedDimension.ClusterEdgeAssembly

namespace EuclideanEpsilonResearch
open Erdos488.Geometry.SeparatedDistances
open Erdos488.Geometry.SeparatedDistances.FixedDimension

def StrictSeparatedConfiguration {ι E : Type*} [PseudoMetricSpace E] (P : ι → E) : Prop :=
  ∀ e f : Edge ι, e ≠ f → 1 < |edgeDistance P e.val-edgeDistance P f.val|

theorem strictSeparatedConfiguration_iff_four_points
    {ι E : Type*} [PseudoMetricSpace E] (P : ι → E) :
    StrictSeparatedConfiguration P ↔
    ∀ a b c d, a ≠ b → c ≠ d → ¬ ((a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
      1 < |dist (P a) (P b)-dist (P c) (P d)| := by
  constructor
  · intro h a b c d hab hcd hne
    let e : Edge ι := ⟨s(a,b),by simpa only [Sym2.mk_isDiag_iff] using hab⟩
    let f : Edge ι := ⟨s(c,d),by simpa only [Sym2.mk_isDiag_iff] using hcd⟩
    have hef : e ≠ f := by
      intro heq
      exact hne (Sym2.eq_iff.mp (congrArg Subtype.val heq))
    exact h e f hef
  · intro h e f hef
    induction e using Subtype.rec with
    | _ s hs =>
      induction f using Subtype.rec with
      | _ t ht =>
        induction s using Sym2.inductionOn with
        | hf a b =>
          induction t using Sym2.inductionOn with
          | hf c d =>
            have hab : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using hs
            have hcd : c ≠ d := by simpa only [Sym2.mk_isDiag_iff] using ht
            have hne : ¬ ((a=c ∧ b=d) ∨ (a=d ∧ b=c)) := by
              intro hh
              exact hef (Subtype.ext (Sym2.eq_iff.mpr hh))
            exact h a b c d hab hcd hne

/-- All four combinations of unordered edge classes are checked. -/
theorem strictSeparatedConfiguration_of_cluster_gaps
    {α β E : Type*} [LinearOrder α] [LinearOrder β] [PseudoMetricSpace E]
    (p : α × β → E)
    (hlocal : ∀ A i j B u v, i < j → u < v → (A,i,j) ≠ (B,u,v) →
      1 < |dist (p (A,i)) (p (A,j))-dist (p (B,u)) (p (B,v))|)
    (hcross : ∀ A B i j C D u v, A < B → C < D → (A,B,i,j) ≠ (C,D,u,v) →
      1 < |dist (p (A,i)) (p (B,j))-dist (p (C,u)) (p (D,v))|)
    (hmixed : ∀ A i j B C u v, i < j → B < C →
      1 < dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))) :
    StrictSeparatedConfiguration p := by
  intro e f hef
  have hval : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  rcases cluster_edge_cases e with ⟨A,i,j,hij,he⟩ | ⟨A,B,i,j,hAB,he⟩
  · rcases cluster_edge_cases f with ⟨B,u,v,huv,hf⟩ | ⟨B,C,u,v,hBC,hf⟩
    · have hne : (A,i,j) ≠ (B,u,v) := by
        intro h
        have hA : A=B := congrArg Prod.fst h
        have hi : i=u := congrArg (fun q => q.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2) h
        apply hval
        simp only [he,hf,hA,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hlocal A i j B u v hij huv hne
    · have h := (hmixed A i j B C u v hij hBC).trans_le
        (le_abs_self (dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))))
      rw [abs_sub_comm] at h
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
  · rcases cluster_edge_cases f with ⟨C,u,v,huv,hf⟩ | ⟨C,D,u,v,hCD,hf⟩
    · have h := (hmixed C u v A B i j huv hAB).trans_le (le_abs_self _)
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
    · have hne : (A,B,i,j) ≠ (C,D,u,v) := by
        intro h
        have hA : A=C := congrArg Prod.fst h
        have hB : B=D := congrArg (fun q => q.2.1) h
        have hi : i=u := congrArg (fun q => q.2.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2.2) h
        apply hval
        simp only [he,hf,hA,hB,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hcross A B i j C D u v hAB hCD hne

theorem finite_range_diam_lt {ι E : Type*}
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


/-- Deletion and zero padding retain strict genuine unordered-edge gaps.
The source configuration and both numerical bounds remain explicit hypotheses. -/
theorem exact_n_delete_pad {n N d D : ℕ} (hn : 0 < n)
    (hsize : n ≤ N) (hdim : d ≤ D)
    (P : Fin N → EuclideanSpace ℝ (Fin d))
    (hmin : ∀ a b, a ≠ b → 1 ≤ dist (P a) (P b))
    (hsep : StrictSeparatedConfiguration P) (B C : ℝ)
    (hbound : ∀ a b, dist (P a) (P b) ≤ B) (hBC : B < C) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin D),
      Function.Injective Q ∧
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      StrictSeparatedConfiguration Q ∧
      (∀ a b, dist (Q a) (Q b) ≤ B) ∧
      (∀ a b, dist (Q a) (Q b) < C) ∧
      Metric.diam (Set.range Q) < C := by
  let f : Fin n → Fin N := Fin.castLE hsize
  have hf : Function.Injective f := Fin.castLE_injective hsize
  have hc : Fintype.card (Fin d) ≤ D := by simpa using hdim
  let Q : Fin n → EuclideanSpace ℝ (Fin D) := fun a => sourcePadCoordinates hc (P (f a))
  have hdist (a b : Fin n) : dist (Q a) (Q b) = dist (P (f a)) (P (f b)) :=
    sourcePadCoordinates_dist hc _ _
  have hminQ : ∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b) := by
    intro a b hab
    rw [hdist]
    exact hmin _ _ (hf.ne hab)
  have hsepQ : StrictSeparatedConfiguration Q := by
    rw [strictSeparatedConfiguration_iff_four_points]
    intro a b c d hab hcd hne
    rw [hdist,hdist]
    apply (strictSeparatedConfiguration_iff_four_points P).1 hsep _ _ _ _
      (hf.ne hab) (hf.ne hcd)
    intro hh
    apply hne
    rcases hh with ⟨hac,hbd⟩ | ⟨had,hbc⟩
    · exact Or.inl ⟨hf hac,hf hbd⟩
    · exact Or.inr ⟨hf had,hf hbc⟩
  have hbQ : ∀ a b, dist (Q a) (Q b) ≤ B := by
    intro a b
    rw [hdist]
    exact hbound _ _
  have hcQ : ∀ a b, dist (Q a) (Q b) < C := fun a b => (hbQ a b).trans_lt hBC
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact ⟨Q,injective_of_unit_minimum_distance Q hminQ,hminQ,hsepQ,hbQ,hcQ,
    finite_range_diam_lt Q C hcQ⟩

#print axioms strictSeparatedConfiguration_iff_four_points
#print axioms strictSeparatedConfiguration_of_cluster_gaps
#print axioms finite_range_diam_lt
#print axioms exact_n_delete_pad
end EuclideanEpsilonResearch
