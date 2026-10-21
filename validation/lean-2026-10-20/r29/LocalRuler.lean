import LocalBounds
import SharpRulerNext

namespace Erdos670R29
open Erdos488.Geometry.SeparatedDistances.FixedDimension

lemma ruler_window_real (p k A i d : ℕ) (hp : 0 < p) (hd : 0 < d) (hi : i+d < k) :
    (p : ℝ)*d ≤ (pass5RulerGap 2 p k A i d : ℝ) ∧
    (pass5RulerGap 2 p k A i d : ℝ) ≤ 2*(p : ℝ)*k := by
  obtain ⟨hl,hu⟩ := pass5RulerGap_window 2 p k A i d hp
  have hl' : (2*(d : ℝ)-1)*p < (pass5RulerGap 2 p k A i d : ℝ) := by exact_mod_cast hl
  have hu' : (pass5RulerGap 2 p k A i d : ℝ) < (2*(d : ℝ)+1)*p := by exact_mod_cast hu
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdk : (d : ℝ)+1 ≤ k := by exact_mod_cast (show d+1 ≤ k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  constructor <;> nlinarith

lemma ruler_order_lag (p k A B i j d e : ℕ) (hp : 0 < p)
    (hgap : pass5RulerGap 2 p k A i d < pass5RulerGap 2 p k B j e) : d ≤ e := by
  by_contra h
  have he : e < d := by omega
  have hw := pass5RulerGap_different_lag 2 p k B A j i e d hp (by norm_num) he
  omega

lemma ruler_injective (p k A B i j d e : ℕ) (hp : p.Prime) (hk : 100 ≤ k)
    (hsize : 6*k < p) (hA : A < 6) (hB : B < 6)
    (hd : 0 < d) (he : 0 < e) (hi : i+d < k) (hj : j+e < k)
    (heq : pass5RulerGap 2 p k A i d = pass5RulerGap 2 p k B j e) :
    A=B ∧ i=j ∧ d=e := by
  have hde : d=e := by
    rcases lt_trichotomy d e with h | h | h
    · have hw := pass5RulerGap_different_lag 2 p k A B i j d e hp.pos (by norm_num) h
      omega
    · exact h
    · have hw := pass5RulerGap_different_lag 2 p k B A j i e d hp.pos (by norm_num) h
      omega
  subst e
  obtain ⟨hAB,hij⟩ := rulerGap_same_lag_injective_sharp 2 p 6 k d A B i j
    hp (by omega) hd (by omega) hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩

noncomputable def localEdge (p k A i j : ℕ) : ℝ :=
  localLength k p ((j-i : ℕ) : ℝ) (pass5RulerGap 2 p k A i (j-i))

theorem local_edges_separated (p k A B i j u v : ℕ) (hp : p.Prime) (hk : 100 ≤ k)
    (hsize : 6*k < p) (hpup : 100*p ≤ 606*k) (hA : A < 6) (hB : B < 6)
    (hij : i < j) (huv : u < v) (hj : j < k) (hv : v < k)
    (hne : ¬ (A=B ∧ i=u ∧ j=v)) :
    1 < |localEdge p k A i j-localEdge p k B u v| := by
  have hdi : i+(j-i) < k := by omega
  have hdu : u+(v-u) < k := by omega
  have hd : 0 < j-i := by omega
  have he : 0 < v-u := by omega
  have hgneq : pass5RulerGap 2 p k A i (j-i) ≠ pass5RulerGap 2 p k B u (v-u) := by
    intro h
    obtain ⟨hAB,hi,hde⟩ := ruler_injective p k A B i u (j-i) (v-u) hp hk hsize hA hB hd he hdi hdu h
    apply hne
    exact ⟨hAB,hi,by omega⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpk : (p : ℝ) ≤ (303/50)*(k : ℝ) := by
    have h : (100 : ℝ)*p ≤ 606*k := by exact_mod_cast hpup
    linarith
  have ordered (A B i u d e : ℕ) (hd : 0 < d) (he : 0 < e)
      (hdi : i+d < k) (hdu : u+e < k)
      (hgap : pass5RulerGap 2 p k A i d < pass5RulerGap 2 p k B u e) :
      1 < localLength k p e (pass5RulerGap 2 p k B u e)-
        localLength k p d (pass5RulerGap 2 p k A i d) := by
    have hde := ruler_order_lag p k A B i u d e hp.pos hgap
    have hgap' : (1 : ℝ) ≤ (pass5RulerGap 2 p k B u e : ℝ)-(pass5RulerGap 2 p k A i d : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ pass5RulerGap 2 p k B u e-pass5RulerGap 2 p k A i d by omega)
    exact local_ordered_gap k p d e _ _ hk' hp' hpk (by positivity)
      (by exact_mod_cast hde) (by exact_mod_cast (show e ≤ k by omega))
      (ruler_window_real p k A i d hp.pos hd hdi).1 hgap'
      (ruler_window_real p k B u e hp.pos he hdu).2
  rcases lt_or_gt_of_ne hgneq with h | h
  · have hh := ordered A B i u (j-i) (v-u) hd he hdi hdu h
    unfold localEdge
    rw [abs_of_neg (by linarith)]
    linarith
  · have hh := ordered B A u i (v-u) (j-i) he hd hdu hdi h
    unfold localEdge
    rw [abs_of_pos (by linarith)]
    exact hh

#print axioms local_edges_separated
end Erdos670R29
