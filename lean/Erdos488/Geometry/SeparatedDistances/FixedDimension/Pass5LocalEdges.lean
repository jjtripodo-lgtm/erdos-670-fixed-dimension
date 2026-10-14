import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Local

/-! Increasing-endpoint interfaces for the fifth-pass local-edge spectrum. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def pass5LocalEdge {m k : ℕ} (p : ℕ) (A : Fin m) (i j : Fin k) : ℝ :=
  pass5LocalLength m k p A.val i.val (j.val-i.val)

theorem pass5LocalEdge_min {m k p : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) (A : Fin m) (i j : Fin k) (hij : i < j) :
    1 < pass5LocalEdge p A i j := by
  exact pass5LocalLength_gt_one m k p A.val i.val (j.val-i.val) hm hk hp hpup
    (by exact Nat.sub_pos_of_lt hij) (by have := j.isLt; omega)

theorem pass5LocalEdge_upper {m k p : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (A : Fin m) (i j : Fin k) (hij : i < j) :
    pass5LocalEdge p A i j < (101 : ℝ)*(49/100)*(m : ℝ)*(k : ℝ)^2 := by
  exact pass5LocalLength_upper m k p A.val i.val (j.val-i.val) hm hk hp
    (by exact Nat.sub_pos_of_lt hij) (by have := j.isLt; omega)

theorem pass5LocalEdge_eq_abs_chord {m k p : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < p) (hpup : p < 4*m*k) (A : Fin m) (i j : Fin k) (hij : i < j) :
    2*pass5Radius m k*|Real.sin ((pass5Angle p k A.val j.val-pass5Angle p k A.val i.val)/2)| =
      pass5LocalEdge p A i j := by
  have he : i.val+(j.val-i.val)=j.val := Nat.add_sub_of_le hij.le
  have h := pass5LocalLength_eq_abs_chord m k p A.val i.val (j.val-i.val)
    hm hk hp hpup (Nat.sub_pos_of_lt hij) (by have := j.isLt; omega)
  simpa only [he, pass5LocalEdge] using h

theorem pass5LocalEdge_separated {m k p : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hp : p.Prime) (hsize : 2*m*k < p) (hpup : p < 4*m*k)
    (A B : Fin m) (i j u v : Fin k) (hij : i < j) (huv : u < v)
    (hne : (A,i,j) ≠ (B,u,v)) :
    1 < |pass5LocalEdge p A i j-pass5LocalEdge p B u v| := by
  have hkp : k < p := by
    have hmul : k ≤ 2*m*k := by nlinarith
    omega
  have hδ : 0 < j.val-i.val := Nat.sub_pos_of_lt hij
  have hε : 0 < v.val-u.val := Nat.sub_pos_of_lt huv
  have hne' : ¬ (A.val=B.val ∧ i.val=u.val ∧ j.val-i.val=v.val-u.val) := by
    rintro ⟨hA,hi,hδ⟩
    apply hne
    have hj : j.val=v.val := by have hij' : i.val<j.val := hij; have huv' : u.val<v.val := huv; omega
    exact Prod.ext (Fin.ext hA) (Prod.ext (Fin.ext hi) (Fin.ext hj))
  exact pass5LocalLength_separated m k p A.val B.val i.val u.val (j.val-i.val) (v.val-u.val)
    hm hk hp hsize hpup A.isLt B.isLt hδ hε
    (by have := j.isLt; omega) (by have := v.isLt; omega)
    (by have := j.isLt; omega) (by have := v.isLt; omega) hne'

end Erdos488.Geometry.SeparatedDistances.FixedDimension
