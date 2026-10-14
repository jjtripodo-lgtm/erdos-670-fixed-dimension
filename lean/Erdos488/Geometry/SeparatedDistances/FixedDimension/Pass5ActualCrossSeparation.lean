import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CrossSeparation
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5SpectrumParameters
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5Ruler
import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleMacro
import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceActualCrossMetric

/-! Concrete scalar cross spectrum with actual fifth-pass ruler digits,
actual colex macro labels, and every numerical gate discharged. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Zero-based colex code with the direct m-vertex indexing of the circles. -/
def pass5PairCode {m : ℕ} (A B : Fin m) : ℕ := Nat.choose B.val 2+A.val

theorem pass5PairCode_lt_choose {m : ℕ} (A B : Fin m) (hAB : A.val < B.val) :
    pass5PairCode A B < m.choose 2 := by
  have hstep : Nat.choose (B.val+1) 2 = Nat.choose B.val 2+B.val := by
    rw [Nat.choose_succ_succ]
    simp [Nat.choose_one_right, add_comm]
  have hchoose : Nat.choose (B.val+1) 2 ≤ Nat.choose m 2 :=
    Nat.choose_le_choose 2 (by omega)
  unfold pass5PairCode
  omega

theorem pass5PairCode_ordered_injective {m : ℕ} (A B C D : Fin m)
    (hAB : A.val < B.val) (hCD : C.val < D.val)
    (heq : pass5PairCode A B = pass5PairCode C D) : A=C ∧ B=D := by
  have hh : sourcePairCode A.castSucc B.castSucc = sourcePairCode C.castSucc D.castSucc := heq
  obtain ⟨hA,hB⟩ := sourcePairCode_ordered_injective A.castSucc B.castSucc
    C.castSucc D.castSucc hAB hCD hh
  exact ⟨Fin.ext (congrArg (fun x : Fin (m+1) => x.val) hA),
    Fin.ext (congrArg (fun x : Fin (m+1) => x.val) hB)⟩

noncomputable def pass5ColexBaseline {m : ℕ} (k : ℕ) (K : ℝ) (A B : Fin m) : ℝ :=
  pass5Scale k * Pass5.circleColexDistance K A B

theorem pass5ColexBaseline_eq {m : ℕ} (k : ℕ) (K : ℝ) (A B : Fin m)
    (hAB : A.val < B.val) :
    pass5ColexBaseline k K A B = pass5Scale k*(K+(pass5PairCode A B : ℝ)+1) := by
  simp [pass5ColexBaseline, Pass5.circleColexDistance, hAB, pass5PairCode,
    colexLabel, Nat.cast_add, add_assoc]

theorem pass5ColexBaseline_lower {m k : ℕ} (hk : 2 ≤ k) (K : ℝ) (A B : Fin m)
    (hAB : A.val < B.val) :
    pass5Scale k*(K+1) ≤ pass5ColexBaseline k K A B := by
  rw [pass5ColexBaseline_eq k K A B hAB]
  apply mul_le_mul_of_nonneg_left _ (pass5_scale_pos hk).le
  have : (0 : ℝ) ≤ (pass5PairCode A B : ℝ) := by positivity
  linarith

theorem pass5ColexBaseline_upper {m k : ℕ} (hk : 2 ≤ k) (K : ℝ) (A B : Fin m)
    (hAB : A.val < B.val) :
    pass5ColexBaseline k K A B ≤ pass5Scale k*(K+(m.choose 2 : ℝ)) := by
  rw [pass5ColexBaseline_eq k K A B hAB]
  apply mul_le_mul_of_nonneg_left _ (pass5_scale_pos hk).le
  have hh : (pass5PairCode A B : ℝ)+1 ≤ (m.choose 2 : ℝ) := by
    exact_mod_cast pass5PairCode_lt_choose A B hAB
  linarith

theorem pass5ColexBaseline_pos {m k : ℕ} (hk : 2 ≤ k) (K : ℝ) (hK : 0 ≤ K)
    (A B : Fin m) (hAB : A.val < B.val) : 0 < pass5ColexBaseline k K A B := by
  have h := pass5ColexBaseline_lower hk K A B hAB
  have hp : 0 < pass5Scale k*(K+1) := mul_pos (pass5_scale_pos hk) (by linarith)
  linarith

theorem pass5ColexBaseline_separated {m k : ℕ} (hk : 2 ≤ k) (K : ℝ)
    (A B C D : Fin m) (hAB : A.val < B.val) (hCD : C.val < D.val)
    (hne : (A,B) ≠ (C,D)) :
    pass5Scale k ≤ |pass5ColexBaseline k K A B-pass5ColexBaseline k K C D| := by
  rw [pass5ColexBaseline_eq k K A B hAB, pass5ColexBaseline_eq k K C D hCD]
  apply pass5_integer_baselines_separated _ _ _ _ (pass5_scale_pos hk).le
  intro hh
  obtain ⟨rfl,rfl⟩ := pass5PairCode_ordered_injective A B C D hAB hCD hh
  exact hne rfl

@[simp] theorem pass5H_eq_halfSpan (k : ℕ) : pass5H k = pass5HalfSpan k := by
  unfold pass5H pass5HalfSpan
  norm_num

@[simp] theorem pass5DigitBudget_concrete (k : ℕ) :
    pass5DigitBudget (9/8 : ℝ) (pass5HalfSpan k) k = pass5ConcreteDigitBudget k := rfl

/-- The concrete scalar distance attached to each cross edge. -/
noncomputable def pass5CrossLength {m : ℕ} (p k : ℕ)
    (A B : Fin m) (i j : ℕ) : ℝ :=
  pass5Phi (pass5ColexBaseline k (pass5Offset m : ℝ) A B)
    (pass5CrossDigit (9/8) k (pass5Digit p k A.val) (pass5Digit p k B.val) i j)

/-- Uniform displacement for every concrete cross edge. -/
theorem pass5CrossLength_displacement {m p k : ℕ}
    (hm : 18177 ≤ m) (hp : 0 < p) (hk : 2 ≤ k)
    (A B : Fin m) (hAB : A.val < B.val) (i j : ℕ) (hi : i < k) (hj : j < k) :
    |pass5CrossLength p k A B i j-pass5ColexBaseline k (pass5Offset m : ℝ) A B| ≤
      pass5ConcreteDigitBudget k/pass5Tau m := by
  have ht := pass5Tau_bounds m hm
  have hf : |pass5Digit p k A.val i| ≤ pass5HalfSpan k := by
    simpa using pass5Digit_abs_le p k A.val i hp hi
  have hg : |pass5Digit p k B.val j| ≤ pass5HalfSpan k := by
    simpa using pass5Digit_abs_le p k B.val j hp hj
  have hb := pass5CrossDigit_bound (9/8) (pass5HalfSpan k) k
    (pass5Digit p k A.val) (pass5Digit p k B.val) i j (by norm_num) hf hg
  have hd := pass5_digit_domain hm hk (pass5ColexBaseline_lower hk (pass5Offset m : ℝ) A B hAB)
  simpa only [pass5CrossLength, pass5DigitBudget_concrete] using
    pass5Phi_displacement (pass5ColexBaseline k (pass5Offset m : ℝ) A B)
      (pass5Tau m) (pass5DigitBudget (9/8) (pass5HalfSpan k) k) _
      (pass5ColexBaseline_pos hk _ (by positivity) A B hAB)
      (by linarith : 0 < pass5Tau m) ht.2.le hb (by simpa using hd)

/-- Every pair of distinct concrete cross edges is separated; only m, p, k
admissibility remains, with no unproved scalar separation hypothesis. -/
theorem pass5_concrete_cross_pairs_separated {m p k : ℕ}
    (hm : 18177 ≤ m) (hp : 0 < p) (hk : 2 ≤ k)
    (A B C D : Fin m) (hAB : A.val < B.val) (hCD : C.val < D.val)
    (i j u v : Fin k) (hne : (A,B,i,j) ≠ (C,D,u,v)) :
    1 ≤ |pass5CrossLength p k A B i.val j.val-pass5CrossLength p k C D u.val v.val| := by
  have ht := pass5Tau_bounds m hm
  have hf (A : Fin m) (i : ℕ) (hi : i < k) :
      |pass5Digit p k A.val i| ≤ pass5HalfSpan k := by
    simpa using pass5Digit_abs_le p k A.val i hp hi
  have hfstep (A : Fin m) (i : ℕ) (hi : i+1 < k) :
      (853589/960000 : ℝ) ≤ pass5Digit p k A.val (i+1)-pass5Digit p k A.val i :=
    (pass5Digit_step p k A.val i hp hi).le
  have hν := pass5ColexBaseline_pos hk (pass5Offset m : ℝ) (by positivity) A B hAB
  have hμ := pass5ColexBaseline_pos hk (pass5Offset m : ℝ) (by positivity) C D hCD
  have hbν := pass5_digit_domain hm hk (pass5ColexBaseline_lower hk (pass5Offset m : ℝ) A B hAB)
  have hbμ := pass5_digit_domain hm hk (pass5ColexBaseline_lower hk (pass5Offset m : ℝ) C D hCD)
  apply pass5_cross_pairs_separated (fun A : Fin m => pass5Digit p k A.val)
    (pass5ColexBaseline k (pass5Offset m : ℝ)) (9/8) (pass5Tau m)
    (pass5HalfSpan k) (853589/960000) (pass5Scale k) k
    (by omega) (by norm_num) (by linarith) ht.2.le (by norm_num) hf hfstep
    (pass5_fine_gap hm) (pass5_carry_gap hm hk) (by simpa using pass5_macro_gap hm hk)
    A B C D hν hμ (by simpa using hbν) (by simpa using hbμ)
    (pass5ColexBaseline_separated hk _ A B C D hAB hCD) i.isLt j.isLt u.isLt v.isLt
  intro heq
  apply hne
  have hA : A=C := congrArg Prod.fst heq
  have hB : B=D := congrArg (fun q => q.2.1) heq
  have hi : i.val=u.val := congrArg (fun q => q.2.2.1) heq
  have hj : j.val=v.val := congrArg (fun q => q.2.2.2) heq
  simp only [hA,hB,Fin.ext hi,Fin.ext hj]

#print axioms pass5_concrete_cross_pairs_separated
#print axioms pass5CrossLength_displacement
end Erdos488.Geometry.SeparatedDistances.FixedDimension
