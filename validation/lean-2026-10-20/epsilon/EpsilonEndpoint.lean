import ReciprocalRounding
import ExactNEmbedding

namespace EuclideanEpsilonResearch

/-- The exact finite construction obligation. This definition is not an assertion
that the construction has been supplied; the endpoint below takes its proof. -/
def EpsilonClusterSource : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1/8 → ∀ m k : ℕ,
    1024/ξ ≤ (m:ℝ) → 2 ≤ k →
    ∃ P : Fin (m*k) → EuclideanSpace ℝ (Fin (5*m-1)),
      (∀ a b, a ≠ b → 1 ≤ dist (P a) (P b)) ∧
      StrictSeparatedConfiguration P ∧
      (∀ a b, dist (P a) (P b) ≤ (1/2+4*ξ)*((m:ℝ)*(k:ℝ))^2)

/-- Conditional packaging only: all-n epsilon quantifiers follow from the exact
finite construction source, reciprocal rounding and isometric deletion/padding. -/
theorem epsilon_all_n_of_cluster_sources (hsource : EpsilonClusterSource)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1/2)
    (n : ℕ) (hn : 4*⌈(8192:ℝ)/ε⌉₊ ≤ n) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin (10*⌈(8192:ℝ)/ε⌉₊-1)),
      Function.Injective Q ∧
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      StrictSeparatedConfiguration Q ∧
      (∀ a b c d, a ≠ b → c ≠ d → ¬ ((a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
        1 < |dist (Q a) (Q b)-dist (Q c) (Q d)|) ∧
      (∀ a b, dist (Q a) (Q b) < (1/2+ε)*(n:ℝ)^2) ∧
      Metric.diam (Set.range Q) < (1/2+ε)*(n:ℝ)^2 := by
  let ξ := ε/8
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξ8 : ξ ≤ 1/8 := by dsimp [ξ]; linarith
  let m₀ := ⌈(8192:ℝ)/ε⌉₊
  have hbudget : 0 < m₀ ∧ (1024:ℝ)/ξ ≤ (m₀:ℝ) ∧ 1/(m₀:ℝ) ≤ ξ/1024 := by
    simpa only [ξ,epsilon_ceil_identity] using epsilon_ceil_budget ξ hξ
  have hn0 : 0 < n := by change 4*m₀ ≤ n at hn; omega
  let k := n/m₀
  let m := (n+k-1)/k
  obtain ⟨hk,hmlo,hmhi,hsize,hsurplus,hkbound⟩ := reciprocal_rounding n m₀ hbudget.1 hn
  change 4 ≤ k at hk
  change m₀ ≤ m at hmlo
  change m ≤ 2*m₀ at hmhi
  change n ≤ m*k at hsize
  change m*k < n+k at hsurplus
  change m₀*k ≤ n at hkbound
  have hmacro : 1024/ξ ≤ (m:ℝ) := hbudget.2.1.trans (by exact_mod_cast hmlo)
  obtain ⟨P,hmin,hsep,hdiam⟩ := hsource ξ hξ hξ8 m k hmacro (by omega)
  have hround := epsilon_rounded_diameter ξ n m k m₀ hξ hξ8 hn0 hbudget.1
    hsurplus hkbound hbudget.2.2
  have hfinal := mul_lt_mul_of_pos_right (epsilon_final_coefficient ε hε)
    (sq_pos_of_pos (show (0:ℝ) < n by exact_mod_cast hn0))
  have hcap : (1/2+4*ξ)*((m:ℝ)*(k:ℝ))^2 < (1/2+ε)*(n:ℝ)^2 :=
    hround.trans hfinal
  obtain ⟨Q,hinj,hminQ,hsepQ,_,hpairQ,hdiamQ⟩ := exact_n_delete_pad hn0 hsize
    (epsilon_dimension_padding m m₀ hmhi) P hmin hsep
    ((1/2+4*ξ)*((m:ℝ)*(k:ℝ))^2) ((1/2+ε)*(n:ℝ)^2) hdiam hcap
  exact ⟨Q,hinj,hminQ,hsepQ,(strictSeparatedConfiguration_iff_four_points Q).1 hsepQ,hpairQ,hdiamQ⟩

#print axioms epsilon_all_n_of_cluster_sources

/-- The sharper internal xi endpoint, padded to any sufficient dimension. -/
theorem xi_all_n_of_cluster_sources (hsource : EpsilonClusterSource)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ8 : ξ ≤ 1/8) (n d : ℕ)
    (hn : 4*⌈(1024:ℝ)/ξ⌉₊ ≤ n) (hd : 10*⌈(1024:ℝ)/ξ⌉₊-1 ≤ d) :
    ∃ Q : Fin n → EuclideanSpace ℝ (Fin d),
      Function.Injective Q ∧
      (∀ a b, a ≠ b → 1 ≤ dist (Q a) (Q b)) ∧
      StrictSeparatedConfiguration Q ∧
      (∀ a b, dist (Q a) (Q b) < (1/2+5*ξ)*(n:ℝ)^2) ∧
      Metric.diam (Set.range Q) < (1/2+5*ξ)*(n:ℝ)^2 := by
  let m₀ := ⌈(1024:ℝ)/ξ⌉₊
  have hbudget := epsilon_ceil_budget ξ hξ
  have hn0 : 0 < n := by omega
  let k := n/m₀
  let m := (n+k-1)/k
  obtain ⟨hk,hmlo,hmhi,hsize,hsurplus,hkbound⟩ := reciprocal_rounding n m₀ hbudget.1 hn
  change 4 ≤ k at hk
  change m₀ ≤ m at hmlo
  change m ≤ 2*m₀ at hmhi
  change n ≤ m*k at hsize
  change m*k < n+k at hsurplus
  change m₀*k ≤ n at hkbound
  have hmacro : 1024/ξ ≤ (m:ℝ) := hbudget.2.1.trans (by exact_mod_cast hmlo)
  obtain ⟨P,hmin,hsep,hdiam⟩ := hsource ξ hξ hξ8 m k hmacro (by omega)
  have hround := epsilon_rounded_diameter ξ n m k m₀ hξ hξ8 hn0 hbudget.1
    hsurplus hkbound hbudget.2.2
  have hdim : 5*m-1 ≤ d := (epsilon_dimension_padding m m₀ hmhi).trans hd
  obtain ⟨Q,hinj,hminQ,hsepQ,_,hpairQ,hdiamQ⟩ := exact_n_delete_pad hn0 hsize
    hdim P hmin hsep ((1/2+4*ξ)*((m:ℝ)*(k:ℝ))^2) ((1/2+5*ξ)*(n:ℝ)^2) hdiam hround
  exact ⟨Q,hinj,hminQ,hsepQ,hpairQ,hdiamQ⟩

/-- Natural ceiling bounds behind the uniform dimension/size corollary. -/
theorem uniform_epsilon_budget (d n : ℕ) (hd : 163840 ≤ d) (hn : 65536 ≤ n) :
    let ξ := max ((20480:ℝ)/(d:ℝ)) ((8192:ℝ)/(n:ℝ))
    0 < ξ ∧ ξ ≤ 1/8 ∧ 4*⌈(1024:ℝ)/ξ⌉₊ ≤ n ∧ 10*⌈(1024:ℝ)/ξ⌉₊-1 ≤ d ∧
    5*ξ ≤ (102400:ℝ)/(d:ℝ)+(40960:ℝ)/(n:ℝ) := by
  let ξ := max ((20480:ℝ)/(d:ℝ)) ((8192:ℝ)/(n:ℝ))
  change 0 < ξ ∧ ξ ≤ 1/8 ∧ 4*⌈(1024:ℝ)/ξ⌉₊ ≤ n ∧ 10*⌈(1024:ℝ)/ξ⌉₊-1 ≤ d ∧ _
  have hd' : (163840:ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (65536:ℝ) ≤ n := by exact_mod_cast hn
  have hd0 : (0:ℝ) < d := by linarith
  have hn0 : (0:ℝ) < n := by linarith
  have hxd : (20480:ℝ)/(d:ℝ) ≤ ξ := le_max_left _ _
  have hxn : (8192:ℝ)/(n:ℝ) ≤ ξ := le_max_right _ _
  have hξ : 0 < ξ := (div_pos (by norm_num) hd0).trans_le hxd
  have hξ8 : ξ ≤ 1/8 := by
    apply max_le
    · apply (div_le_iff₀ hd0).2
      linarith
    · apply (div_le_iff₀ hn0).2
      linarith
  have hcd : (1024:ℝ)/ξ ≤ (d:ℝ)/20 := by
    have hh := (div_le_iff₀ hd0).1 hxd
    apply (div_le_iff₀ hξ).2
    nlinarith
  have hcn : (1024:ℝ)/ξ ≤ (n:ℝ)/8 := by
    have hh := (div_le_iff₀ hn0).1 hxn
    apply (div_le_iff₀ hξ).2
    nlinarith
  have hc : (⌈(1024:ℝ)/ξ⌉₊:ℝ) < (1024:ℝ)/ξ+1 := Nat.ceil_lt_add_one (by positivity)
  have hsize : 4*⌈(1024:ℝ)/ξ⌉₊ ≤ n := by
    have : (4:ℝ)*(⌈(1024:ℝ)/ξ⌉₊:ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hdim : 10*⌈(1024:ℝ)/ξ⌉₊-1 ≤ d := by
    have : (10:ℝ)*(⌈(1024:ℝ)/ξ⌉₊:ℝ) ≤ d := by linarith
    have hh : 10*⌈(1024:ℝ)/ξ⌉₊ ≤ d := by exact_mod_cast this
    omega
  have hsum : ξ ≤ (20480:ℝ)/(d:ℝ)+(8192:ℝ)/(n:ℝ) := by
    apply max_le
    · have : (0:ℝ) ≤ 8192/(n:ℝ) := by positivity
      linarith
    · have : (0:ℝ) ≤ 20480/(d:ℝ) := by positivity
      linarith
  refine ⟨hξ,hξ8,hsize,hdim,?_⟩
  have he : (102400:ℝ)/(d:ℝ)+(40960:ℝ)/(n:ℝ) =
      5*((20480:ℝ)/(d:ℝ)+(8192:ℝ)/(n:ℝ)) := by ring
  rw [he]
  linarith

/-- Uniform large-dimension, large-size consequence of the same construction. -/
theorem uniform_all_n_of_cluster_sources (hsource : EpsilonClusterSource)
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
        (1/2+(102400:ℝ)/(d:ℝ)+(40960:ℝ)/(n:ℝ))*(n:ℝ)^2 := by
  let ξ := max ((20480:ℝ)/(d:ℝ)) ((8192:ℝ)/(n:ℝ))
  obtain ⟨hξ,hξ8,hsize,hdim,hcoeff⟩ := uniform_epsilon_budget d n hd hn
  obtain ⟨Q,hinj,hmin,hsep,hpair,hdiam⟩ := xi_all_n_of_cluster_sources hsource ξ hξ hξ8 n d hsize hdim
  have hb : (1/2+5*ξ)*(n:ℝ)^2 ≤
      (1/2+(102400:ℝ)/(d:ℝ)+(40960:ℝ)/(n:ℝ))*(n:ℝ)^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg (n:ℝ))
    linarith
  exact ⟨Q,hinj,hmin,hsep,(strictSeparatedConfiguration_iff_four_points Q).1 hsep,
    fun a b => (hpair a b).trans_le hb,hdiam.trans_le hb⟩

#print axioms xi_all_n_of_cluster_sources
#print axioms uniform_epsilon_budget
#print axioms uniform_all_n_of_cluster_sources
end EuclideanEpsilonResearch
