import Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5CircleMacro

namespace Erdos670EpsilonFamily
open scoped BigOperators Matrix
open Matrix Erdos488.Geometry.SeparatedDistances.FixedDimension
open Erdos488.Geometry.SeparatedDistances
open Erdos488.Geometry.SeparatedDistances.FixedDimension.Pass5

/-! Private epsilon-family formalization. Macro shortening T is independent
of the digit-completion radius R. Imported foundations are unchanged. -/

theorem colex_two_circle_macro_exists {n : ℕ} (hn : 1 ≤ n) {K : ℝ}
    (hK : 10 ≤ K) (hlarge : 16384*(harmonic (n+2) : ℝ)^2 ≤ K)
    (hnK : (n+1 : ℕ) ≤ K) (S T R s θ k : ℝ)
    (hr : (T/S)^2 ≤ K^2/16) (hc : 1 ≤ s*k)
    (hR : 7056*(s/θ)^2*(s*k)^2*(K+(n+1 : ℕ)) ≤ R^2) :
    ∃ p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ U : Matrix (Fin (n+1)) (Fin (n+2)) ℝ,
    ∃ W : Matrix (Fin (n+2)) (Fin (n+2)) ℝ,
      (∀ A B, A ≠ B → ‖p A-p B‖^2 = (colexDistance K A B)^2-2*(T/S)^2) ∧
      (Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => R^2)) ∧
      (∀ A B,
        (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
          (s/θ)*((if B.val < A.val then colexDistance K A B else 0) +
            (s*k)*(if A.val < B.val then colexDistance K A B else 0))) := by
  obtain ⟨p, _, hpd, _⟩ := flattened_colex_all_anchor_potentials hn hK hlarge ((T/S)^2) hr
  obtain ⟨F, G, hFproj, hGproj, hFbudget, hGbudget⟩ :=
    sourceFineCoarseCoefficients_exist hn hK hlarge ((T/S)^2) hr hnK p hpd
  let U := circleDirectionMatrix s θ k F G
  obtain ⟨W, hW⟩ := circle_completion_factor U R
    (circleDirectionMatrix_budget (by linarith : 0 ≤ K) hc F G hFbudget hGbudget hR)
  refine ⟨p, U, W, ?_, hW, ?_⟩
  · intro A B hAB
    have h := hpd B A
    simpa only [offDiagonalShift, Ne.symm hAB, if_false, colexSqData,
      colexDistance_symm K B A] using h
  · intro A B
    change (fun i => (p A-p B) i) ⬝ᵥ (fun i => circleDirection s θ k F G A i) = _
    rw [euclidean_dot_inner]
    exact circleDirection_projection K s θ k p F G hFproj hGproj A B

/-- Natural m-indexed wrapper, preserving the advertised m−1 macro dimension. -/
theorem colex_two_circle_macro_exists_m {m : ℕ} (hm : 3 ≤ m) {K : ℝ}
    (hK : 10 ≤ K) (hlarge : 16384*(harmonic m : ℝ)^2 ≤ K)
    (hmK : (m : ℝ) ≤ K) (S T R s θ k : ℝ)
    (hr : (T/S)^2 ≤ K^2/16) (hc : 1 ≤ s*k)
    (hR : 7056*(s/θ)^2*(s*k)^2*(K+(m : ℝ)) ≤ R^2) :
    ∃ p : Fin m → EuclideanSpace ℝ (Fin (m-1)),
    ∃ U : Matrix (Fin (m-1)) (Fin m) ℝ,
    ∃ W : Matrix (Fin m) (Fin m) ℝ,
      (∀ A B, A ≠ B → ‖p A-p B‖^2 = (circleColexDistance K A B)^2-2*(T/S)^2) ∧
      (Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => R^2)) ∧
      (∀ A B,
        (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
          (s/θ)*((if B.val < A.val then circleColexDistance K A B else 0) +
            (s*k)*(if A.val < B.val then circleColexDistance K A B else 0))) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n+2 := ⟨m-2, by omega⟩
  rw [show n+2-1=n+1 by omega]
  have hn : 1 ≤ n := by omega
  have hnK : (n+1 : ℕ) ≤ K := by push_cast at *; linarith
  have hsmall : 7056*(s/θ)^2*(s*k)^2*(K+(n+1 : ℕ)) ≤ R^2 := by
    calc
      _ ≤ 7056*(s/θ)^2*(s*k)^2*(K+(n+2 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        push_cast
        linarith
      _ ≤ R^2 := hR
  simpa only [circleColexDistance, colexDistance] using colex_two_circle_macro_exists hn hK hlarge hnK S T R s θ k hr hc hsmall


/-- The exact two-circle total shortening. Only the first circle consumes the
incidence/digit completion budget. -/
theorem colex_two_radius_macro_exists_m {m : ℕ} (hm : 3 ≤ m) {K : ℝ}
    (hK : 10 ≤ K) (hlarge : 16384*(harmonic m : ℝ)^2 ≤ K)
    (hmK : (m : ℝ) ≤ K) (S R₀ R₁ s θ k : ℝ)
    (hr : (R₀^2+R₁^2)/S^2 ≤ K^2/16) (hc : 1 ≤ s*k)
    (hR : 7056*(s/θ)^2*(s*k)^2*(K+(m : ℝ)) ≤ R₀^2) :
    ∃ p : Fin m → EuclideanSpace ℝ (Fin (m-1)),
    ∃ U : Matrix (Fin (m-1)) (Fin m) ℝ,
    ∃ W : Matrix (Fin m) (Fin m) ℝ,
      (∀ A B, A ≠ B → ‖p A-p B‖^2 =
        (circleColexDistance K A B)^2-2*((R₀^2+R₁^2)/S^2)) ∧
      (Uᵀ*U+Wᵀ*W = Matrix.diagonal (fun _ => R₀^2)) ∧
      (∀ A B,
        (fun i => (p A-p B) i) ⬝ᵥ (fun i => U i A) =
          (s/θ)*((if B.val < A.val then circleColexDistance K A B else 0) +
            (s*k)*(if A.val < B.val then circleColexDistance K A B else 0))) := by
  have he : (Real.sqrt (R₀^2+R₁^2)/S)^2 = (R₀^2+R₁^2)/S^2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  obtain ⟨p, U, W, hp, hW, hproj⟩ := colex_two_circle_macro_exists_m hm hK hlarge hmK
    S (Real.sqrt (R₀^2+R₁^2)) R₀ s θ k (by rw [he]; exact hr) hc hR
  refine ⟨p, U, W, ?_, hW, hproj⟩
  intro A B hAB
  rw [hp A B hAB, he]

#print axioms colex_two_circle_macro_exists_m
#print axioms colex_two_radius_macro_exists_m

end Erdos670EpsilonFamily
