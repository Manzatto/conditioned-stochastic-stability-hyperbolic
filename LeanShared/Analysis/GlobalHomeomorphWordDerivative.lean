module
public import LeanShared.Analysis.HomeomorphDerivativeEquivalence
public import LeanShared.Analysis.OrthogonalRateGlobalWordFakeLeaves
public import LeanShared.Analysis.FiniteDerivativeWord
public import LeanShared.Analysis.ProductRateWordRadialBounds

/-! Actual spatial derivatives at the literal prefix states form an
invertible matrix list whose chronological product is exactly the spatial
derivative of the global homeomorphism word. -/
public noncomputable section
namespace LeanShared.GlobalHomeomorphWordDerivative
open CylinderPrincipalCoefficient ProductRateWordRadialBounds
variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem wordEquiv_append_singleton (blocks : List (E ≃L[ℝ] E)) (B : E ≃L[ℝ] E) :
    wordEquiv (blocks ++ [B]) = (wordEquiv blocks).trans B := by
  apply DFunLike.ext
  intro z
  induction blocks generalizing z with
  | nil => rfl
  | cons A tail ih => exact ih (A z)

@[expose] def blocks (H : G → E ≃ₜ E) (smooth : ∀ g, Differentiable ℝ (H g))
    (inverseSmooth : ∀ g, Differentiable ℝ (H g).symm)
    {N : ℕ} (word : Fin N → G) (x : E) : ℕ → List (E ≃L[ℝ] E)
  | 0 => []
  | k+1 => if hk : k<N then blocks H smooth inverseSmooth word x k ++
      [HomeomorphDerivativeEquivalence.derivative (H (word ⟨k,hk⟩))
        (smooth _) (inverseSmooth _) (prefixOrbit (fun g => (H g : E → E)) word k x)]
    else blocks H smooth inverseSmooth word x k

theorem blocks_length (H : G → E ≃ₜ E) (smooth : ∀ g, Differentiable ℝ (H g))
    (inverseSmooth : ∀ g, Differentiable ℝ (H g).symm)
    {N : ℕ} (word : Fin N → G) (x : E) (k : ℕ) (within : k ≤ N) :
    (blocks H smooth inverseSmooth word x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k<N := within
    simp only [blocks,dite_eq_left hk,List.length_append,List.length_singleton,ih (Nat.le_of_lt hk)]

theorem mem_blocks (H : G → E ≃ₜ E) (smooth : ∀ g, Differentiable ℝ (H g))
    (inverseSmooth : ∀ g, Differentiable ℝ (H g).symm)
    {N : ℕ} (word : Fin N → G) (x : E) (k : ℕ)
    (B : E ≃L[ℝ] E) (member : B ∈ blocks H smooth inverseSmooth word x k) :
    ∃ j : Fin N, B = HomeomorphDerivativeEquivalence.derivative (H (word j))
      (smooth _) (inverseSmooth _) (prefixOrbit (fun g => (H g : E → E)) word j.val x) := by
  induction k with
  | zero => simp only [blocks,List.not_mem_nil] at member
  | succ k ih =>
    by_cases hk : k<N
    · rw [blocks,dite_eq_left hk] at member
      rcases List.mem_append.mp member with old | last
      · exact ih old
      · exact ⟨⟨k,hk⟩,List.mem_singleton.mp last⟩
    · rw [blocks,dite_eq_right hk] at member
      exact ih member

theorem word_derivative (H : G → E ≃ₜ E) (smooth : ∀ g, Differentiable ℝ (H g))
    (inverseSmooth : ∀ g, Differentiable ℝ (H g).symm)
    {N : ℕ} (word : Fin N → G) (x : E) (k : ℕ) :
    (wordEquiv (blocks H smooth inverseSmooth word x k)).toContinuousLinearMap =
      fderiv ℝ (prefixOrbit (fun g => (H g : E → E)) word k) x := by
  rw [FiniteDerivativeWord.fderiv_prefixOrbit _ smooth]
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k<N
    · rw [blocks,dite_eq_left hk,wordEquiv_append_singleton]
      change (HomeomorphDerivativeEquivalence.derivative (H (word ⟨k,hk⟩))
        (smooth _) (inverseSmooth _) (prefixOrbit (fun g => (H g : E → E)) word k x)).toContinuousLinearMap.comp
        (wordEquiv (blocks H smooth inverseSmooth word x k)).toContinuousLinearMap = _
      rw [HomeomorphDerivativeEquivalence.derivative_coe,ih]
      simp only [FiniteDerivativeWord.prefixDerivative,dite_eq_left hk]
    · simp only [blocks,FiniteDerivativeWord.prefixDerivative,dite_eq_right hk,ih]

end LeanShared.GlobalHomeomorphWordDerivative
