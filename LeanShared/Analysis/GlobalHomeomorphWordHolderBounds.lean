module
public import LeanShared.Analysis.GlobalWordNarrowProjectionBounds
public import LeanShared.Analysis.UniformHolderDerivativeComposition

/-! Uniform first derivative and Holder bounds for the literal full word
and its actual inverse follow from the ordinary one-step bounds. Constants
are constructed recursively before the parameter choices and the word. -/
public noncomputable section
open Set
namespace LeanShared.GlobalHomeomorphWordHolderBounds
open OrthogonalRateGlobalWordFakeLeaves

@[expose] def holderConstant (K L α : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => (L*(K^n)^α*K^n+K*holderConstant K L α n)+
    (holderConstant K L α n*K^α*K+K^n*L)

theorem holderConstant_nonneg {K L α : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ holderConstant K L α n := by
  induction n with
  | zero => rfl
  | succ n ih => dsimp only [holderConstant];positivity

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem prefix_bounds (H : G → E ≃ₜ E) (smooth : ∀ g, ContDiff ℝ 1 (H g))
    (inverseSmooth : ∀ g, ContDiff ℝ 1 (H g).symm)
    {K L α : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (forwardBound : ∀ g x, ‖fderiv ℝ (H g) x‖ ≤ K)
    (inverseBound : ∀ g x, ‖fderiv ℝ (H g).symm x‖ ≤ K)
    (forwardHolder : ∀ g x y, ‖fderiv ℝ (H g) x-fderiv ℝ (H g) y‖ ≤ L*‖x-y‖^α)
    (inverseHolder : ∀ g x y, ‖fderiv ℝ (H g).symm x-fderiv ℝ (H g).symm y‖ ≤ L*‖x-y‖^α)
    {N : ℕ} (word : Fin N → G) (k : ℕ) (within : k ≤ N) :
    (∀ x, ‖fderiv ℝ (prefixHomeomorph H word k) x‖ ≤ K^k) ∧
    (∀ x, ‖fderiv ℝ (prefixHomeomorph H word k).symm x‖ ≤ K^k) ∧
    (∀ x y, ‖fderiv ℝ (prefixHomeomorph H word k) x-fderiv ℝ (prefixHomeomorph H word k) y‖ ≤
      holderConstant K L α k*‖x-y‖^α) ∧
    ∀ x y, ‖fderiv ℝ (prefixHomeomorph H word k).symm x-fderiv ℝ (prefixHomeomorph H word k).symm y‖ ≤
      holderConstant K L α k*‖x-y‖^α := by
  induction k with
  | zero =>
    refine ⟨?_,?_,?_,?_⟩
    · intro x
      change ‖fderiv ℝ (id : E → E) x‖ ≤ 1
      rw [fderiv_id]
      exact ContinuousLinearMap.norm_id_le
    · intro x
      change ‖fderiv ℝ (id : E → E) x‖ ≤ 1
      rw [fderiv_id]
      exact ContinuousLinearMap.norm_id_le
    · intro x y
      rw [holderConstant,zero_mul]
      change ‖fderiv ℝ (id : E → E) x-fderiv ℝ (id : E → E) y‖ ≤ 0
      simp only [fderiv_id,sub_self,norm_zero,le_refl]
    · intro x y
      rw [holderConstant,zero_mul]
      change ‖fderiv ℝ (id : E → E) x-fderiv ℝ (id : E → E) y‖ ≤ 0
      simp only [fderiv_id,sub_self,norm_zero,le_refl]
  | succ k ih =>
    have hk : k<N := within
    obtain ⟨oldForward,oldInverse,oldHolder,oldInverseHolder⟩ := ih (Nat.le_of_lt hk)
    have oldSmooth := GlobalWordNarrowProjectionBounds.prefix_contDiff H smooth word k
    have oldInverseSmooth := GlobalWordNarrowProjectionBounds.prefix_inverse_contDiff H inverseSmooth word k
    have hPower : 0 ≤ K^k := pow_nonneg hK _
    have hConstant : 0 ≤ holderConstant K L α k := holderConstant_nonneg hK hL k
    have forward := UniformHolderDerivativeComposition.bound (K := univ) (V := univ)
      convex_univ (subset_univ _) (fun x _ => (smooth (word ⟨k,hk⟩)).differentiable one_ne_zero x)
      (fun x _ => oldSmooth.differentiable one_ne_zero x) hα hK hPower hL hConstant
      (fun x _ => forwardBound _ x) (fun x _ => oldForward x)
      (fun x _ y _ => forwardHolder _ x y) (fun x _ y _ => oldHolder x y)
    have backward := UniformHolderDerivativeComposition.bound (K := univ) (V := univ)
      convex_univ (subset_univ _) (fun x _ => oldInverseSmooth.differentiable one_ne_zero x)
      (fun x _ => (inverseSmooth (word ⟨k,hk⟩)).differentiable one_ne_zero x) hα hPower hK hConstant hL
      (fun x _ => oldInverse x) (fun x _ => inverseBound _ x)
      (fun x _ y _ => oldInverseHolder x y) (fun x _ y _ => inverseHolder _ x y)
    rw [prefixHomeomorph,dite_eq_left hk]
    refine ⟨?_,?_,?_,?_⟩
    · intro x
      change ‖fderiv ℝ ((H (word ⟨k,hk⟩) : E → E) ∘ (prefixHomeomorph H word k : E → E)) x‖ ≤ K^(k+1)
      simpa only [pow_succ,mul_comm] using forward.1 x (mem_univ x)
    · intro x
      change ‖fderiv ℝ (((prefixHomeomorph H word k).symm : E → E) ∘ ((H (word ⟨k,hk⟩)).symm : E → E)) x‖ ≤ K^(k+1)
      simpa only [pow_succ] using backward.1 x (mem_univ x)
    · intro x y
      apply (forward.2 x (mem_univ x) y (mem_univ y)).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      exact le_add_of_nonneg_right (by positivity)
    · intro x y
      apply (backward.2 x (mem_univ x) y (mem_univ y)).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      exact le_add_of_nonneg_left (by positivity)

end LeanShared.GlobalHomeomorphWordHolderBounds
