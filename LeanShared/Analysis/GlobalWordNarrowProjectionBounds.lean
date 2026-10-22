module
public import LeanShared.Analysis.GlobalHomeomorphWordDerivative
public import LeanShared.Analysis.OrthogonalRateWordNarrowCones
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Narrow source/kernel and stable-preimage slopes for the actual derivative
of an actual chronological global word, with no derivative packet assumed. -/
public noncomputable section
open Set
namespace LeanShared.GlobalWordNarrowProjectionBounds
open OrthogonalProductCoordinates ProductRateWordRadialBounds OrthogonalRateGlobalWordFakeLeaves
variable {G X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem prefix_contDiff (H : G → E ≃ₜ E) (smooth : ∀ g, ContDiff ℝ 1 (H g))
    {N : ℕ} (word : Fin N → G) (k : ℕ) : ContDiff ℝ 1 (prefixHomeomorph H word k) := by
  induction k with
  | zero => exact contDiff_id
  | succ k ih =>
    by_cases hk : k<N
    · rw [prefixHomeomorph,dite_eq_left hk]
      exact (smooth _).comp ih
    · simpa only [prefixHomeomorph,dite_eq_right hk] using ih

omit [FiniteDimensional ℝ E] in
theorem prefix_inverse_contDiff (H : G → E ≃ₜ E) (smooth : ∀ g, ContDiff ℝ 1 (H g).symm)
    {N : ℕ} (word : Fin N → G) (k : ℕ) : ContDiff ℝ 1 (prefixHomeomorph H word k).symm := by
  induction k with
  | zero => exact contDiff_id
  | succ k ih =>
    by_cases hk : k<N
    · rw [prefixHomeomorph,dite_eq_left hk]
      exact ih.comp (smooth _)
    · simpa only [prefixHomeomorph,dite_eq_right hk] using ih

set_option maxHeartbeats 1000000 in
theorem exists_uniform_budget {q : ℝ} (positiveQ : 0<q) (contractingQ : q<1)
    (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (H : G→E≃ₜE)
      (smooth : ∀ g, ContDiff ℝ 1 (H g)) (inverseSmooth : ∀ g, ContDiff ℝ 1 (H g).symm)
      (U : G→X≃L[ℝ]X) (S : G→Y→L[ℝ]Y),
      (∀ g, ‖S g‖≤q) → (∀ g, ‖(U g).symm.toContinuousLinearMap‖≤q) →
      (∀ g x, ‖fderiv ℝ (H g) x-transport dimension ((U g).toContinuousLinearMap.prodMap (S g))‖≤ε) →
      ∀ {N : ℕ} (word : Fin N→G) (x : E) (R : E→L[ℝ]E),
      ‖R-secondProjection dimension‖≤(1/64:ℝ) →
      let W := prefixHomeomorph H word N
      let D := HomeomorphDerivativeEquivalence.derivative W
        ((prefix_contDiff H smooth word N).differentiable one_ne_zero)
        ((prefix_inverse_contDiff H inverseSmooth word N).differentiable one_ne_zero) x
      (∀ v : (secondProjection dimension).range.comap D.toLinearMap,
        ‖firstProjection dimension (v:E)‖≤(1/8:ℝ)*‖secondProjection dimension (v:E)‖) ∧
      ∀ v : R.ker, ‖secondProjection dimension (D v)‖≤(1/8:ℝ)*‖firstProjection dimension (D v)‖ := by
  obtain ⟨ε,positiveε,narrow⟩ := OrthogonalRateWordNarrowCones.exists_uniform_budget positiveQ contractingQ dimension
  refine ⟨ε,positiveε,?_⟩
  intro H smooth inverseSmooth U S stable unstable close N word x R sourceClose
  let differentiable := fun g => (smooth g).differentiable one_ne_zero
  let inverseDifferentiable := fun g => (inverseSmooth g).differentiable one_ne_zero
  let blocks := GlobalHomeomorphWordDerivative.blocks H differentiable inverseDifferentiable word x N
  have near : ∀ B∈blocks, ∃ U : X≃L[ℝ]X, ∃ S : Y→L[ℝ]Y,
      ‖S‖≤q ∧ ‖U.symm.toContinuousLinearMap‖≤q ∧
      ‖B.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S)‖≤ε := by
    intro B member
    obtain ⟨j,rfl⟩ := GlobalHomeomorphWordDerivative.mem_blocks H differentiable inverseDifferentiable word x N B member
    refine ⟨U (word j),S (word j),stable _,unstable _,?_⟩
    rw [HomeomorphDerivativeEquivalence.derivative_coe]
    exact close _ _
  have facts := narrow blocks near
  let W := prefixHomeomorph H word N
  let D := HomeomorphDerivativeEquivalence.derivative W
    ((prefix_contDiff H smooth word N).differentiable one_ne_zero)
    ((prefix_inverse_contDiff H inverseSmooth word N).differentiable one_ne_zero) x
  have actual (v : E) : wordEquiv blocks v=D v := by
    change (wordEquiv blocks).toContinuousLinearMap v=D.toContinuousLinearMap v
    rw [HomeomorphDerivativeEquivalence.derivative_coe]
    have identity : (wordEquiv blocks).toContinuousLinearMap=fderiv ℝ W x := by
      rw [prefixHomeomorph_coe]
      exact GlobalHomeomorphWordDerivative.word_derivative H differentiable inverseDifferentiable word x N
    rw [identity]
  change (∀ v : (secondProjection dimension).range.comap D.toLinearMap, _) ∧ _
  constructor
  · intro v
    have target : firstProjection dimension (D v)=0 := by
      obtain ⟨w,hw⟩ := v.property
      change secondProjection dimension w=D v at hw
      obtain ⟨z,rfl⟩ := (equiv dimension).surjective w
      rw [←hw,secondProjection_apply,firstProjection_apply]
      exact (equiv dimension).map_zero
    exact facts.2.1 v (by rw [actual,target,norm_zero]; positivity)
  · intro v
    have bound := facts.2.2 R sourceClose v.val v.property
    simpa only [actual] using bound

end LeanShared.GlobalWordNarrowProjectionBounds
