module
public import LeanShared.Analysis.OrthogonalRateWordRadialBounds

/-! A single near-diagonal budget preserves the narrow1/8 direction cones
for every actual Hilbert matrix word. Close stable-projector kernels enter
these cones with slope1/63, so the actual word image has slope at most1/8. -/
public noncomputable section
open Set
namespace LeanShared.OrthogonalRateWordNarrowCones
open OrthogonalProductCoordinates ProductRateWordRadialBounds OrthogonalRateWordRadialBounds
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem exists_uniform_budget {q : ℝ} (positiveQ : 0 < q) (contractingQ : q < 1)
    (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ blocks : List (E ≃L[ℝ] E),
      (∀ B ∈ blocks, ∃ U : X ≃L[ℝ] X, ∃ S : Y →L[ℝ] Y,
        ‖S‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
          ‖B.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S)‖ ≤ ε) →
      (∀ v, ‖secondProjection dimension v‖ ≤ (1/8:ℝ)*‖firstProjection dimension v‖ →
        ‖secondProjection dimension (wordEquiv blocks v)‖ ≤ (1/8:ℝ)*‖firstProjection dimension (wordEquiv blocks v)‖) ∧
      (∀ v, ‖firstProjection dimension (wordEquiv blocks v)‖ ≤ (1/8:ℝ)*‖secondProjection dimension (wordEquiv blocks v)‖ →
        ‖firstProjection dimension v‖ ≤ (1/8:ℝ)*‖secondProjection dimension v‖) ∧
      ∀ R : E →L[ℝ] E, ‖R-secondProjection dimension‖ ≤ (1/64:ℝ) →
        ∀ v ∈ R.ker,
          ‖secondProjection dimension (wordEquiv blocks v)‖ ≤ (1/8:ℝ)*‖firstProjection dimension (wordEquiv blocks v)‖ := by
  obtain ⟨δ,positiveδ,_stableRate,_unstableRate,budget⟩ :=
    ProductRateConeBounds.exists_budget (X := X) (Y := Y) positiveQ contractingQ
      (by norm_num : (0:ℝ)<1/8) (by norm_num : (1/8:ℝ)≤1)
  have twice : 2*(δ/2)=δ := by ring
  refine ⟨δ/2,by positivity,fun blocks near => ?_⟩
  let splitBlocks := blocks.map
    (fun B => (equiv dimension).trans (B.trans (equiv dimension).symm))
  have actions (B : (X×Y) ≃L[ℝ] (X×Y)) (hB : B∈splitBlocks) :
      (∀ z, ‖z.2‖ ≤ (1/8:ℝ)*‖z.1‖ → ‖(B z).2‖ ≤ (1/8:ℝ)*‖(B z).1‖) ∧
      (∀ z, ‖(B z).1‖ ≤ (1/8:ℝ)*‖(B z).2‖ → ‖z.1‖ ≤ (1/8:ℝ)*‖z.2‖) := by
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hB
    obtain ⟨U,S,stable,unstable,close⟩ := near C hC
    have normBound := (pullback_norm_le dimension
      (C.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S))).trans
        (mul_le_mul_of_nonneg_left close (by norm_num : (0:ℝ)≤2))
    rw [pullback_sub,pullback_transport] at normBound
    have sourceClose : ‖((equiv dimension).trans (C.trans (equiv dimension).symm)).toContinuousLinearMap-
        U.toContinuousLinearMap.prodMap S‖ ≤ δ := by
      change ‖pullback dimension C.toContinuousLinearMap-U.toContinuousLinearMap.prodMap S‖ ≤ δ
      simpa only [twice] using normBound
    have facts := budget U S _ stable unstable sourceClose
    exact ⟨facts.2.1,facts.1⟩
  have wordIdentity (z : X×Y) :
      wordEquiv blocks (equiv dimension z)=equiv dimension (wordEquiv splitBlocks z) := by
    have identity := transport_word dimension blocks
    have value := congrArg (fun A : E →L[ℝ] E => A (equiv dimension z)) identity
    simpa only [transport,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using value.symm
  have forward (v : E) (input : ‖secondProjection dimension v‖ ≤ (1/8:ℝ)*‖firstProjection dimension v‖) :
      ‖secondProjection dimension (wordEquiv blocks v)‖ ≤ (1/8:ℝ)*‖firstProjection dimension (wordEquiv blocks v)‖ := by
    obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
    rw [secondProjection_apply,firstProjection_apply,norm_second_axis,norm_first_axis] at input
    rw [wordIdentity,secondProjection_apply,firstProjection_apply,norm_second_axis,norm_first_axis]
    exact forward_narrow splitBlocks (fun B hB => (actions B hB).1) z input
  refine ⟨forward,?_,?_⟩
  · intro v target
    obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
    rw [wordIdentity,firstProjection_apply,secondProjection_apply,norm_first_axis,norm_second_axis] at target
    rw [firstProjection_apply,secondProjection_apply,norm_first_axis,norm_second_axis]
    exact backward_narrow splitBlocks (fun B hB => (actions B hB).2) z target
  · intro R close v member
    apply forward v
    obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
    have zero : R (equiv dimension z)=0 := member
    have error := ((R-secondProjection dimension).le_opNorm (equiv dimension z)).trans
      (mul_le_mul_of_nonneg_right close (norm_nonneg _))
    change ‖R (equiv dimension z)-secondProjection dimension (equiv dimension z)‖ ≤ _ at error
    rw [zero,zero_sub,norm_neg,secondProjection_apply,norm_second_axis] at error
    rw [secondProjection_apply,firstProjection_apply,norm_second_axis,norm_first_axis]
    have triangle := norm_le_axis_sum dimension z
    nlinarith [norm_nonneg z.1]

end LeanShared.OrthogonalRateWordNarrowCones
