module
public import LeanShared.Analysis.GlobalHomeomorphWordDerivative
public import LeanShared.Analysis.OrthogonalRateWordRadialBounds

/-! The radial bounds apply to the ACTUAL derivative of the literal
nonlinear chronological global word, at its actual prefix states. The
constant four occurs once and the cone alternative is closed. -/
public noncomputable section
open Set
namespace LeanShared.GlobalWordAdjointRadialBounds
open OrthogonalProductCoordinates CylinderPrincipalCoefficient ProductRateWordRadialBounds
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem exists_uniform_bounds {q : ℝ} (positiveQ : 0 < q) (contractingQ : q < 1)
    (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E) :
    ∃ ε : ℝ, 0 < ε ∧ q+2*ε < 1 ∧ 1 < 1/q-2*ε ∧
      ∀ {G : Type*} (H : G → E ≃ₜ E)
      (_smooth : ∀ g, Differentiable ℝ (H g)) (_inverseSmooth : ∀ g, Differentiable ℝ (H g).symm)
      (U : G → X ≃L[ℝ] X) (S : G → Y →L[ℝ] Y),
      (∀ g, ‖S g‖ ≤ q) → (∀ g, ‖(U g).symm.toContinuousLinearMap‖ ≤ q) →
      (∀ g x, ‖fderiv ℝ (H g) x-transport dimension ((U g).toContinuousLinearMap.prodMap (S g))‖ ≤ ε) →
      ∀ {N : ℕ} (word : Fin N → G) (x : E),
      let D := fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H word N) x
      (∀ β : ℝ, 1/2 ≤ β → ∀ ξ : E,
        D.adjoint ξ ∉ ProjectionConeTransversality.cone (secondProjection dimension) β →
        ‖D.adjoint ξ‖ ≤ 4*(q+2*ε)^N*‖ξ‖) ∧
      (∀ ξ : E, ξ ∉ interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) →
        (4*((1/q-2*ε)⁻¹)^N)⁻¹*‖ξ‖ ≤ ‖D.adjoint ξ‖) ∧
      ∀ β : ℝ, 1/2 ≤ β → ∀ ξ : E,
        D.adjoint ξ ∈ ProjectionConeTransversality.cone (secondProjection dimension) β ∨
          ‖D.adjoint ξ‖ ≤ 4*(q+2*ε)^N*‖ξ‖ := by
  obtain ⟨ε,positiveε,stableRate,unstableRate,producer⟩ :=
    OrthogonalRateWordRadialBounds.exists_uniform_radial_bounds positiveQ contractingQ dimension
  refine ⟨ε,positiveε,stableRate,unstableRate,?_⟩
  intro G H smooth inverseSmooth U S stable unstable close N word x
  let matrices := GlobalHomeomorphWordDerivative.blocks H smooth inverseSmooth word x N
  have near : ∀ B ∈ matrices, ∃ U : X ≃L[ℝ] X, ∃ S : Y →L[ℝ] Y,
      ‖S‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
      ‖B.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S)‖ ≤ ε := by
    intro B member
    obtain ⟨j,rfl⟩ := GlobalHomeomorphWordDerivative.mem_blocks H smooth inverseSmooth word x N B member
    refine ⟨U (word j),S (word j),stable _,unstable _,?_⟩
    rw [HomeomorphDerivativeEquivalence.derivative_coe]
    exact close _ _
  obtain ⟨upper,lower,alternative⟩ := producer matrices near
  have wordIdentity : (wordEquiv matrices).toContinuousLinearMap =
      fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H word N) x := by
    rw [OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph_coe]
    exact GlobalHomeomorphWordDerivative.word_derivative H smooth inverseSmooth word x N
  have lengthIdentity : matrices.length = N :=
    GlobalHomeomorphWordDerivative.blocks_length H smooth inverseSmooth word x N le_rfl
  rw [wordIdentity,lengthIdentity] at upper lower alternative
  exact ⟨upper,lower,alternative⟩

end LeanShared.GlobalWordAdjointRadialBounds
