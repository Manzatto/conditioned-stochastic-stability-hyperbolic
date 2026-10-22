module
public import LeanShared.Analysis.OneStepConePolarization
public import LeanShared.Analysis.GlobalWordQuarterPhaseGeometry

/-! Every word of length at least one of actual global extensions polarizes
frequencies: the adjoint word derivative sends nonzero vectors outside the
plus half cone into the interior of the narrow one-step cone. Each step
polarizes, and the narrow cone avoids the plus half cone, so no length
threshold is needed. -/
public noncomputable section
open Set
namespace LeanShared.GlobalWordOneStepPolarization
open OrthogonalProductCoordinates ProductRateWordRadialBounds
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem list_polarization (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    {q : ℝ} (positive : 0 < q) (contracting : q < 1) :
    ∀ blocks : List (E ≃L[ℝ] E),
    (∀ B ∈ blocks, ∃ U : X ≃L[ℝ] X, ∃ S : Y ≃L[ℝ] Y,
      ‖S.toContinuousLinearMap‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
      ‖B.toContinuousLinearMap - (diagonal dimension U S).toContinuousLinearMap‖ ≤
        ProjectionConeRateMargin.tolerance q) →
    ∀ v : E, v ≠ 0 →
      v ∉ interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) →
      (wordEquiv blocks).toContinuousLinearMap.adjoint v ≠ 0 ∧
      (wordEquiv blocks).toContinuousLinearMap.adjoint v ∉
        interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) ∧
      (blocks ≠ [] → (wordEquiv blocks).toContinuousLinearMap.adjoint v ∈
        interior (ProjectionConeTransversality.cone (secondProjection dimension)
          (OneStepConePolarization.narrowOpening q))) := by
  obtain ⟨_, narrowNonneg, narrowLtTwo, _, _, _, _, _⟩ :=
    OneStepConePolarization.opening_bounds positive contracting
  intro blocks
  induction blocks with
  | nil =>
    intro _ v nonzero outside
    have identity : (wordEquiv ([] : List (E ≃L[ℝ] E))).toContinuousLinearMap =
        ContinuousLinearMap.id ℝ E := ContinuousLinearEquiv.coe_refl
    rw [identity, ContinuousLinearMap.adjoint_id]
    exact ⟨nonzero, outside, fun h => absurd rfl h⟩
  | cons B tail ih =>
    intro near v nonzero outside
    have nearTail : ∀ C ∈ tail, ∃ U : X ≃L[ℝ] X, ∃ S : Y ≃L[ℝ] Y,
        ‖S.toContinuousLinearMap‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
        ‖C.toContinuousLinearMap - (diagonal dimension U S).toContinuousLinearMap‖ ≤
          ProjectionConeRateMargin.tolerance q :=
      fun C hC => near C (List.mem_cons_of_mem _ hC)
    obtain ⟨wNonzero, wOutside, _⟩ := ih nearTail v nonzero outside
    obtain ⟨U, S, stable, unstable, close⟩ := near B List.mem_cons_self
    have identity : (wordEquiv (B :: tail)).toContinuousLinearMap =
        (wordEquiv tail).toContinuousLinearMap.comp B.toContinuousLinearMap :=
      ContinuousLinearMap.ext fun w => rfl
    rw [identity, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
    have step := OneStepConePolarization.adjoint_half_polarization dimension U S q positive
      contracting stable unstable B.toContinuousLinearMap close
      ((wordEquiv tail).toContinuousLinearMap.adjoint v) wNonzero wOutside
    exact ⟨step.1, OneStepConePolarization.not_mem_interior_half dimension narrowNonneg narrowLtTwo
      (interior_subset step.2) step.1, fun _ => step.2⟩

theorem global_word_polarization (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    {q : ℝ} (positive : 0 < q) (contracting : q < 1)
    {G : Type*} (H : G → E ≃ₜ E)
    (smooth : ∀ g, Differentiable ℝ (H g)) (inverseSmooth : ∀ g, Differentiable ℝ (H g).symm)
    (U : G → X ≃L[ℝ] X) (S : G → Y ≃L[ℝ] Y)
    (stable : ∀ g, ‖(S g).toContinuousLinearMap‖ ≤ q)
    (unstable : ∀ g, ‖(U g).symm.toContinuousLinearMap‖ ≤ q)
    (close : ∀ g x, ‖fderiv ℝ (H g) x - (diagonal dimension (U g) (S g)).toContinuousLinearMap‖ ≤
      ProjectionConeRateMargin.tolerance q)
    {N : ℕ} (positiveN : 0 < N) (word : Fin N → G) (x ξ : E) (nonzero : ξ ≠ 0)
    (outside : ξ ∉ interior
      (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))) :
    (fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H word N) x).adjoint ξ ≠ 0 ∧
    (fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H word N) x).adjoint ξ ∈
      interior (ProjectionConeTransversality.cone (secondProjection dimension)
        (OneStepConePolarization.narrowOpening q)) := by
  let matrices := GlobalHomeomorphWordDerivative.blocks H smooth inverseSmooth word x N
  have near : ∀ B ∈ matrices, ∃ U : X ≃L[ℝ] X, ∃ S : Y ≃L[ℝ] Y,
      ‖S.toContinuousLinearMap‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
      ‖B.toContinuousLinearMap - (diagonal dimension U S).toContinuousLinearMap‖ ≤
        ProjectionConeRateMargin.tolerance q := by
    intro B member
    obtain ⟨j, rfl⟩ := GlobalHomeomorphWordDerivative.mem_blocks H smooth inverseSmooth word x N B member
    refine ⟨U (word j), S (word j), stable _, unstable _, ?_⟩
    rw [HomeomorphDerivativeEquivalence.derivative_coe]
    exact close _ _
  have wordIdentity : (wordEquiv matrices).toContinuousLinearMap =
      fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H word N) x := by
    rw [OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph_coe]
    exact GlobalHomeomorphWordDerivative.word_derivative H smooth inverseSmooth word x N
  have lengthIdentity : matrices.length = N :=
    GlobalHomeomorphWordDerivative.blocks_length H smooth inverseSmooth word x N le_rfl
  have nonempty : matrices ≠ [] := List.ne_nil_of_length_pos (by rw [lengthIdentity]; exact positiveN)
  have result := list_polarization dimension positive contracting matrices near ξ nonzero outside
  rw [wordIdentity] at result
  exact ⟨result.1, result.2.2 nonempty⟩

end LeanShared.GlobalWordOneStepPolarization
