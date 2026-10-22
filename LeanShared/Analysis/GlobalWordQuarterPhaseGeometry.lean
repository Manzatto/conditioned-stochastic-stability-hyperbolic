module
public import LeanShared.Analysis.GlobalWordAdjointRadialBounds

/-! The actual word derivative has a closed quarter-cone margin inside
the fixed half Fourier cone. The graph factorization already constructed
for the radial estimate gives the quarter-cone constant ten once per word. -/
public noncomputable section
open Set
namespace LeanShared.GlobalWordQuarterPhaseGeometry
open OrthogonalProductCoordinates ProductRateWordRadialBounds
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

private theorem upper_quarter (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (A : (X×Y) →L[ℝ] (X×Y)) (J : X →L[ℝ] X) (K : Y →L[ℝ] X)
    (L : X →L[ℝ] Y) (S : Y →L[ℝ] Y)
    (factorization : ∀ u s, A (u,s) = (J (u-K s),L (J (u-K s))+S s))
    {μ : ℝ} (nonnegativeμ : 0 ≤ μ) (smallK : ‖K‖ ≤ 1/8) (stable : ‖S‖ ≤ μ)
    (ξ : E) (outside : (transport dimension A).adjoint ξ ∉
      ProjectionConeTransversality.cone (secondProjection dimension) (1/4)) :
    ‖(transport dimension A).adjoint ξ‖ ≤ 10*μ*‖ξ‖ := by
  obtain ⟨z,rfl⟩ := (equiv dimension).surjective ξ
  rw [TriangularAdjointRadialBounds.adjoint_formula dimension A J K L S factorization z] at outside ⊢
  let u : X := J.adjoint (z.1+L.adjoint z.2)
  let s : Y := S.adjoint z.2-K.adjoint u
  have notCone : ¬ ‖s‖ ≤ (1/4:ℝ)*‖u‖ := by
    simpa only [TriangularAdjointRadialBounds.second_cone_iff] using outside
  have quarter : (1/4:ℝ)*‖u‖ ≤ ‖s‖ := (lt_of_not_ge notCone).le
  have boundS : ‖S.adjoint z.2‖ ≤ μ*‖z.2‖ := by
    have estimate := S.adjoint.le_opNorm z.2
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
  have boundK : ‖K.adjoint u‖ ≤ (1/8:ℝ)*‖u‖ := by
    have estimate := K.adjoint.le_opNorm u
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right smallK (norm_nonneg _))
  have stableComponent : ‖s‖ ≤ μ*‖z.2‖+(1/8:ℝ)*‖u‖ :=
    (norm_sub_le _ _).trans (add_le_add boundS boundK)
  have sumBound := norm_le_axis_sum dimension (u,s)
  have total : ‖equiv dimension (u,s)‖ ≤ 10*μ*‖z.2‖ := by nlinarith
  exact total.trans (mul_le_mul_of_nonneg_left (axis_norm_le dimension z).2 (by positivity))

private theorem matrix_bounds {q : ℝ} (positiveQ : 0 < q) (contractingQ : q < 1)
    (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E) :
    ∃ ε : ℝ, 0 < ε ∧ q+2*ε < 1 ∧ 1 < 1/q-2*ε ∧
      ∀ blocks : List (E ≃L[ℝ] E),
      (∀ B ∈ blocks, ∃ U : X ≃L[ℝ] X, ∃ S : Y →L[ℝ] Y,
        ‖S‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
          ‖B.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S)‖ ≤ ε) →
      (∀ ξ : E, (wordEquiv blocks).toContinuousLinearMap.adjoint ξ ∉
          ProjectionConeTransversality.cone (secondProjection dimension) (1/4) →
        ‖(wordEquiv blocks).toContinuousLinearMap.adjoint ξ‖ ≤ 10*(q+2*ε)^blocks.length*‖ξ‖) ∧
      ∀ ξ : E, ξ ∉ interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) →
        (4*((1/q-2*ε)⁻¹)^blocks.length)⁻¹*‖ξ‖ ≤ ‖(wordEquiv blocks).toContinuousLinearMap.adjoint ξ‖ := by
  obtain ⟨δ,positiveδ,stableRate,unstableRate,producer⟩ :=
    ProductRateWordRadialBounds.exists_uniform_radial_bounds positiveQ contractingQ dimension
  have twice : 2*(δ/2)=δ := by ring
  refine ⟨δ/2,by positivity,by rwa [twice],by rwa [twice],fun blocks near => ?_⟩
  let splitBlocks := blocks.map (fun B => (equiv dimension).trans (B.trans (equiv dimension).symm))
  have splitNear : ∀ B ∈ splitBlocks, ∃ U : X ≃L[ℝ] X, ∃ S : Y →L[ℝ] Y,
      ‖S‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
        ‖B.toContinuousLinearMap-U.toContinuousLinearMap.prodMap S‖ ≤ δ := by
    intro B hB
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hB
    obtain ⟨U,S,stable,unstable,close⟩ := near C hC
    refine ⟨U,S,stable,unstable,?_⟩
    have normBound := (OrthogonalRateWordRadialBounds.pullback_norm_le dimension
      (C.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S))).trans
        (mul_le_mul_of_nonneg_left close (by norm_num : (0:ℝ) ≤ 2))
    rw [OrthogonalRateWordRadialBounds.pullback_sub,OrthogonalRateWordRadialBounds.pullback_transport] at normBound
    change ‖OrthogonalRateWordRadialBounds.pullback dimension C.toContinuousLinearMap-
      U.toContinuousLinearMap.prodMap S‖ ≤ δ
    simpa only [twice] using normBound
  obtain ⟨J,K,L,S₀,factorization,normK,_normL,_normJ,normS,_upper,lower,_alternative⟩ :=
    producer splitBlocks splitNear
  have wordIdentity : transport dimension (wordEquiv splitBlocks).toContinuousLinearMap =
      (wordEquiv blocks).toContinuousLinearMap := OrthogonalRateWordRadialBounds.transport_word dimension blocks
  have lengthIdentity : splitBlocks.length=blocks.length := List.length_map _
  have upper (ξ : E) (outside : (wordEquiv blocks).toContinuousLinearMap.adjoint ξ ∉
      ProjectionConeTransversality.cone (secondProjection dimension) (1/4)) :
      ‖(wordEquiv blocks).toContinuousLinearMap.adjoint ξ‖ ≤ 10*(q+δ)^blocks.length*‖ξ‖ := by
    have bound := upper_quarter dimension (wordEquiv splitBlocks).toContinuousLinearMap
      J.toContinuousLinearMap K L S₀.toContinuousLinearMap factorization
      (pow_nonneg (by positivity : 0 ≤ q+δ) _) normK normS ξ
      (by rwa [wordIdentity])
    simpa only [wordIdentity,lengthIdentity] using bound
  rw [wordIdentity,lengthIdentity] at lower
  simpa only [twice] using And.intro upper lower

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
      (∀ ξ : E, D.adjoint ξ ∉ ProjectionConeTransversality.cone (secondProjection dimension) (1/4) →
        ‖D.adjoint ξ‖ ≤ 10*(q+2*ε)^N*‖ξ‖) ∧
      ∀ ξ : E, ξ ∉ interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) →
        (4*((1/q-2*ε)⁻¹)^N)⁻¹*‖ξ‖ ≤ ‖D.adjoint ξ‖ := by
  obtain ⟨ε,positiveε,stableRate,unstableRate,producer⟩ := matrix_bounds positiveQ contractingQ dimension
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
  obtain ⟨upper,lower⟩ := producer matrices near
  have wordIdentity : (wordEquiv matrices).toContinuousLinearMap =
      fderiv ℝ (OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph H word N) x := by
    rw [OrthogonalRateGlobalWordFakeLeaves.prefixHomeomorph_coe]
    exact GlobalHomeomorphWordDerivative.word_derivative H smooth inverseSmooth word x N
  have lengthIdentity : matrices.length=N := GlobalHomeomorphWordDerivative.blocks_length H smooth inverseSmooth word x N le_rfl
  rw [wordIdentity,lengthIdentity] at upper lower
  exact ⟨upper,lower⟩

end LeanShared.GlobalWordQuarterPhaseGeometry
