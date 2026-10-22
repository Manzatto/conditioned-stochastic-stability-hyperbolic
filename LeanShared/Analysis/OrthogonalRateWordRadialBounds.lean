module
public import LeanShared.Analysis.ProductRateWordRadialBounds

/-! Actual Hilbert-space matrix words inherit the graph radial estimates.
The change from the max-product norm costs two in the allowed one-step
error; it cancels exactly inside every word. -/
@[expose] public noncomputable section
open Set
namespace LeanShared.OrthogonalRateWordRadialBounds
open OrthogonalProductCoordinates ProductRateWordRadialBounds
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

def pullback (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (B : E →L[ℝ] E) : (X×Y) →L[ℝ] (X×Y) :=
  (equiv dimension).symm.toContinuousLinearMap.comp
    (B.comp (equiv dimension).toContinuousLinearMap)

theorem pullback_norm_le (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (B : E →L[ℝ] E) : ‖pullback dimension B‖ ≤ 2*‖B‖ := by
  calc
    _ ≤ ‖(equiv dimension).symm.toContinuousLinearMap‖ *
        (‖B‖ * ‖(equiv dimension).toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg (equiv dimension).symm.toContinuousLinearMap))
    _ ≤ 1*(‖B‖*2) := mul_le_mul (inverse_equiv_norm_le_one dimension)
      (mul_le_mul_of_nonneg_left (equiv_norm_le_two dimension) (norm_nonneg B))
      (mul_nonneg (norm_nonneg B) (norm_nonneg (equiv dimension).toContinuousLinearMap)) zero_le_one
    _ = 2*‖B‖ := by ring

theorem pullback_transport (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (A : (X×Y) →L[ℝ] (X×Y)) : pullback dimension (transport dimension A) = A := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [pullback, transport, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

theorem pullback_sub (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (B C : E →L[ℝ] E) : pullback dimension (B-C) = pullback dimension B-pullback dimension C := by
  simp only [pullback, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem transport_word (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (blocks : List (E ≃L[ℝ] E)) :
    transport dimension (wordEquiv (blocks.map
      (fun B => (equiv dimension).trans (B.trans (equiv dimension).symm)))).toContinuousLinearMap =
        (wordEquiv blocks).toContinuousLinearMap := by
  have conjugation := conjugate_word (equiv dimension).symm blocks
  simp only [ContinuousLinearEquiv.symm_symm] at conjugation
  rw [conjugation]
  apply ContinuousLinearMap.ext
  intro z
  simp only [transport, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]

set_option maxHeartbeats 1000000 in
/-- The allowed error is chosen before the length and the actual blocks.
Every constant four occurs once, after the full word has been formed. -/
theorem exists_uniform_radial_bounds {q : ℝ} (positiveQ : 0 < q) (contractingQ : q < 1)
    (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E) :
    ∃ ε : ℝ, 0 < ε ∧ q+2*ε < 1 ∧ 1 < 1/q-2*ε ∧
      ∀ blocks : List (E ≃L[ℝ] E),
      (∀ B ∈ blocks, ∃ U : X ≃L[ℝ] X, ∃ S : Y →L[ℝ] Y,
        ‖S‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
          ‖B.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S)‖ ≤ ε) →
      (∀ β : ℝ, 1/2 ≤ β → ∀ ξ : E,
        (wordEquiv blocks).toContinuousLinearMap.adjoint ξ ∉
          ProjectionConeTransversality.cone (secondProjection dimension) β →
        ‖(wordEquiv blocks).toContinuousLinearMap.adjoint ξ‖ ≤ 4*(q+2*ε)^blocks.length*‖ξ‖) ∧
      (∀ ξ : E, ξ ∉ interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) →
        (4*((1/q-2*ε)⁻¹)^blocks.length)⁻¹*‖ξ‖ ≤ ‖(wordEquiv blocks).toContinuousLinearMap.adjoint ξ‖) ∧
      ∀ β : ℝ, 1/2 ≤ β → ∀ ξ : E,
        (wordEquiv blocks).toContinuousLinearMap.adjoint ξ ∈
            ProjectionConeTransversality.cone (secondProjection dimension) β ∨
          ‖(wordEquiv blocks).toContinuousLinearMap.adjoint ξ‖ ≤ 4*(q+2*ε)^blocks.length*‖ξ‖ := by
  obtain ⟨δ, positiveδ, stableRate, unstableRate, producer⟩ :=
    ProductRateWordRadialBounds.exists_uniform_radial_bounds positiveQ contractingQ dimension
  have twice : 2*(δ/2) = δ := by ring
  refine ⟨δ/2, by positivity, by rwa [twice], by rwa [twice], fun blocks near => ?_⟩
  let splitBlocks := blocks.map
    (fun B => (equiv dimension).trans (B.trans (equiv dimension).symm))
  have splitNear : ∀ B ∈ splitBlocks, ∃ U : X ≃L[ℝ] X, ∃ S : Y →L[ℝ] Y,
      ‖S‖ ≤ q ∧ ‖U.symm.toContinuousLinearMap‖ ≤ q ∧
        ‖B.toContinuousLinearMap-U.toContinuousLinearMap.prodMap S‖ ≤ δ := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
    obtain ⟨U, S, stable, unstable, close⟩ := near C hC
    refine ⟨U, S, stable, unstable, ?_⟩
    have normBound := (pullback_norm_le dimension
      (C.toContinuousLinearMap-transport dimension (U.toContinuousLinearMap.prodMap S))).trans
        (mul_le_mul_of_nonneg_left close (by norm_num : (0:ℝ) ≤ 2))
    rw [pullback_sub, pullback_transport] at normBound
    change ‖pullback dimension C.toContinuousLinearMap-U.toContinuousLinearMap.prodMap S‖ ≤ δ
    simpa only [twice] using normBound
  obtain ⟨_J, _K, _L, _S₀, _factorization, _normK, _normL, _normJ, _normS,
    upper, lower, alternative⟩ := producer splitBlocks splitNear
  have wordIdentity : transport dimension (wordEquiv splitBlocks).toContinuousLinearMap =
      (wordEquiv blocks).toContinuousLinearMap := transport_word dimension blocks
  have lengthIdentity : splitBlocks.length = blocks.length := List.length_map _
  rw [wordIdentity, lengthIdentity] at upper lower alternative
  simpa only [twice] using And.intro upper (And.intro lower alternative)

end LeanShared.OrthogonalRateWordRadialBounds
