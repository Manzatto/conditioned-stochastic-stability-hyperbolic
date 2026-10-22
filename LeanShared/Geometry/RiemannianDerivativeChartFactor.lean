module
public import LeanShared.Geometry.CompactRiemannianChartBounds

/-! The native manifold derivative is reconstructed from the actual
coordinate derivative and the two actual chart differentials. -/
public noncomputable section
namespace LeanShared.RiemannianDerivativeChartFactor
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem norm_le
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (H : M → M) (smooth : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) H)
    (d c : OpenPartialHomeomorph M E)
    (dDiff : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (cDiff : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (x : M) (hx : x ∈ d.source) (target : H x ∈ c.source) :
    ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x‖ ≤
      ‖(cDiff.mfderiv target).symm.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c (H x))).symm.toContinuousLinearMap‖ *
      ‖fderiv ℝ (c ∘ H ∘ d.symm) (d x)‖ *
      ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) (d x)).toContinuousLinearMap.comp
        (dDiff.mfderiv hx).toContinuousLinearMap‖ := by
  let C := dDiff.mfderiv hx
  let D := cDiff.mfderiv target
  let A := mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x
  let F := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d x)).toContinuousLinearMap.comp C.toContinuousLinearMap
  let B := D.symm.toContinuousLinearMap.comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c (H x))).symm.toContinuousLinearMap
  let G := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c (H x))).toContinuousLinearMap.comp
    ((D.toContinuousLinearMap.comp (A.comp C.symm.toContinuousLinearMap)).comp
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d x)).symm.toContinuousLinearMap)
  have first : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) d.symm (d x) C.symm.toContinuousLinearMap :=
    (dDiff.mdifferentiableAt_symm (d.map_source hx)).hasMFDerivAt
  have middle : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) H (d.symm (d x)) A := by
    rw [d.left_inv hx]
    exact (smooth x).hasMFDerivAt
  have last : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) c (H (d.symm (d x))) D.toContinuousLinearMap := by
    rw [d.left_inv hx]
    exact (cDiff.mdifferentiableAt target).hasMFDerivAt
  have raw := last.comp (d x) (middle.comp (d x) first)
  have rawCoordinate := raw.2
  simp [mfld_simps,chartAt_self_eq] at rawCoordinate
  have coordinate : HasFDerivAt (c ∘ H ∘ d.symm) G (d x) := by
    convert rawCoordinate using 1
    ext v
    rfl
  have derivative : fderiv ℝ (c ∘ H ∘ d.symm) (d x) = G := coordinate.fderiv
  have reconstruct : A = B.comp (G.comp F) := by
    ext v
    simp only [A,B,C,D,F,G,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  change ‖A‖ ≤ ‖B‖*‖fderiv ℝ (c ∘ H ∘ d.symm) (d x)‖*‖F‖
  rw [derivative]
  calc
    _ ≤ ‖B‖*(‖G‖*‖F‖) := by
      rw [reconstruct]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := (mul_assoc _ _ _).symm

end LeanShared.RiemannianDerivativeChartFactor
