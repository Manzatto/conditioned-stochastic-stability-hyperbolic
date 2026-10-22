module
public import LeanShared.Dynamics.HyperbolicAdaptedReferenceFrames
public import LeanShared.Geometry.OrthogonalProductOperatorBounds
import Mathlib.Tactic.Linarith

/-! Actual adapted whole frames with a genuine Euclidean input model.
The fixed change of model preserves the adapted quadratic form exactly
and has explicit bounds relative to the previous max-product coordinates. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet HyperbolicAdaptedFramePatches
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

abbrev PatchSystem.EuclideanModel (system : PatchSystem b) :=
  EuclideanSpace ℝ (Fin (system.framing.unstableDimension + system.framing.stableDimension))

@[expose] def PatchSystem.euclideanEquiv (system : PatchSystem b) :
    (EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension)) ≃L[ℝ] system.EuclideanModel :=
  OrthogonalProductCoordinates.equiv (by simp [Module.finrank_prod])

theorem PatchSystem.euclideanEquiv_norm (system : PatchSystem b) :
    ‖system.euclideanEquiv.toContinuousLinearMap‖ ≤ 2 ∧
      ‖system.euclideanEquiv.symm.toContinuousLinearMap‖ ≤ 1 :=
  ⟨OrthogonalProductCoordinates.equiv_norm_le_two _,
    OrthogonalProductCoordinates.inverse_equiv_norm_le_one _⟩

@[expose] def PatchSystem.euclideanReferenceFrame (system : PatchSystem b) (c : Λ)
    (y : system.frameDomain c) : system.EuclideanModel ≃L[ℝ]
      TangentSpace (𝓘(ℝ, E)) y.val.val :=
  system.euclideanEquiv.symm.trans (system.referenceFrame c y)

theorem PatchSystem.euclideanReferenceFrame_quadratic (system : PatchSystem b) (c : Λ)
    (y : system.frameDomain c) (v : system.EuclideanModel) :
    HyperbolicAdaptedForms.splitForm T T.symm b.hyperbolic.projection system.rate system.time y.val.val
      (system.euclideanReferenceFrame c y v) (system.euclideanReferenceFrame c y v) = ‖v‖ ^ 2 := by
  have quadratic := wholeFrame_quadratic (system.unstableFrame c) (system.stableFrame c)
    ⟨y.val.val, y.val.property, y.property.1⟩ (system.euclideanEquiv.symm v)
  change HyperbolicAdaptedForms.splitForm T T.symm b.hyperbolic.projection system.rate system.time y.val.val
    (system.euclideanReferenceFrame c y v) (system.euclideanReferenceFrame c y v) = _ at quadratic
  rw [quadratic]
  have equal := OrthogonalProductCoordinates.norm_sq
    (show Module.finrank ℝ (EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension)) = Module.finrank ℝ system.EuclideanModel
      by simp [Module.finrank_prod]) (system.euclideanEquiv.symm v)
  change ‖system.euclideanEquiv (system.euclideanEquiv.symm v)‖ ^ 2 = _ at equal
  rw [system.euclideanEquiv.apply_symm_apply] at equal
  exact equal.symm

theorem PatchSystem.euclideanReferenceFrame_bounds (system : PatchSystem b) (c : Λ)
    (y : system.frameDomain c) :
    ‖(system.euclideanReferenceFrame c y).toContinuousLinearMap‖ ≤ 2 ∧
      ‖(system.euclideanReferenceFrame c y).symm.toContinuousLinearMap‖ ≤ 2 * system.inverse_bound := by
  have bounds := system.whole_bounds c ⟨y.val.val, y.val.property, y.property.1⟩
  constructor
  · change ‖(system.referenceFrame c y).toContinuousLinearMap.comp
      system.euclideanEquiv.symm.toContinuousLinearMap‖ ≤ 2
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul bounds.1 system.euclideanEquiv_norm.2 (norm_nonneg _) (by norm_num)).trans_eq
        (mul_one 2))
  · change ‖system.euclideanEquiv.toContinuousLinearMap.comp
      (system.referenceFrame c y).symm.toContinuousLinearMap‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul system.euclideanEquiv_norm.1 bounds.2 (norm_nonneg _) (by norm_num))

theorem PatchSystem.euclidean_chartFrame (system : PatchSystem b) (c : Λ)
    (y : system.frameDomain c) :
    ContinuousCenteredFrameCharts.chartFrame c.val y.val.val y.property.2
      (system.euclideanReferenceFrame c y) =
      system.euclideanEquiv.symm.trans (ContinuousCenteredFrameCharts.chartFrame c.val y.val.val
        y.property.2 (system.referenceFrame c y)) := by
  apply ContinuousLinearEquiv.ext
  rfl

end LeanShared.HyperbolicAdaptedPatchSystem
