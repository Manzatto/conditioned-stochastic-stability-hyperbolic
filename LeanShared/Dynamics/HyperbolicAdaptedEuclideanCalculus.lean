module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanFrames
public import LeanShared.Analysis.CenteredCoordinateModelChange

/-! Exact prototype and derivative transport to the actual Euclidean
adapted model, retaining the constants in the change from max-product norm. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet CenteredManifoldCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

abbrev PatchSystem.SplitModel (system : PatchSystem b) :=
  EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
    EuclideanSpace ℝ (Fin system.framing.stableDimension)

@[expose] def PatchSystem.euclideanDiagonal (system : PatchSystem b)
    (U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.unstableDimension))
    (S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.stableDimension)) :
    system.EuclideanModel ≃L[ℝ] system.EuclideanModel :=
  system.euclideanEquiv.symm.trans ((U.prodCongr S).trans system.euclideanEquiv)

theorem PatchSystem.euclideanDiagonal_bounds (system : PatchSystem b)
    (U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.unstableDimension))
    (S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.stableDimension)) :
    ‖(system.euclideanDiagonal U S).toContinuousLinearMap‖ ≤ 2 * ‖(U.prodCongr S).toContinuousLinearMap‖ ∧
      ‖(system.euclideanDiagonal U S).symm.toContinuousLinearMap‖ ≤
        2 * ‖(U.prodCongr S).symm.toContinuousLinearMap‖ := by
  have dimension : Module.finrank ℝ system.SplitModel = Module.finrank ℝ system.EuclideanModel := by
    simp [Module.finrank_prod]
  exact ⟨OrthogonalProductCoordinates.transport_norm_le dimension (U.prodCongr S).toContinuousLinearMap,
    OrthogonalProductCoordinates.transport_norm_le dimension (U.prodCongr S).symm.toContinuousLinearMap⟩

theorem PatchSystem.centered_euclidean_eq (system : PatchSystem b)
    (L R : system.SplitModel ≃L[ℝ] E) (a b : E) (h : E → E) :
    centered (system.euclideanEquiv.symm.trans L) (system.euclideanEquiv.symm.trans R) a b h =
      system.euclideanEquiv ∘ centered L R a b h ∘ system.euclideanEquiv.symm := by
  simpa only [ContinuousLinearEquiv.symm_symm] using
    centered_model_change L R system.euclideanEquiv.symm system.euclideanEquiv.symm a b h

theorem PatchSystem.euclidean_derivative_error (system : PatchSystem b)
    (f : system.SplitModel → system.SplitModel)
    (U : EuclideanSpace ℝ (Fin system.framing.unstableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.unstableDimension))
    (S : EuclideanSpace ℝ (Fin system.framing.stableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin system.framing.stableDimension)) (z : system.EuclideanModel) :
    ‖fderiv ℝ (system.euclideanEquiv ∘ f ∘ system.euclideanEquiv.symm) z -
      (system.euclideanDiagonal U S).toContinuousLinearMap‖ ≤
      2 * ‖fderiv ℝ f (system.euclideanEquiv.symm z) - U.toContinuousLinearMap.prodMap S.toContinuousLinearMap‖ := by
  have dimension : Module.finrank ℝ system.SplitModel = Module.finrank ℝ system.EuclideanModel := by
    simp [Module.finrank_prod]
  rw [ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv]
  change ‖OrthogonalProductCoordinates.transport dimension (fderiv ℝ f (system.euclideanEquiv.symm z)) -
    OrthogonalProductCoordinates.transport dimension (U.toContinuousLinearMap.prodMap S.toContinuousLinearMap)‖ ≤ _
  rw [← OrthogonalProductCoordinates.transport_sub]
  exact OrthogonalProductCoordinates.transport_norm_le dimension _

end LeanShared.HyperbolicAdaptedPatchSystem
