module

public import LeanShared.Geometry.DiffeomorphismInverseOperatorNorm
public import LeanShared.Geometry.BundleProjectionCoordinateBounds

/-! The inverse of the actual differential, expressed in independently
chosen native tangent charts, satisfies exactly the projected estimate of
the actual inverse map. Fiber transport and both chart losses are proved. -/
public noncomputable section
open IsManifold Bundle
open scoped Manifold Bundle ContDiff
namespace LeanShared.DiffeomorphismDifferential
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem inverse_coordinate_comp_norm_le (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (i j : M) (x : M) (target : T x ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j).baseSet)
    (P : ∀ y : M, TangentSpace (𝓘(ℝ,E)) y →L[ℝ] TangentSpace (𝓘(ℝ,E)) y)
    (C κ : ℝ) (nonnegativeC : 0 ≤ C) (nonnegativeκ : 0 ≤ κ)
    (sourceBound : ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) i).continuousLinearMapAt ℝ x‖ ≤ C)
    (targetBound : ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) j).symmL ℝ (T x)‖ ≤ C)
    (native : ‖(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm (T x)).comp (P (T x))‖ ≤ κ) :
    ‖(BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j)
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i) (T x) x
        (differential T forward inverse x).symm.toContinuousLinearMap).comp
      (BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E)))
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j) P (T x))‖ ≤ C ^ 2 * κ := by
  exact BundleProjectionCocycleCoordinates.map_comp_projection_norm_le
    (TangentSpace (𝓘(ℝ,E)))
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j)
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i) P (T x) x target
    (differential T forward inverse x).symm.toContinuousLinearMap C κ
    nonnegativeC targetBound sourceBound
    (inverse_comp_norm_le T forward inverse x (P (T x)) κ nonnegativeκ native)

end LeanShared.DiffeomorphismDifferential
