module
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Exact affine-normalized coordinates under independent linear changes
of input and output model spaces. No charted-space instance is replaced. -/
public noncomputable section
namespace LeanShared.CenteredManifoldCoordinates
variable {E F P Q X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem centered_model_change (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F)
    (φ : X ≃L[ℝ] P) (ψ : Y ≃L[ℝ] Q) (a : E) (b : F) (h : E → F) :
    centered (φ.trans L) (ψ.trans R) a b h = ψ.symm ∘ centered L R a b h ∘ φ := rfl

theorem centered_model_change_fderiv (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F)
    (φ : X ≃L[ℝ] P) (ψ : Y ≃L[ℝ] Q) (a : E) (b : F) (h : E → F) (z : X) :
    fderiv ℝ (centered (φ.trans L) (ψ.trans R) a b h) z =
      ψ.symm.toContinuousLinearMap.comp
        ((fderiv ℝ (centered L R a b h) (φ z)).comp φ.toContinuousLinearMap) := by
  rw [centered_model_change, ContinuousLinearEquiv.comp_fderiv,
    ContinuousLinearEquiv.comp_right_fderiv]

end LeanShared.CenteredManifoldCoordinates
