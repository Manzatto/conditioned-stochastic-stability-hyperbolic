module

public import LeanShared.Geometry.DiffeomorphismInverseDifferential
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! The actual inverse differential retains projected operator bounds
when its target fiber is identified by the inverse-map identity. The
Riemannian norm transport is proved, not silently treated as definitional. -/
public noncomputable section
open IsManifold Bundle
open scoped Manifold Bundle
namespace LeanShared.DiffeomorphismDifferential
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem inverse_comp_norm_le (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (x : M) (P : TangentSpace (𝓘(ℝ,E)) (T x) →L[ℝ] TangentSpace (𝓘(ℝ,E)) (T x))
    (κ : ℝ) (nonnegative : 0 ≤ κ)
    (bound : ‖(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm (T x)).comp P‖ ≤ κ) :
    ‖(differential T forward inverse x).symm.toContinuousLinearMap.comp P‖ ≤ κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro v
  have estimate := (((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm (T x)).comp P).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right bound (norm_nonneg v))
  have transport (y : M) (same : y = x) (w : TangentSpace (𝓘(ℝ,E)) y) :
      ‖w‖ = ‖(show TangentSpace (𝓘(ℝ,E)) x from w)‖ := by
    subst y
    rfl
  rw [transport _ (T.symm_apply_apply x) _] at estimate
  change ‖(differential T forward inverse x).symm (P v)‖ ≤ κ * ‖v‖
  rw [differential_symm_apply]
  exact estimate

end LeanShared.DiffeomorphismDifferential
