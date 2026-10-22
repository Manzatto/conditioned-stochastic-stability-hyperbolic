module

public import LeanShared.Dynamics.ToralCatMapFlatMetric

/-! The actual differential of the real torus quotient is exactly the
constructed flat frame. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

set_option backward.isDefEq.respectTransparency false in
theorem quotientDifferential_product (z v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ProductModel)) quotient z
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v) =
        productTangentFrame (quotient z) v := by
  have one : MDifferentiable (𝓘(ℝ, ℝ)) (𝓘(ℝ, UnitAddCircleManifold.Model))
      UnitAddCircleManifold.projection := UnitAddCircleManifold.smooth_projection.mdifferentiable (by simp)
  have productDerivative := mfderiv_prodMap (one z.1) (one z.2)
  have functions : Prod.map UnitAddCircleManifold.projection UnitAddCircleManifold.projection = quotient := rfl
  rw [functions] at productDerivative
  have normalized : mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ProductModel)) quotient z =
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, UnitAddCircleManifold.Model)) UnitAddCircleManifold.projection z.1).prodMap
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, UnitAddCircleManifold.Model)) UnitAddCircleManifold.projection z.2) := by
    rw [modelWithCornersSelf_prod, modelWithCornersSelf_prod]
    rw [← chartedSpaceSelf_prod (H := ℝ) (H' := ℝ)]
    exact productDerivative
  rw [normalized]
  change ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, UnitAddCircleManifold.Model)) UnitAddCircleManifold.projection z.1) v.1,
    (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, UnitAddCircleManifold.Model)) UnitAddCircleManifold.projection z.2) v.2) =
      (UnitAddCircleManifold.tangentFrame _ v.1, UnitAddCircleManifold.tangentFrame _ v.2)
  rw [UnitAddCircleManifold.tangentFrame_projection, UnitAddCircleManifold.tangentFrame_projection]

set_option backward.isDefEq.respectTransparency false in
theorem quotientDifferential (z v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) quotient z
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v) =
        tangentFrame (quotient z) (liftHilbertEquivalence v) := by
  have same : (@id Torus) ∘ quotient = quotient := rfl
  have chain := mfderiv_comp (I := 𝓘(ℝ, ℝ × ℝ)) (I' := 𝓘(ℝ, ProductModel))
    (I'' := 𝓘(ℝ, HilbertModel)) z
    ((identity_to_hilbert.mdifferentiable (by simp)) (quotient z))
    ((smooth_quotient_product.mdifferentiable (by simp)) z)
  rw [same] at chain
  rw [chain]
  change mfderiv (𝓘(ℝ, ProductModel)) (𝓘(ℝ, HilbertModel)) (@id Torus) (quotient z)
    (mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ProductModel)) quotient z
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) = _
  rw [quotientDifferential_product]
  simp only [tangentFrame, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply,
    tangentRechart_apply]

end LeanShared.ToralCatMap
