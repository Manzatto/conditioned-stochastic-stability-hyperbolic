module
public import LeanShared.Geometry.CenteredNativeChartDerivative
public import LeanShared.Geometry.FlatTangentIsometry

/-! Equal genuine coordinate first jets give equal native restricted
Jacobians. Equal endpoint fibers are transported by an actual isometry;
the original Riemannian metric is retained throughout. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold
namespace LeanShared.NativeFirstJetJacobianExt
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

def tangentTransport (x y : M) (same : x = y) :
    TangentSpace (𝓘(ℝ,E)) x ≃ₗᵢ[ℝ] TangentSpace (𝓘(ℝ,E)) y := by
  subst y
  exact LinearIsometryEquiv.refl ℝ _

omit [FiniteDimensional ℝ E] in
theorem tangentTransport_apply (x y : M) (same : x = y) (v : TangentSpace (𝓘(ℝ,E)) x) :
    (tangentTransport x y same v : E) = v := by
  subst y
  rfl

theorem normDet_eq (f g : M → M) (x : M) (c d : OpenPartialHomeomorph M E)
    (hc : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (hd : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (source : x ∈ c.source) (targetF : f x ∈ d.source) (targetG : g x ∈ d.source)
    (smoothF : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x)
    (smoothG : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) g x)
    (sameValue : f x = g x)
    (sameJet : fderiv ℝ (d ∘ f ∘ c.symm) (c x) = fderiv ℝ (d ∘ g ∘ c.symm) (c x))
    (U : Submodule ℝ (TangentSpace (𝓘(ℝ,E)) x)) :
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict U).normDet =
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) g x).toLinearMap.domRestrict U).normDet := by
  have derivative_equal (v : TangentSpace (𝓘(ℝ,E)) x) :
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x v : E) = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) g x v := by
    have first := CenteredNativeChartDerivative.intertwines f x c d hc hd source targetF
      (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ E) 0 0 smoothF v
    have second := CenteredNativeChartDerivative.intertwines g x c d hc hd source targetG
      (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ E) 0 0 smoothG v
    have uncenter (k : E → E) : CenteredManifoldCoordinates.centered
        (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ E) 0 0 k = k := by
      funext z
      change k (0+z)-0 = k z
      rw [zero_add,sub_zero]
    rw [uncenter] at first second
    simp at first second
    rw [sameJet] at first
    rw [← sameValue] at second
    have encoded := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (f x))).injective
      (first.trans second.symm)
    exact (hd.mfderiv targetF).injective encoded
  let J := tangentTransport (E := E) (g x) (f x) sameValue.symm
  have actual (v : TangentSpace (𝓘(ℝ,E)) x) :
      J (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) g x v) = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x v := by
    change tangentTransport (E := E) (g x) (f x) sameValue.symm _ = _
    rw [tangentTransport_apply]
    exact (derivative_equal v).symm
  have equal : J.toLinearIsometry.toLinearMap.comp
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) g x).toLinearMap.domRestrict U) =
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict U := by
    ext v
    exact actual v.val
  exact (congrArg LinearMap.normDet equal).symm.trans
    (NormDetIsometry.comp _ J.toLinearIsometry)

end LeanShared.NativeFirstJetJacobianExt
