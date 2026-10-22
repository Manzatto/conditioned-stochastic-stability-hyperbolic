module
public import LeanShared.Geometry.CenteredNativeChartDerivative
public import LeanShared.Analysis.NativeCoordinateJacobianComparison

/-! Native unstable determinants compared with the literal affine-normalized
coordinate derivative, even when the manifold model and Fourier model differ.
Only the two actual endpoint encodings enter the comparison constant. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold Topology
namespace LeanShared.CenteredTangentJacobianComparison
open CenteredManifoldCoordinates
variable {E P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

def encoding (c : OpenPartialHomeomorph M E)
    (hc : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E))) (x : M) (inside : x∈c.source)
    (L : P ≃L[ℝ] E) : TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] P :=
  ((hc.mfderiv inside).trans (NormedSpace.fromTangentSpace (𝕜:=ℝ) (c x))).trans L.symm

theorem native_jacobian_le (H : M→M) (x : M)
    (c d : OpenPartialHomeomorph M E)
    (hc : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (hd : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (inside : x∈c.source) (target : H x∈d.source)
    (L R : P ≃L[ℝ] E) (a b : E)
    (smooth : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)
    (D : TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) (H x))
    (differential : D.toContinuousLinearMap=mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)
    (U : Submodule ℝ (TangentSpace (𝓘(ℝ,E)) x))
    (Csource CtargetInverse : ℝ) (sourceNonnegative : 0≤Csource)
    (targetNonnegative : 0≤CtargetInverse)
    (sourceBound : ∀ v,‖encoding c hc x inside L v‖≤Csource*‖v‖)
    (targetBound : ∀ v,‖(encoding d hd (H x) target R).symm v‖≤CtargetInverse*‖v‖) :
    (D.toLinearMap.domRestrict U).normDet ≤
      (GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) CtargetInverse*
        GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) Csource)*
      ((fderiv ℝ (centered L R a b (d ∘ H ∘ c.symm)) (L.symm (c x-a))).toLinearMap.domRestrict
        ((encoding c hc x inside L).toContinuousLinearMap.comp U.subtypeL).toLinearMap.range).normDet := by
  have relation (v : TangentSpace (𝓘(ℝ,E)) x) :
      encoding d hd (H x) target R (D v) =
        fderiv ℝ (centered L R a b (d ∘ H ∘ c.symm)) (L.symm (c x-a))
          (encoding c hc x inside L v) := by
    have native := CenteredNativeChartDerivative.intertwines H x c d hc hd inside target L R a b smooth v
    have Dv : D v=mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x v :=
      congrArg (fun A : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) (H x) => A v) differential
    have sourceFormula (w : TangentSpace (𝓘(ℝ,E)) x) :
        (hc.mfderiv inside) w=mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) c x w := rfl
    have targetFormula (w : TangentSpace (𝓘(ℝ,E)) (H x)) :
        (hd.mfderiv target) w=mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) d (H x) w := rfl
    simpa only [encoding,ContinuousLinearEquiv.trans_apply,Dv,sourceFormula,targetFormula] using native
  exact NativeCoordinateJacobianComparison.native_le_coordinate D
    (encoding c hc x inside L) (encoding d hd (H x) target R) U
    (fderiv ℝ (centered L R a b (d ∘ H ∘ c.symm)) (L.symm (c x-a))) relation
    Csource CtargetInverse sourceNonnegative targetNonnegative sourceBound targetBound

/-- A global extension equal near the actual source point has exactly the
same derivative determinant there. No norm of a whole chart word is used. -/
theorem native_jacobian_le_of_eventuallyEq (H : M→M) (x : M)
    (c d : OpenPartialHomeomorph M E)
    (hc : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (hd : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (inside : x∈c.source) (target : H x∈d.source)
    (L R : P ≃L[ℝ] E) (a b : E)
    (smooth : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)
    (D : TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) (H x))
    (differential : D.toContinuousLinearMap=mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)
    (U : Submodule ℝ (TangentSpace (𝓘(ℝ,E)) x))
    (global : P→P)
    (agreement : global =ᶠ[𝓝 (L.symm (c x-a))] centered L R a b (d ∘ H ∘ c.symm))
    (Csource CtargetInverse : ℝ) (sourceNonnegative : 0≤Csource)
    (targetNonnegative : 0≤CtargetInverse)
    (sourceBound : ∀ v,‖encoding c hc x inside L v‖≤Csource*‖v‖)
    (targetBound : ∀ v,‖(encoding d hd (H x) target R).symm v‖≤CtargetInverse*‖v‖) :
    (D.toLinearMap.domRestrict U).normDet ≤
      (GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) CtargetInverse*
        GraphJacobian.densityBound (ι:=Fin (Module.finrank ℝ U)) Csource)*
      ((fderiv ℝ global (L.symm (c x-a))).toLinearMap.domRestrict
        ((encoding c hc x inside L).toContinuousLinearMap.comp U.subtypeL).toLinearMap.range).normDet := by
  rw [agreement.fderiv_eq]
  exact native_jacobian_le H x c d hc hd inside target L R a b smooth D differential U
    Csource CtargetInverse sourceNonnegative targetNonnegative sourceBound targetBound

end LeanShared.CenteredTangentJacobianComparison
