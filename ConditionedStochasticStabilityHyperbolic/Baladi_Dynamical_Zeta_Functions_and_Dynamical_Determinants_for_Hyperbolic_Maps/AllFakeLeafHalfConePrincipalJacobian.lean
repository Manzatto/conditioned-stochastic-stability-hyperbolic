module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafTangentProjection
public import LeanShared.Analysis.ProjectionConeFakeLeafSlope
public import LeanShared.Analysis.TransverseSubspaceJacobian
import all LeanShared.Analysis.FakeLeafGraph

/-! Explicit word-independent principal-Jacobian constants for the literal
half-cone fake leaves. All tangent slopes and image transversality are derived
from the actual endpoint projection and whole-word image estimates. -/
public noncomputable section
open Set
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
theorem C1Embedded.principal_jacobian_of_half_cone {V : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded V Γ)
    (positive : 0 < Module.finrank ℝ Vᗮ)
    (fake : FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone V.starProjection (1/2))
      (Module.finrank ℝ Vᗮ) Γ = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (sourceSlope : ∀x∈Γ,∀y∈Γ, ‖Vᗮ.starProjection (x-y)‖≤L*‖V.starProjection (x-y)‖)
    (u : V) (hu : u ∈ FakeLeafGraph.parameterDomain V Γ)
    (U S : Submodule ℝ E) (A : E ≃L[ℝ] E) (Q : E →L[ℝ] U)
    (close : ‖V.starProjection-U.starProjection‖≤(1/8:ℝ))
    (unstableDimension : Module.finrank ℝ V=Module.finrank ℝ U)
    (stableDimension : Module.finrank ℝ S=Module.finrank ℝ Uᗮ)
    (stable : ∀v:S, Q (A v)=0)
    (stableSlope : ∀v:S, ‖V.starProjection (v:E)‖≤(1/8:ℝ)*‖Vᗮ.starProjection (v:E)‖)
    (imageSlope : ∀v:U, ‖Vᗮ.starProjection (A v)‖≤(1/8:ℝ)*‖V.starProjection (A v)‖)
    (targetProjection : ∀v:E, ‖V.starProjection v‖≤‖Q v‖+(1/8:ℝ)*‖v‖) :
    let g := ConeGraphGeometry.graphPoint V (FakeLeafGraph.heightExtension V Γ hL sourceSlope)
    (A.toLinearMap.domRestrict U).normDet ≤
      (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) 2 *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) 9 *
        (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ *
          GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (8/3))) *
      (A.toLinearMap.domRestrict (fderiv ℝ g u).toLinearMap.range).normDet := by
  intro g
  have fixedSecants := ProjectionConeFakeLeafSlope.half_cone_secants V positive Γ fake
  have actualSecants (x:E) (hx:x∈Γ) (y:E) (hy:y∈Γ) :
      ‖Uᗮ.starProjection (x-y)‖≤(8/3:ℝ)*‖U.starProjection (x-y)‖ := by
    exact ProjectionConeFakeLeafSlope.transport V U (x-y) (by norm_num) (by norm_num)
      close (fixedSecants x hx y hy) (by norm_num) (by norm_num)
  have complementClose : ‖Vᗮ.starProjection-Uᗮ.starProjection‖≤(1/8:ℝ) := by
    rw [V.starProjection_orthogonal,U.starProjection_orthogonal]
    have identity : (ContinuousLinearMap.id ℝ E-V.starProjection)-
        (ContinuousLinearMap.id ℝ E-U.starProjection)=-(V.starProjection-U.starProjection) := by abel
    rw [identity,norm_neg]
    exact close
  have actualStable (v:S) : ‖U.orthogonalProjectionOnto (v:E)‖≤
      (1/3:ℝ)*‖Uᗮ.orthogonalProjectionOnto (v:E)‖ := by
    have estimate := ProjectionConeFakeLeafSlope.transport Vᗮ Uᗮ (v:E)
      (by norm_num) (by norm_num) complementClose
      (show ‖Vᗮᗮ.starProjection (v:E)‖≤(1/8:ℝ)*‖Vᗮ.starProjection (v:E)‖ by
        simpa only [Submodule.orthogonal_orthogonal] using stableSlope v)
      (by norm_num) (show (1/8:ℝ)+(1/8)*(1+1/8)≤(1/3)*(1-(1/8)*(1+1/8)) by norm_num)
    simpa only [Submodule.orthogonal_orthogonal,Submodule.starProjection_apply,Submodule.norm_coe] using estimate
  have transverse : ∀v:(A.toContinuousLinearMap.comp U.subtypeL).toLinearMap.range,
      ‖(v:E)‖≤2*‖Q v‖ := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    change A (w:E)=v.val at hw
    have slope := imageSlope w
    rw [hw] at slope
    have triangle : ‖(v:E)‖≤‖V.starProjection (v:E)‖+‖Vᗮ.starProjection (v:E)‖ := by
      simpa only [V.starProjection_add_starProjection_orthogonal] using
        norm_add_le (V.starProjection (v:E)) (Vᗮ.starProjection (v:E))
    have projection := targetProjection v
    nlinarith [norm_nonneg (Q v)]
  have domainOpen := embedded.projection_open hL sourceSlope
  have heightRegular := ((embedded.heightExtension_contDiffOn hL sourceSlope).differentiableOn
    one_ne_zero u hu).differentiableAt (domainOpen.mem_nhds hu)
  have derivative := V.subtypeL.hasFDerivAt.add
    (Vᗮ.subtypeL.hasFDerivAt.comp u heightRegular.hasFDerivAt)
  have differential : fderiv ℝ g u = IntrinsicGraphJacobian.graphDifferential V
      (fderiv ℝ (FakeLeafGraph.heightExtension V Γ hL sourceSlope) u) := derivative.fderiv
  have injective : Function.Injective (fderiv ℝ g u) := by
    rw [differential]
    exact IntrinsicGraphJacobian.graphDifferential_injective V _
  have dimension : Module.finrank ℝ (fderiv ℝ g u).toLinearMap.range=Module.finrank ℝ U :=
    (LinearMap.finrank_range_of_inj injective).trans unstableDimension
  have result := TransverseSubspaceJacobian.compare U S (fderiv ℝ g u).toLinearMap.range A Q
    stableDimension dimension stable (by norm_num : (0:ℝ)≤1/3)
    (by norm_num : (0:ℝ)≤8/3) (by norm_num : (0:ℝ)≤2) actualStable
    (embedded.tangent_projection_slope hL sourceSlope U (8/3) actualSecants u hu)
    transverse (by norm_num : (1/3:ℝ)*(8/3)<1)
  norm_num only at result
  exact result
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
