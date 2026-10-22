module
public import LeanShared.Dynamics.HyperbolicPseudoReferenceGeometry
public import LeanShared.Dynamics.HyperbolicIsometricFraming
import all LeanShared.Dynamics.HyperbolicEuclideanBlocks

/-! The constructed nearby-target native blocks become exact diagonal blocks
in the SAME chosen Euclidean frames at every incoming and outgoing point.
Isometric component frames preserve the actual contraction constants. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 2400000 in
theorem PseudoReferenceGeometry.exists_euclidean_blocks
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
    (d : PseudoReferenceGeometry h) (a : IsometricFraming h)
    (θ : ℝ) (positive : 0 < θ) (small : θ ≤ 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ x y : Λ, dist ((T ^ d.blockLength) x.val) y.val < η →
      let e := trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z) (d.index y).val
      y.val ∈ e.baseSet ∧ (T ^ d.blockLength) x.val ∈ e.baseSet ∧
      ∃ R : TangentSpace (𝓘(ℝ, E)) ((T ^ d.blockLength) x.val) ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) y.val,
      ∃ S : EuclideanSpace ℝ (Fin a.stableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.stableDimension),
      ∃ U : EuclideanSpace ℝ (Fin a.unstableDimension) ≃L[ℝ] EuclideanSpace ℝ (Fin a.unstableDimension),
        ‖R.toContinuousLinearMap‖ ≤ d.nativeBound ∧ ‖R.symm.toContinuousLinearMap‖ ≤ d.nativeBound ∧
        ‖S.toContinuousLinearMap‖ ≤ 1 / 4 ∧ ‖U.symm.toContinuousLinearMap‖ ≤ 1 / 4 ∧
        (a.whole y).symm.toContinuousLinearMap.comp
          (R.toContinuousLinearMap.comp
            ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T ^ d.blockLength : M ≃ₜ M) x.val).comp
              (a.whole x).toContinuousLinearMap)) =
          U.toContinuousLinearMap.prodMap S.toContinuousLinearMap ∧
        ‖(e.continuousLinearMapAt ℝ ((T ^ d.blockLength) x.val)).comp
          (R.symm.toContinuousLinearMap.comp (e.symmL ℝ y.val)) - ContinuousLinearMap.id ℝ E‖ < θ := by
  obtain ⟨η,positiveη,blocks⟩ := d.produce θ positive small
  refine ⟨η,positiveη,fun x y near => ?_⟩
  obtain ⟨source,target,R,S,U,normR,inverseR,stableBound,unstableBound,actionS,actionU,closeR⟩ := blocks x y near
  let s := ((a.stable x).toContinuousLinearEquiv.trans S).trans (a.stable y).symm.toContinuousLinearEquiv
  let u := ((a.unstable x).toContinuousLinearEquiv.trans U).trans (a.unstable y).symm.toContinuousLinearEquiv
  have normalizedS (v : EuclideanSpace ℝ (Fin a.stableDimension)) :
      (a.stable y (s v)).val = R
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T ^ d.blockLength : M ≃ₜ M) x.val (a.stable x v).val) := by
    change (a.stable y ((a.stable y).symm (S (a.stable x v)))).val = _
    rw [(a.stable y).apply_symm_apply]
    exact actionS (a.stable x v)
  have normalizedU (v : EuclideanSpace ℝ (Fin a.unstableDimension)) :
      (a.unstable y (u v)).val = R
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T ^ d.blockLength : M ≃ₜ M) x.val (a.unstable x v).val) := by
    change (a.unstable y ((a.unstable y).symm (U (a.unstable x v)))).val = _
    rw [(a.unstable y).apply_symm_apply]
    exact actionU (a.unstable x v)
  refine ⟨source,target,R,s,u,normR,inverseR,
    transport_bound (a.stable x) (a.stable y) S (by norm_num) stableBound,
    transport_bound (a.unstable y) (a.unstable x) U.symm (by norm_num) unstableBound,?_,closeR⟩
  apply ContinuousLinearMap.ext
  intro z
  apply (a.whole y).injective
  change a.whole y ((a.whole y).symm (R
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T ^ d.blockLength : M ≃ₜ M) x.val (a.whole x z)))) =
    a.whole y (u z.1,s z.2)
  rw [(a.whole y).apply_symm_apply]
  simp only [a.whole_apply,map_add]
  rw [normalizedU,normalizedS]

end LeanShared.HyperbolicBasicSet
