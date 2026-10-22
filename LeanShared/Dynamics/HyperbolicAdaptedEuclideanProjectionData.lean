module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanProjectionEncoding

/-! The actual BasicData splitting produces normalized projections within
1/64 of the stable axis, with the correct ranks and kernel slope1/63. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet OrthogonalProductCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem PatchSystem.normalized_projection_data (system : PatchSystem b) (atlas : ChartAtlas system) :
    ∃ η : ℝ, 0 < η ∧ ∀ c ∈ atlas.centers, ∀ x (hx : x∈atlas.patch c), ∀ y : M,
      dist x.val y < η → y∈b.hyperbolic.normedAdaptedProjection.collar ∩ (chartAt E c.val).source ∧
      ‖system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y-system.euclideanSecondProjection‖ ≤ 1/64 ∧
      (∀ v, system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y
        (system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y v) =
          system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y v) ∧
      Module.finrank ℝ (system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y).range =
        system.framing.stableDimension ∧
      Module.finrank ℝ (system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y).ker =
        system.framing.unstableDimension ∧
      ∀ v ∈ (system.normalizedProjection c ⟨x,atlas.inside c hx⟩ y).ker,
        ‖system.euclideanSecondProjection v‖ ≤ (1/63:ℝ)*‖system.euclideanFirstProjection v‖ := by
  obtain ⟨η,positiveη,near⟩ := system.normalized_projection_radius atlas (by norm_num : (0:ℝ)<1/64)
  refine ⟨η,positiveη,fun c hc x hx y close => ?_⟩
  have geometry := near c hc x hx y close
  let p := b.hyperbolic.normedAdaptedProjection
  let ref : system.frameDomain c := ⟨x,atlas.inside c hx⟩
  let Qy := system.normalizedProjection c ref y
  let Qx := system.normalizedProjection c ref x.val
  have idemy : ∀v,Qy (Qy v)=Qy v := system.normalizedProjection_idempotent c ref y geometry.1.2 geometry.1.1
  have idemx : ∀v,Qx (Qx v)=Qx v := system.normalizedProjection_idempotent c ref x.val
    (atlas.inside c hx).2 (p.core_subset x.property)
  have rank : Module.finrank ℝ Qy.range = Module.finrank ℝ Qx.range :=
    CloseProjectionRanges.finrank_eq Qy Qx idemy idemx (by
      change ‖system.normalizedProjection c ref y-system.normalizedProjection c ref x.val‖ < 1
      rw [system.normalizedProjection_core c ref]
      exact geometry.2.trans (by norm_num))
  have kernelRank : Module.finrank ℝ Qy.ker = Module.finrank ℝ Qx.ker := by
    have left := Qy.toLinearMap.finrank_range_add_finrank_ker
    have right := Qx.toLinearMap.finrank_range_add_finrank_ker
    omega
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.euclideanReferenceFrame c ref)
  let A := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) x.val
      (atlas.inside c hx).2 L
  have commutes (v : TangentSpace (𝓘(ℝ,E)) x.val) : A (p.projection x.val v)=Qx (A v) :=
    system.normalizedProjection_encoding c ref x.val (atlas.inside c hx).2 v
  have stableCore : Module.finrank ℝ (p.projection x.val).range = system.framing.stableDimension := by
    change Module.finrank ℝ (p.stable x.val) = _
    rw [p.stable_core x.val x.property]
    simpa using
      (system.framing.stable x).toLinearEquiv.finrank_eq.symm
  have unstableCore : Module.finrank ℝ (p.projection x.val).ker = system.framing.unstableDimension := by
    change Module.finrank ℝ (p.unstable x.val) = _
    rw [p.unstable_core x.val x.property]
    simpa using
      (system.framing.unstable x).toLinearEquiv.finrank_eq.symm
  refine ⟨geometry.1,geometry.2.le,idemy,
    rank.trans ((ConjugateProjectionRanks.finrank_range A _ Qx commutes).trans stableCore),
    kernelRank.trans ((ConjugateProjectionRanks.finrank_ker A _ Qx commutes).trans unstableCore),?_⟩
  intro v member
  obtain ⟨z,rfl⟩ := system.euclideanEquiv.surjective v
  have zero : Qy (system.euclideanEquiv z)=0 := member
  have error := ((Qy-system.euclideanSecondProjection).le_opNorm (system.euclideanEquiv z)).trans
    (mul_le_mul_of_nonneg_right geometry.2.le (norm_nonneg _))
  change ‖Qy (system.euclideanEquiv z)-system.euclideanSecondProjection (system.euclideanEquiv z)‖ ≤ _ at error
  rw [zero,zero_sub,norm_neg] at error
  have second : system.euclideanSecondProjection (system.euclideanEquiv z)=system.euclideanEquiv (0,z.2) :=
    secondProjection_apply system.euclideanDimension z
  have first : system.euclideanFirstProjection (system.euclideanEquiv z)=system.euclideanEquiv (z.1,0) :=
    firstProjection_apply system.euclideanDimension z
  have normSecond : ‖system.euclideanEquiv (0,z.2)‖ = ‖z.2‖ := norm_second_axis system.euclideanDimension z.2
  have normFirst : ‖system.euclideanEquiv (z.1,0)‖ = ‖z.1‖ := norm_first_axis system.euclideanDimension z.1
  rw [second,normSecond] at error
  rw [second,first,normSecond,normFirst]
  have triangle : ‖system.euclideanEquiv z‖ ≤ ‖z.1‖+‖z.2‖ := norm_le_axis_sum system.euclideanDimension z
  nlinarith

end LeanShared.HyperbolicAdaptedPatchSystem
