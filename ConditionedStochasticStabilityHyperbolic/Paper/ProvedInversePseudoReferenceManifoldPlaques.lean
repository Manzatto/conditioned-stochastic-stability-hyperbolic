module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInversePseudoReferencePlaques
public import LeanShared.Dynamics.RandomCocycleChartTransport

/-! Actual manifold plaques along arbitrary sufficiently accurate
pseudo-reference orbits. All local maps are literal noisy finite words,
and all time-dependent charts are the constructed coherent charts. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.FiniteJetComposition LeanShared.PseudoReferenceCoordinateMaps
open LeanShared.HyperbolicBasicSet

set_option maxHeartbeats 2400000 in
theorem InverseFamily.exists_pseudo_reference_manifold_plaques
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {h : HyperbolicData (E := E) T.symm Λ}
    {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (geometry : PseudoReferenceGeometry h) (a : IsometricFraming h)
    (cap : ℝ) (positiveCap : 0 < cap) :
    ∃ radius : ℝ, 0 < radius ∧ radius ≤ cap ∧
      ∃ tolerance : ℝ, 0 < tolerance ∧ ∃ window : ℝ≥0, 0 < window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ window → ∀ reference : ℕ → Λ,
      (∀ n, dist ((T.symm : M → M)^[geometry.blockLength] (reference (n + 1)).val)
        (reference n).val < tolerance) →
      ∃ d : LeanShared.RandomCocycleChartTransport.Data M (ℕ → cube (ι := ι) ε)
        (EuclideanSpace ℝ (Fin a.unstableDimension)) (EuclideanSpace ℝ (Fin a.stableDimension)),
        d.localMap.radius = radius ∧
        (∀ n y controls, d.map n (y,controls) =
          word (fun j => fun y => J.map ε ((controls j).val,y)) geometry.blockLength y) ∧
        ∀ n, d.coordinates n = normalizedChart geometry a.whole (reference n) := by
  obtain ⟨radius,positiveRadius,radiusCap,targets,tolerance,positiveTolerance,window,positiveWindow,produce⟩ :=
    J.exists_pseudo_reference_plaques regularity deterministic inverse geometry a cap positiveCap
  refine ⟨radius,positiveRadius,radiusCap,tolerance,positiveTolerance,window,positiveWindow,
    fun ε hp hw reference step => ?_⟩
  obtain ⟨localData,radiusEq,mapIdentity,validity⟩ := produce ε hp hw reference step
  have target (n : ℕ) : Metric.ball 0 localData.radius ⊆
      (normalizedChart geometry a.whole (reference n)).target := by
    intro z hz
    have bound : ‖z‖ ≤ radius := by
      have strict : ‖z‖ < localData.radius := by simpa only [Metric.mem_ball,dist_zero_right] using hz
      exact strict.le.trans radiusEq.le
    change chart geometry (reference n) (reference n).val + linear geometry a.whole (reference n) z ∈
      (chart geometry (reference n)).target
    exact targets (reference n) z bound
  let d : LeanShared.RandomCocycleChartTransport.Data M (ℕ → cube (ι := ι) ε)
      (EuclideanSpace ℝ (Fin a.unstableDimension)) (EuclideanSpace ℝ (Fin a.stableDimension)) := {
    coordinates := fun n => normalizedChart geometry a.whole (reference n)
    localMap := localData
    map := fun _ p => word (fun j => fun y => J.map ε ((p.2 j).val,y)) geometry.blockLength p.1
    target := target
    conjugacy := by
      intro n controls z hz
      have bound : ‖z‖ ≤ radius := hz.le.trans radiusEq.le
      refine ⟨validity n z bound controls,?_⟩
      exact (mapIdentity n controls z).symm }
  exact ⟨d,radiusEq,(fun _ _ _ => rfl),fun _ => rfl⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
