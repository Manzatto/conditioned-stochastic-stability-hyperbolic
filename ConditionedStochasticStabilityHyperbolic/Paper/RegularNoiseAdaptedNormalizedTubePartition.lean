module
public import LeanShared.Dynamics.HyperbolicAdaptedNormalizedTubePartition
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCompactManifold

/-! The supplied actual finite Whitney atlas implies ambient compactness.
Thus the actual adapted normalized tube partition needs no additional
compact-manifold assumption at the regular-noise endpoint. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

theorem Maps.exists_adapted_normalizedTube_partition {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    {radius : ℝ} (positive : 0 < radius) :
    ∃ s : Finset atlas.NormalizedTubeIndex,
      ∃ d : FiniteSmoothCapturePartition.Data (E := E) Λ
        (fun i : s => atlas.normalizedTube radius i.val), Λ ⊆ d.capture := by
  let := F.atlas.compactSpace
  exact atlas.exists_normalizedTube_partition positive

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
