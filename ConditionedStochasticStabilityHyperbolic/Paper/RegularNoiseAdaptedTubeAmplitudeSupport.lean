module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeAmplitudeHolder

/-! The fixed finite tube cutoffs produce one compact Euclidean amplitude
support before any word length, controls, or itinerary labels are chosen.
This is the compact support entering the actual nonlinked row bound. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared HyperbolicBasicSet HyperbolicAdaptedPatchSystem
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {base : BasicData (E := E) T Λ V}
  {system : PatchSystem base} (atlas : ChartAtlas system)
  {radius : ℝ} {s : Finset atlas.NormalizedTubeIndex}
  (d : FiniteSmoothCapturePartition.Data (E := E) Λ
    (fun i : s => atlas.normalizedTube radius i.val))

def tubeAmplitudeSupport : Set system.EuclideanModel :=
  ⋃ i : s, ChartLocalization.localSupport (atlas.normalizedTubeChart i.val)
    (fun m => (d.beta i m : ℂ))

theorem tubeAmplitudeSupport_compact : IsCompact (tubeAmplitudeSupport atlas d) := by
  classical
  apply isCompact_iUnion
  intro i
  have support : tsupport (fun m => (d.beta i m : ℂ)) ⊆
      (atlas.normalizedTubeChart i.val).source :=
    (tsupport_comp_subset Complex.ofReal_zero (d.beta i)).trans
      ((d.support i).trans (fun _ hx => hx.1))
  exact ChartLocalization.localSupport_isCompact (atlas.normalizedTubeChart i.val)
    (fun m => (d.beta i m : ℂ)) support (HasCompactSupport.of_compactSpace _)

omit [CompactSpace M] in
theorem localSupport_subset_tubeAmplitudeSupport (i : s) :
    ChartLocalization.localSupport (atlas.normalizedTubeChart i.val)
      (fun m => (d.beta i m : ℂ)) ⊆ tubeAmplitudeSupport atlas d :=
  subset_iUnion (fun j : s => ChartLocalization.localSupport (atlas.normalizedTubeChart j.val)
    (fun m => (d.beta j m : ℂ))) i

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
