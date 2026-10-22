module
public import LeanShared.Dynamics.HyperbolicAdaptedOriginalModelTubes

/-! A genuine continuous linear model equivalence is obtained from an
actual adapted frame at an actual point of the nonempty core. This uses
the given original norm and does not install an inner product on it. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

def ChartAtlas.originalModelEquiv (atlas : ChartAtlas system) :
    E ≃L[ℝ] system.EuclideanModel := by
  let c : Λ := ⟨b.nonempty.choose,b.nonempty.choose_spec⟩
  have patch : c ∈ atlas.patch c := interior_subset (atlas.center_mem c)
  let ref : system.frameDomain c := ⟨c,atlas.inside c patch⟩
  exact (ContinuousCenteredFrameCharts.chartFrame c.val c.val
    (atlas.inside c patch).2 (system.euclideanReferenceFrame c ref)).symm

theorem ChartAtlas.originalModelEquiv_inverse (atlas : ChartAtlas system) (v : E) :
    (atlas.originalModelEquiv).symm (atlas.originalModelEquiv v) = v :=
  (atlas.originalModelEquiv).symm_apply_apply v

end LeanShared.HyperbolicAdaptedPatchSystem
