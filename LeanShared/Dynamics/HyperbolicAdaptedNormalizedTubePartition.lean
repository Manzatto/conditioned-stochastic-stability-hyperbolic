module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanFrames
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
public import LeanShared.Geometry.FiniteSmoothCapturePartition

/-! The actual adapted Euclidean tubes form a cover at every positive
radius. Compactness and the smooth partition theorem produce a finite
partition supported in these tubes, on an open neighborhood of the core.
Smoothness is always measured in the original manifold model. -/
@[expose] public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

abbrev ChartAtlas.NormalizedTubeIndex (atlas : ChartAtlas system) :=
  {i : Λ × Λ // i.1 ∈ atlas.centers ∧ i.2 ∈ atlas.patch i.1}

def ChartAtlas.normalizedTubeChart (atlas : ChartAtlas system)
    (i : atlas.NormalizedTubeIndex) : OpenPartialHomeomorph M system.EuclideanModel :=
  ContinuousCenteredFrameCharts.normalizedChart i.val.1.val i.val.2.val
    (atlas.inside i.val.1 i.property.2).2
    (system.euclideanReferenceFrame i.val.1 ⟨i.val.2,atlas.inside i.val.1 i.property.2⟩)

def ChartAtlas.normalizedTube (atlas : ChartAtlas system) (radius : ℝ)
    (i : atlas.NormalizedTubeIndex) : Set M :=
  (atlas.normalizedTubeChart i).source ∩ (atlas.normalizedTubeChart i) ⁻¹' ball 0 radius

theorem ChartAtlas.normalizedTube_open (atlas : ChartAtlas system) (radius : ℝ)
    (i : atlas.NormalizedTubeIndex) : IsOpen (atlas.normalizedTube radius i) :=
  (atlas.normalizedTubeChart i).isOpen_inter_preimage isOpen_ball

theorem ChartAtlas.normalizedTube_cover (atlas : ChartAtlas system) {radius : ℝ}
    (positive : 0 < radius) : Λ ⊆ ⋃ i, atlas.normalizedTube radius i := by
  intro m hm
  obtain ⟨c,hc,inside⟩ := mem_iUnion₂.mp (atlas.cover (mem_univ (⟨m,hm⟩ : Λ)))
  let i : atlas.NormalizedTubeIndex := ⟨(c,⟨m,hm⟩),hc,interior_subset inside⟩
  refine mem_iUnion.mpr ⟨i,?_⟩
  change m ∈ (atlas.normalizedTubeChart i).source ∧
    atlas.normalizedTubeChart i m ∈ ball 0 radius
  constructor
  · exact (atlas.inside c (interior_subset inside)).2
  · change ContinuousCenteredFrameCharts.normalizedChart c.val m
      (atlas.inside c (interior_subset inside)).2
      (system.euclideanReferenceFrame c ⟨⟨m,hm⟩,atlas.inside c (interior_subset inside)⟩) m ∈
        ball 0 radius
    rw [ContinuousCenteredFrameCharts.normalizedChart_center]
    exact mem_ball_self positive

variable [FiniteDimensional ℝ E] [CompactSpace M]

/-- Both the finite normalized tube family and its actual smooth cutoffs
are constructed internally, before a noise word or a horizon is selected. -/
theorem ChartAtlas.exists_normalizedTube_partition (atlas : ChartAtlas system) {radius : ℝ}
    (positive : 0 < radius) :
    ∃ s : Finset atlas.NormalizedTubeIndex,
      ∃ d : FiniteSmoothCapturePartition.Data (E := E) Λ
        (fun i : s => atlas.normalizedTube radius i.val), Λ ⊆ d.capture := by
  classical
  obtain ⟨s,cover⟩ := b.hyperbolic.compact.elim_finite_subcover
    (atlas.normalizedTube radius) (atlas.normalizedTube_open radius)
    (atlas.normalizedTube_cover positive)
  have selected : Λ ⊆ ⋃ i : s, atlas.normalizedTube radius i.val := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (cover hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxi⟩
  let d := FiniteSmoothCapturePartition.data (E := E) Λ b.hyperbolic.compact
    (fun i : s => atlas.normalizedTube radius i.val)
  exact ⟨s,d,d.reference (fun i => atlas.normalizedTube_open radius i.val) selected⟩

end LeanShared.HyperbolicAdaptedPatchSystem
