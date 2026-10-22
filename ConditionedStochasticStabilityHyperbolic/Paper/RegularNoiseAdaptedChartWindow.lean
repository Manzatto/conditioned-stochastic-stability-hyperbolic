module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseBoundedFrameTube
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import Mathlib.Topology.MetricSpace.Thickening

/-! Literal one-step noisy maps have a common C1 window on every nearby
pair of the actual adapted atlas references, with all original controls. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem
open LeanShared.HyperbolicBasicSet LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem Maps.adapted_chart_noise_window {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (regularity : 1 ≤ r) (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    {system : PatchSystem b} (atlas : ChartAtlas system) (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ radius > 0, ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
      let f := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm)
      let g := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)
      ∀ z, ‖z‖ ≤ radius → DifferentiableAt ℝ f z ∧
        ‖f z - g z‖ + ‖fderiv ℝ f z - fderiv ℝ g z‖ ≤ δ := by
  let K (c : Λ) := Subtype.val '' atlas.patch c
  have compactK (c : Λ) : IsCompact (K c) := (atlas.compact c).image continuous_subtype_val
  have sourceK (c : Λ) : K c ⊆ (chartAt E c.val).source := by
    rintro _ ⟨x, hx, rfl⟩
    exact (atlas.inside c hx).2
  have tubes (c : Λ) := (compactK c).exists_cthickening_subset_open
    (chartAt E c.val).open_source (sourceK c)
  choose ρ positiveρ tubeInside using tubes
  let pair (ij : Λ × Λ) := K ij.1 ∩ T ⁻¹' Metric.cthickening (ρ ij.2) (K ij.2)
  have compactPair (ij : Λ × Λ) : IsCompact (pair ij) :=
    (compactK ij.1).inter_right (Metric.isClosed_cthickening.preimage T.continuous)
  have sourcePair (ij : Λ × Λ) : pair ij ⊆ (chartAt E ij.1.val).source :=
    fun _ hx => sourceK ij.1 hx.1
  have targetPair (ij : Λ × Λ) : MapsTo T (pair ij) (chartAt E ij.2.val).source :=
    fun _ hx => tubeInside ij.2 hx.2
  let centers (ij : Λ × Λ) := chartAt E ij.1.val '' pair ij
  have compactCenters (ij : Λ × Λ) : IsCompact (centers ij) :=
    (compactPair ij).image_of_continuousOn ((chartAt E ij.1.val).continuousOn.mono (sourcePair ij))
  have validCenters (ij : Λ × Λ) : centers ij ⊆ (chartAt E ij.1.val).target ∩
      ((T : M → M)^[1] ∘ (chartAt E ij.1.val).symm) ⁻¹' (chartAt E ij.2.val).source := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(chartAt E ij.1.val).map_source (sourcePair ij hx), ?_⟩
    change T ((chartAt E ij.1.val).symm (chartAt E ij.1.val x)) ∈ (chartAt E ij.2.val).source
    rw [(chartAt E ij.1.val).left_inv (sourcePair ij hx)]
    exact targetPair ij hx
  have windows (ij : Λ × Λ) := F.uniform_centered_word_c1_tube
    (P := EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension))
    (Q := EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension))
    regularity forward (chartAt E ij.1.val) (chartAt E ij.2.val)
    (chart_mem_maximalAtlas ij.1.val) (chart_mem_maximalAtlas ij.2.val) 1
    (centers ij) (compactCenters ij) (validCenters ij) atlas.bound δ atlas.one_le_bound positiveδ
  choose radii positiveRadii noise positiveNoise estimates using windows
  obtain ⟨radius, positiveRadius, commonRadius⟩ := CompactUniformCenteredCharts.common_positive
    (atlas.centers.product atlas.centers) radii (fun ij _ => positiveRadii ij)
  obtain ⟨η, positiveη, commonTarget⟩ := CompactUniformCenteredCharts.common_positive
    atlas.centers ρ (fun c _ => positiveρ c)
  obtain ⟨cutoff, positiveCutoff, commonNoise⟩ := CompactUniformCenteredCharts.common_positive
    (atlas.centers.product atlas.centers) (fun ij => (noise ij : ℝ))
      (fun ij _ => by exact_mod_cast positiveNoise ij)
  refine ⟨radius, positiveRadius, η, positiveη, ⟨cutoff, positiveCutoff.le⟩, positiveCutoff, ?_⟩
  intro ε hp hw control c hc d hd x hx y hy near
  dsimp only
  intro z small
  have member : (c, d) ∈ atlas.centers.product atlas.centers := Finset.mem_product.mpr ⟨hc, hd⟩
  have targetCenter : T x.val ∈ Metric.cthickening (ρ d) (K d) :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ d) (K d) ⟨y, hy, rfl⟩
      (near.le.trans (commonTarget d hd))
  have center : x.val ∈ pair (c, d) := ⟨⟨x, hx, rfl⟩, targetCenter⟩
  have localNoise : ε ≤ noise (c, d) := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr hw).trans (commonNoise (c, d) member))
  have result := estimates (c, d) ε hp localNoise (fun _ => control)
    ((chartAt E c.val) x.val) (mem_image_of_mem _ center) _ _
    (atlas.frame_bounds c hc x hx).1 (atlas.frame_bounds d hd y hy).2
    ((chartAt E d.val) y.val) z (small.trans (commonRadius (c, d) member))
  simpa only [FiniteJetComposition.word, Function.comp_def, Function.id_def, Function.iterate_one] using result

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
