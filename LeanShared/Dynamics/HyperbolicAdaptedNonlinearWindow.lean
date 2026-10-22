module
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
public import LeanShared.Geometry.CompactMisalignedAtlasRadius
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import Mathlib.Topology.MetricSpace.Thickening

/-! Common nonlinear radii for every nearby pair of actual adapted atlas
references. Compactness is needed only on the actual core patches, not on
the ambient manifold. The map is the original one-step generator. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet CenteredManifoldCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.nonlinear_window {system : PatchSystem b} (atlas : ChartAtlas system)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ radius > 0, ∃ η > 0, ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
      ∀ z, ‖z‖ ≤ radius →
        (chartAt E c.val) x.val + L z ∈ (chartAt E c.val).target ∧
        T ((chartAt E c.val).symm ((chartAt E c.val) x.val + L z)) ∈ (chartAt E d.val).source ∧
        DifferentiableAt ℝ (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
          (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)) z ∧
        ‖fderiv ℝ (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
            (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)) z -
          fderiv ℝ (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
            (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)) 0‖ < δ := by
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
  have positiveBound : 0 < atlas.bound := lt_of_lt_of_le zero_lt_one atlas.one_le_bound
  have localRadii (ij : Λ × Λ) := CompactMisalignedAtlasRadius.exists_radius
    (P := EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension))
    (Q := EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension))
    T forward (chartAt E ij.1.val) (chartAt E ij.2.val)
    (chart_mem_maximalAtlas ij.1.val) (chart_mem_maximalAtlas ij.2.val)
    (pair ij) (compactPair ij) (sourcePair ij) (targetPair ij)
    atlas.bound δ positiveBound positiveδ
  choose radii positiveRadii estimates using localRadii
  obtain ⟨radius, positiveRadius, commonRadius⟩ := CompactUniformCenteredCharts.common_positive
    (atlas.centers.product atlas.centers) radii (fun ij _ => positiveRadii ij)
  obtain ⟨η, positiveη, commonTarget⟩ := CompactUniformCenteredCharts.common_positive
    atlas.centers ρ (fun c _ => positiveρ c)
  refine ⟨radius, positiveRadius, η, positiveη, ?_⟩
  intro c hc d hd x hx y hy near
  dsimp only
  intro z small
  have targetCenter : T x.val ∈ Metric.cthickening (ρ d) (K d) :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ d) (K d) ⟨y, hy, rfl⟩
      (near.le.trans (commonTarget d hd))
  have center : x.val ∈ pair (c, d) := ⟨⟨x, hx, rfl⟩, targetCenter⟩
  exact estimates (c, d) x.val center _ _ (atlas.frame_bounds c hc x hx).1
    (atlas.frame_bounds d hd y hy).2 ((chartAt E d.val) y.val) z
    (small.trans (commonRadius (c, d) (Finset.mem_product.mpr ⟨hc, hd⟩)))

end LeanShared.HyperbolicAdaptedPatchSystem
