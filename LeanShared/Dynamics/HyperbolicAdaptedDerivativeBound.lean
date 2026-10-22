module
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
public import LeanShared.Geometry.CompactFramedChartDerivativeBound
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Uniform actual one-step coordinate derivative bounds on the finite
adapted atlas, including all nearby target references. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet CenteredManifoldCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.derivative_bound {system : PatchSystem b} (atlas : ChartAtlas system)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M)) :
    ∃ B > 0, ∃ η > 0, ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
      ‖fderiv ℝ (centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm)) 0‖ ≤ B := by
  classical
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
  have localBounds (ij : Λ × Λ) := CompactFramedChartDerivativeBound.uniform_bound
    (P := EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension))
    (Q := EuclideanSpace ℝ (Fin system.framing.unstableDimension) ×
      EuclideanSpace ℝ (Fin system.framing.stableDimension))
    T forward (chartAt E ij.1.val) (chartAt E ij.2.val)
    (chart_mem_maximalAtlas ij.1.val) (chart_mem_maximalAtlas ij.2.val)
    (pair ij) (compactPair ij) (sourcePair ij) (targetPair ij) atlas.bound positiveBound
  choose B positiveB bounds using localBounds
  let total := ∑ ij ∈ atlas.centers.product atlas.centers, B ij
  have total_nonnegative : 0 ≤ total := Finset.sum_nonneg (fun ij _ => (positiveB ij).le)
  have commonBound (ij) (member : ij ∈ atlas.centers.product atlas.centers) : B ij ≤ total :=
    Finset.single_le_sum (fun ij _ => (positiveB ij).le) member
  obtain ⟨η, positiveη, commonTarget⟩ := CompactUniformCenteredCharts.common_positive
    atlas.centers ρ (fun c _ => positiveρ c)
  refine ⟨total + 1, by linarith, η, positiveη, ?_⟩
  intro c hc d hd x hx y hy near
  have targetCenter : T x.val ∈ Metric.cthickening (ρ d) (K d) :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ d) (K d) ⟨y, hy, rfl⟩
      (near.le.trans (commonTarget d hd))
  have center : x.val ∈ pair (c, d) := ⟨⟨x, hx, rfl⟩, targetCenter⟩
  exact ((bounds (c, d) x.val center _ _ (atlas.frame_bounds c hc x hx).1
    (atlas.frame_bounds d hd y hy).2 ((chartAt E d.val) y.val)).trans
      (commonBound (c, d) (Finset.mem_product.mpr ⟨hc, hd⟩))).trans (by linarith)

end LeanShared.HyperbolicAdaptedPatchSystem
