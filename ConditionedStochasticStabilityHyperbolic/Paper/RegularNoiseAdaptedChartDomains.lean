module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedChartWindow
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCompactManifold
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWordTarget
import all LeanShared.Geometry.CompactUniformCenteredCharts
import Mathlib.Tactic.FieldSimp

/-! Genuine chart-domain validity of the actual one-step noisy maps on a
common closed coordinate ball in every nearby pair of adapted patches. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem Maps.adapted_chart_domains {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ radius > 0, ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y, y ∈ atlas.patch d →
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
      ∀ z, ‖z‖ ≤ radius →
        (chartAt E c.val) x.val + L z ∈ (chartAt E c.val).target ∧
        F.family ε control.val ((chartAt E c.val).symm ((chartAt E c.val) x.val + L z)) ∈
          (chartAt E d.val).source := by
  let : CompactSpace M := F.atlas.compactSpace
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
  let domain (ij : Λ × Λ) := (chartAt E ij.1.val).target ∩
    (T ∘ (chartAt E ij.1.val).symm) ⁻¹' (chartAt E ij.2.val).source
  have openDomain (ij : Λ × Λ) : IsOpen (domain ij) :=
    (chartAt E ij.1.val).isOpen_inter_preimage_symm ((chartAt E ij.2.val).open_source.preimage T.continuous)
  have validCenters (ij : Λ × Λ) : centers ij ⊆ domain ij := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(chartAt E ij.1.val).map_source (sourcePair ij hx), ?_⟩
    change T ((chartAt E ij.1.val).symm (chartAt E ij.1.val x)) ∈ (chartAt E ij.2.val).source
    rw [(chartAt E ij.1.val).left_inv (sourcePair ij hx)]
    exact targetPair ij hx
  have padded (ij : Λ × Λ) := (compactCenters ij).exists_cthickening_subset_open
    (openDomain ij) (validCenters ij)
  choose radii positiveRadii tubeInside using padded
  let tube (ij : Λ × Λ) := Metric.cthickening (radii ij) (centers ij)
  have compactTube (ij : Λ × Λ) : IsCompact (tube ij) := (compactCenters ij).cthickening
  have compactStarts (ij : Λ × Λ) : IsCompact ((chartAt E ij.1.val).symm '' tube ij) :=
    (compactTube ij).image_of_continuousOn ((chartAt E ij.1.val).symm.continuousOn.mono
      (fun _ hx => (tubeInside ij hx).1))
  have targetStarts (ij : Λ × Λ) : MapsTo ((T : M → M)^[1])
      ((chartAt E ij.1.val).symm '' tube ij) (chartAt E ij.2.val).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (tubeInside ij hz).2
  have windows (ij : Λ × Λ) := F.exists_uniform_word_target 1 _ _ (compactStarts ij)
    (chartAt E ij.2.val).open_source (targetStarts ij)
  choose noise positiveNoise targets using windows
  have positiveB : 0 < atlas.bound := lt_of_lt_of_le zero_lt_one atlas.one_le_bound
  obtain ⟨radius, positiveRadius, commonRadius⟩ := CompactUniformCenteredCharts.common_positive
    (atlas.centers.product atlas.centers) (fun ij => radii ij / atlas.bound)
      (fun ij _ => div_pos (positiveRadii ij) positiveB)
  obtain ⟨η, positiveη, commonTarget⟩ := CompactUniformCenteredCharts.common_positive
    atlas.centers ρ (fun c _ => positiveρ c)
  obtain ⟨cutoff, positiveCutoff, commonNoise⟩ := CompactUniformCenteredCharts.common_positive
    (atlas.centers.product atlas.centers) (fun ij => (noise ij : ℝ))
      (fun ij _ => by exact_mod_cast positiveNoise ij)
  refine ⟨radius, positiveRadius, η, positiveη, min F.window ⟨cutoff, positiveCutoff.le⟩,
    lt_min F.window_positive positiveCutoff, min_le_left _ _, ?_⟩
  intro ε hp hw control c hc d hd x hx y hy near
  dsimp only
  intro z small
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
  have member : (c, d) ∈ atlas.centers.product atlas.centers := Finset.mem_product.mpr ⟨hc, hd⟩
  have targetCenter : T x.val ∈ Metric.cthickening (ρ d) (K d) :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ d) (K d) ⟨y, hy, rfl⟩
      (near.le.trans (commonTarget d hd))
  have center : x.val ∈ pair (c, d) := ⟨⟨x, hx, rfl⟩, targetCenter⟩
  have displacement : dist ((chartAt E c.val) x.val + L z) ((chartAt E c.val) x.val) ≤ radii (c, d) := by
    rw [dist_eq_norm, add_sub_cancel_left]
    calc
      ‖L z‖ ≤ ‖L.toContinuousLinearMap‖ * ‖z‖ := L.toContinuousLinearMap.le_opNorm z
      _ ≤ atlas.bound * (radii (c, d) / atlas.bound) :=
        mul_le_mul (atlas.frame_bounds c hc x hx).1 (small.trans (commonRadius (c, d) member))
          (norm_nonneg _) positiveB.le
      _ = radii (c, d) := by field_simp
  have inTube : (chartAt E c.val) x.val + L z ∈ tube (c, d) :=
    Metric.mem_cthickening_of_dist_le _ ((chartAt E c.val) x.val) (radii (c, d)) (centers (c, d))
      (mem_image_of_mem _ center) displacement
  have localNoise : ε ≤ noise (c, d) := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr (hw.trans (min_le_right _ _))).trans (commonNoise (c, d) member))
  refine ⟨(tubeInside (c, d) inTube).1, ?_⟩
  have output := targets (c, d) ε hp localNoise (fun _ => control) (mem_image_of_mem _ inTube)
  simpa only [FiniteJetComposition.word, Function.comp_def, Function.id_def] using output

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
