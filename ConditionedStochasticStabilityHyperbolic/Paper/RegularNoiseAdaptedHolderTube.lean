module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCenteredHolderTube
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCalculus
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! Actual uniform first-derivative Holder controls on the same fixed
adapted atlas, in its genuine Euclidean model and with every original
noise control. All windows and constants precede the moving references. -/
public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.CenteredManifoldCoordinates
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem Maps.adapted_euclidean_holder_tube {r α : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ radius > 0, ∃ η > 0, ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ control : cube (ι := ι) ε,
      ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.euclideanReferenceFrame d ⟨y, atlas.inside d hy⟩)
      let h := centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ F.family ε control.val ∘ (chartAt E c.val).symm)
      (∀ z, ‖z‖ ≤ radius → ‖fderiv ℝ h z‖ ≤ B) ∧
      ∀ z, ‖z‖ ≤ radius → ∀ w, ‖w‖ ≤ radius →
        ‖fderiv ℝ h z-fderiv ℝ h w‖ ≤ C*‖z-w‖^α := by
  classical
  let K (c : Λ) := Subtype.val '' atlas.patch c
  have compactK (c : Λ) : IsCompact (K c) := (atlas.compact c).image continuous_subtype_val
  have sourceK (c : Λ) : K c ⊆ (chartAt E c.val).source := by
    rintro _ ⟨x, hx, rfl⟩
    exact (atlas.inside c hx).2
  have tubes (c : Λ) := (compactK c).exists_cthickening_subset_open
    (chartAt E c.val).open_source (sourceK c)
  choose ρ positiveρ tubeInside using tubes
  let pair (ij : Λ × Λ) := K ij.1 ∩ T ⁻¹' cthickening (ρ ij.2) (K ij.2)
  have compactPair (ij : Λ × Λ) : IsCompact (pair ij) :=
    (compactK ij.1).inter_right (isClosed_cthickening.preimage T.continuous)
  let centers (ij : Λ × Λ) := chartAt E ij.1.val '' pair ij
  have compactCenters (ij : Λ × Λ) : IsCompact (centers ij) :=
    (compactPair ij).image_of_continuousOn ((chartAt E ij.1.val).continuousOn.mono
      (fun _ hx => sourceK ij.1 hx.1))
  have validCenters (ij : Λ × Λ) : centers ij ⊆ (chartAt E ij.1.val).target ∩
      (T ∘ (chartAt E ij.1.val).symm) ⁻¹' (chartAt E ij.2.val).source := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(chartAt E ij.1.val).map_source (sourceK ij.1 hx.1), ?_⟩
    change T ((chartAt E ij.1.val).symm (chartAt E ij.1.val x)) ∈ (chartAt E ij.2.val).source
    rw [(chartAt E ij.1.val).left_inv (sourceK ij.1 hx.1)]
    exact tubeInside ij.2 hx.2
  have oneFrame : 1 ≤ 2*atlas.bound := by linarith [atlas.one_le_bound]
  have windows (ij : Λ × Λ) := F.uniform_centered_first_holder_tube
    (P := system.EuclideanModel) (Q := system.EuclideanModel)
    positiveα subunitα lower regular (chartAt E ij.1.val) (chartAt E ij.2.val)
    (chart_mem_maximalAtlas ij.1.val) (chart_mem_maximalAtlas ij.2.val)
    (centers ij) (compactCenters ij) (validCenters ij) (2*atlas.bound) oneFrame
  choose radii positiveRadii noise positiveNoise window B C nonnegativeB nonnegativeC estimates using windows
  let pairs := atlas.centers.product atlas.centers
  obtain ⟨radius, positiveRadius, commonRadius⟩ := CompactUniformCenteredCharts.common_positive
    pairs radii (fun ij _ => positiveRadii ij)
  obtain ⟨η, positiveη, commonTarget⟩ := CompactUniformCenteredCharts.common_positive
    atlas.centers ρ (fun c _ => positiveρ c)
  obtain ⟨cutoff, positiveCutoff, commonNoise⟩ := CompactUniformCenteredCharts.common_positive
    pairs (fun ij => (noise ij : ℝ)) (fun ij _ => by exact_mod_cast positiveNoise ij)
  have commonB (ij : Λ × Λ) (hij : ij ∈ pairs) : B ij ≤ pairs.sum B :=
    Finset.single_le_sum (fun i _ => nonnegativeB i) hij
  have commonC (ij : Λ × Λ) (hij : ij ∈ pairs) : C ij ≤ pairs.sum C :=
    Finset.single_le_sum (fun i _ => nonnegativeC i) hij
  refine ⟨radius, positiveRadius, η, positiveη, min F.window ⟨cutoff, positiveCutoff.le⟩,
    lt_min F.window_positive positiveCutoff, min_le_left _ _, pairs.sum B, pairs.sum C,
    Finset.sum_nonneg (fun i _ => nonnegativeB i), Finset.sum_nonneg (fun i _ => nonnegativeC i), ?_⟩
  intro ε hp hw control c hc d hd x hx y hy near
  have member : (c, d) ∈ pairs := Finset.mem_product.mpr ⟨hc, hd⟩
  have targetCenter : T x.val ∈ cthickening (ρ d) (K d) :=
    mem_cthickening_of_dist_le _ y.val (ρ d) (K d) ⟨y, hy, rfl⟩
      (near.le.trans (commonTarget d hd))
  have center : x.val ∈ pair (c, d) := ⟨⟨x, hx, rfl⟩, targetCenter⟩
  have localNoise : ε ≤ noise (c, d) := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr (hw.trans (min_le_right _ _))).trans (commonNoise (c, d) member))
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.euclideanReferenceFrame c ⟨x, atlas.inside c hx⟩)
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.euclideanReferenceFrame d ⟨y, atlas.inside d hy⟩)
  have boundL : ‖L.toContinuousLinearMap‖ ≤ 2*atlas.bound := by
    dsimp only [L]
    rw [system.euclidean_chartFrame c ⟨x, atlas.inside c hx⟩]
    change ‖(ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
      (system.referenceFrame c ⟨x, atlas.inside c hx⟩)).toContinuousLinearMap.comp
      system.euclideanEquiv.symm.toContinuousLinearMap‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (atlas.frame_bounds c hc x hx).1 system.euclideanEquiv_norm.2
        (norm_nonneg _) (by linarith [atlas.one_le_bound])).trans (by linarith [atlas.one_le_bound]))
  have boundR : ‖R.symm.toContinuousLinearMap‖ ≤ 2*atlas.bound := by
    dsimp only [R]
    rw [system.euclidean_chartFrame d ⟨y, atlas.inside d hy⟩]
    change ‖system.euclideanEquiv.toContinuousLinearMap.comp
      (ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.referenceFrame d ⟨y, atlas.inside d hy⟩)).symm.toContinuousLinearMap‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul system.euclideanEquiv_norm.1 (atlas.frame_bounds d hd y hy).2 (norm_nonneg _) (by norm_num))
  have facts := estimates (c, d) ε hp localNoise control ((chartAt E c.val) x.val)
    (mem_image_of_mem _ center) L R boundL boundR ((chartAt E d.val) y.val)
  dsimp only at facts ⊢
  exact ⟨fun z hz => (facts.1 z (hz.trans (commonRadius (c, d) member))).trans (commonB (c, d) member),
    fun z hz w hw => (facts.2 z (hz.trans (commonRadius (c, d) member)) w
      (hw.trans (commonRadius (c, d) member))).trans
        (mul_le_mul_of_nonneg_right (commonC (c, d) member) (Real.rpow_nonneg (norm_nonneg _) _))⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
