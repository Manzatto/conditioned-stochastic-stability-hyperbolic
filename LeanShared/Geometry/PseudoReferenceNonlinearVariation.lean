module
public import LeanShared.Geometry.PseudoReferenceLinearBounds
public import LeanShared.Geometry.PseudoReferenceCompactPatches
public import LeanShared.Geometry.CompactMisalignedAtlasRadius
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! Actual uniform nonlinear derivative variation for EVERY nearby pair of
reference points in the constructed coherent charts. Compact target tubes
supply the chart margins; discontinuous chart/frame choices cause no gap. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle
open CenteredManifoldCoordinates

set_option maxHeartbeats 1600000 in
theorem exists_nonlinear_variation_window
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {B : ℝ} {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
    (d : HyperbolicBasicSet.PseudoReferenceGeometry h)
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B) (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B ∧
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (H : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H)
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ, 0 < η ∧ ∀ x y : Λ,
      dist (H x.val) y.val < η → ∀ z : P, ‖z‖ ≤ radius →
        chart d x x.val + linear d frame x z ∈ (chart d x).target ∧
        H (decode d frame x z) ∈ (chart d y).source ∧
        DifferentiableAt ℝ (centered (linear d frame x) (linear d frame y)
          ((chart d x) x.val) ((chart d y) y.val) (chart d y ∘ H ∘ (chart d x).symm)) z ∧
        ‖fderiv ℝ (centered (linear d frame x) (linear d frame y)
            ((chart d x) x.val) ((chart d y) y.val) (chart d y ∘ H ∘ (chart d x).symm)) z -
          fderiv ℝ (centered (linear d frame x) (linear d frame y)
            ((chart d x) x.val) ((chart d y) y.val) (chart d y ∘ H ∘ (chart d x).symm)) 0‖ < δ := by
  obtain ⟨C,positiveC,linearBounds⟩ := exists_uniform_linear_bound d frame positiveB bounds
  have tubes (i : Λ) := (compact_ambientPatch d i).exists_cthickening_subset_open
    (chartAt E i.val).open_source (ambientPatch_source d i)
  choose ρ positiveρ tubeInside using tubes
  let targetTube (i : Λ) := Metric.cthickening (ρ i) (ambientPatch d i)
  have compactTube (i : Λ) : IsCompact (targetTube i) := (compact_ambientPatch d i).cthickening
  let pairPatch (ij : Λ × Λ) := ambientPatch d ij.1 ∩ H ⁻¹' targetTube ij.2
  have compactPair (ij : Λ × Λ) : IsCompact (pairPatch ij) :=
    (compact_ambientPatch d ij.1).inter_right ((compactTube ij.2).isClosed.preimage smooth.continuous)
  have sourcePair (ij : Λ × Λ) : pairPatch ij ⊆ (chartAt E ij.1.val).source :=
    fun _ hx => ambientPatch_source d ij.1 hx.1
  have targetPair (ij : Λ × Λ) : MapsTo H (pairPatch ij) (chartAt E ij.2.val).source :=
    fun _ hx => tubeInside ij.2 hx.2
  have localRadii (ij : Λ × Λ) := CompactMisalignedAtlasRadius.exists_radius (P := P) (Q := P)
    H smooth (chartAt E ij.1.val) (chartAt E ij.2.val)
    (chart_mem_maximalAtlas ij.1.val) (chart_mem_maximalAtlas ij.2.val)
    (pairPatch ij) (compactPair ij) (sourcePair ij) (targetPair ij) C δ positiveC positiveδ
  choose radii positiveRadii estimates using localRadii
  obtain ⟨radius,positiveRadius,commonRadius⟩ := CompactUniformCenteredCharts.common_positive
    (d.centers.product d.centers) radii (fun ij _ => positiveRadii ij)
  obtain ⟨η,positiveη,commonTarget⟩ := CompactUniformCenteredCharts.common_positive
    d.centers ρ (fun i _ => positiveρ i)
  refine ⟨radius,positiveRadius,η,positiveη,fun x y near z hz => ?_⟩
  let ij : Λ × Λ := (d.index x,d.index y)
  have member : ij ∈ d.centers.product d.centers := Finset.mem_product.mpr ⟨d.index_mem x,d.index_mem y⟩
  have targetCenter : H x.val ∈ targetTube ij.2 :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ ij.2) (ambientPatch d ij.2)
      (selected_ambientPatch d y) (near.le.trans (commonTarget (d.index y) (d.index_mem y)))
  have center : x.val ∈ pairPatch ij := ⟨selected_ambientPatch d x,targetCenter⟩
  exact estimates ij x.val center (linear d frame x) (linear d frame y) (linearBounds x).1
    (linearBounds y).2 ((chart d y) y.val) z (hz.trans (commonRadius ij member))

end LeanShared.PseudoReferenceCoordinateMaps
