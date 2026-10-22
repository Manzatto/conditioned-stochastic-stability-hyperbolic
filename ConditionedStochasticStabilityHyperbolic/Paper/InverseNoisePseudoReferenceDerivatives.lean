module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseCenteredWordOffsets
public import LeanShared.Geometry.PseudoReferenceLinearBounds
public import LeanShared.Geometry.PseudoReferenceCompactPatches
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! Literal noisy finite words satisfy one common centered derivative estimate
for every nearby pseudo-reference pair. The reference tolerance, coordinate
radius and noise threshold precede all points and control choices. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.FiniteJetComposition LeanShared.CenteredManifoldCoordinates
open LeanShared.PseudoReferenceCoordinateMaps

set_option maxHeartbeats 1600000 in
theorem InverseFamily.pseudo_reference_derivative_window
    {E M ι P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {B : ℝ}
    {h : LeanShared.HyperbolicBasicSet.HyperbolicData (E := E) T.symm Λ}
    {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (d : LeanShared.HyperbolicBasicSet.PseudoReferenceGeometry h)
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B) (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B ∧
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ, 0 < η ∧ ∃ cutoff : ℝ≥0, 0 < cutoff ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ x y : Λ,
      dist ((T.symm : M → M)^[d.blockLength] x.val) y.val < η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ z : P, ‖z‖ ≤ radius →
        let f := centered (linear d frame x) (linear d frame y) ((chart d x) x.val) ((chart d y) y.val)
          (chart d y ∘ word (fun n => fun w => J.map ε ((controls n).val,w)) d.blockLength ∘ (chart d x).symm)
        let g := centered (linear d frame x) (linear d frame y) ((chart d x) x.val) ((chart d y) y.val)
          (chart d y ∘ (T.symm : M → M)^[d.blockLength] ∘ (chart d x).symm)
        DifferentiableAt ℝ f z ∧ ‖fderiv ℝ f z - fderiv ℝ g z‖ ≤ δ := by
  obtain ⟨C,positiveC,linearBounds⟩ := exists_uniform_linear_bound d frame positiveB bounds
  let H := (T.symm : M → M)^[d.blockLength]
  have tubes (i : Λ) := (compact_ambientPatch d i).exists_cthickening_subset_open
    (chartAt E i.val).open_source (ambientPatch_source d i)
  choose ρ positiveρ tubeInside using tubes
  let targetTube (i : Λ) := Metric.cthickening (ρ i) (ambientPatch d i)
  have compactTube (i : Λ) : IsCompact (targetTube i) := (compact_ambientPatch d i).cthickening
  let pairPatch (ij : Λ × Λ) := ambientPatch d ij.1 ∩ H ⁻¹' targetTube ij.2
  have compactPair (ij : Λ × Λ) : IsCompact (pairPatch ij) :=
    (compact_ambientPatch d ij.1).inter_right ((compactTube ij.2).isClosed.preimage (T.symm.continuous.iterate _))
  have sourcePair (ij : Λ × Λ) : pairPatch ij ⊆ (chartAt E ij.1.val).source :=
    fun _ hx => ambientPatch_source d ij.1 hx.1
  have targetPair (ij : Λ × Λ) : MapsTo H (pairPatch ij) (chartAt E ij.2.val).source :=
    fun _ hx => tubeInside ij.2 hx.2
  let centers (ij : Λ × Λ) := chartAt E ij.1.val '' pairPatch ij
  have compactCenters (ij : Λ × Λ) : IsCompact (centers ij) :=
    (compactPair ij).image_of_continuousOn ((chartAt E ij.1.val).continuousOn.mono (sourcePair ij))
  have validCenters (ij : Λ × Λ) : centers ij ⊆ (chartAt E ij.1.val).target ∩
      (H ∘ (chartAt E ij.1.val).symm) ⁻¹' (chartAt E ij.2.val).source := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨(chartAt E ij.1.val).map_source (sourcePair ij hx),?_⟩
    change H ((chartAt E ij.1.val).symm (chartAt E ij.1.val x)) ∈ (chartAt E ij.2.val).source
    rw [(chartAt E ij.1.val).left_inv (sourcePair ij hx)]
    exact targetPair ij hx
  have windows (ij : Λ × Λ) := J.centered_word_offset_window (P := P) (Q := P) regularity deterministic inverse
    (chartAt E ij.1.val) (chartAt E ij.2.val) (chart_mem_maximalAtlas ij.1.val)
    (chart_mem_maximalAtlas ij.2.val) d.blockLength (centers ij) (compactCenters ij) (validCenters ij)
    C δ positiveC positiveδ
  choose radii positiveRadii noise positiveNoise estimates using windows
  obtain ⟨radius,positiveRadius,commonRadius⟩ := LeanShared.CompactUniformCenteredCharts.common_positive
    (d.centers.product d.centers) radii (fun ij _ => positiveRadii ij)
  obtain ⟨η,positiveη,commonTarget⟩ := LeanShared.CompactUniformCenteredCharts.common_positive
    d.centers ρ (fun i _ => positiveρ i)
  obtain ⟨cutoff,positiveCutoff,commonNoise⟩ := LeanShared.CompactUniformCenteredCharts.common_positive
    (d.centers.product d.centers) (fun ij => (noise ij : ℝ)) (fun ij _ => by exact_mod_cast positiveNoise ij)
  refine ⟨radius,positiveRadius,η,positiveη,⟨cutoff,positiveCutoff.le⟩,positiveCutoff,
    fun ε hp hw x y near controls z hz => ?_⟩
  let ij : Λ × Λ := (d.index x,d.index y)
  have member : ij ∈ d.centers.product d.centers := Finset.mem_product.mpr ⟨d.index_mem x,d.index_mem y⟩
  have targetCenter : H x.val ∈ targetTube ij.2 :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ ij.2) (ambientPatch d ij.2)
      (selected_ambientPatch d y) (near.le.trans (commonTarget (d.index y) (d.index_mem y)))
  have center : x.val ∈ pairPatch ij := ⟨selected_ambientPatch d x,targetCenter⟩
  have localNoise : ε ≤ noise ij := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr hw).trans (commonNoise ij member))
  exact estimates ij ε hp localNoise controls ((chart d x) x.val) (mem_image_of_mem _ center)
    (linear d frame x) (linear d frame y) (linearBounds x).1 (linearBounds y).2
    ((chart d y) y.val) z (hz.trans (commonRadius ij member))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
