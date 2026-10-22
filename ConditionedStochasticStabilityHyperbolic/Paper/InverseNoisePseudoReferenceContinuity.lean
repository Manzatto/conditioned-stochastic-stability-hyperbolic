module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseCenteredWordContinuity
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseWordTarget
public import LeanShared.Geometry.PseudoReferenceLinearBounds
public import LeanShared.Geometry.PseudoReferenceCompactPatches
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! Actual centered noisy words are jointly continuous on a common ball for
EVERY nearby pseudo-reference pair. Actual input/output chart validity is
derived using compact coordinate tubes and uniform noisy target estimates. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.FiniteJetComposition LeanShared.CenteredManifoldCoordinates
open LeanShared.PseudoReferenceCoordinateMaps

set_option maxHeartbeats 1600000 in
theorem InverseFamily.pseudo_reference_continuity_window
    {E M ι P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {B : ℝ}
    {h : LeanShared.HyperbolicBasicSet.HyperbolicData (E := E) T.symm Λ}
    {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    (d : LeanShared.HyperbolicBasicSet.PseudoReferenceGeometry h)
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B) (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B ∧
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ, 0 < η ∧ ∃ cutoff : ℝ≥0, 0 < cutoff ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ x y : Λ,
      dist ((T.symm : M → M)^[d.blockLength] x.val) y.val < η →
      (∀ z : P, ‖z‖ ≤ radius →
        chart d x x.val + linear d frame x z ∈ (chart d x).target ∧
        ∀ controls : ℕ → cube (ι := ι) ε,
          word (fun n => fun w => J.map ε ((controls n).val,w)) d.blockLength
            (decode d frame x z) ∈ (chart d y).source) ∧
      ContinuousOn (fun p : (ℕ → cube (ι := ι) ε) × P =>
        centered (linear d frame x) (linear d frame y) ((chart d x) x.val) ((chart d y) y.val)
          (chart d y ∘ word (fun n => fun w => J.map ε ((p.1 n).val,w)) d.blockLength ∘ (chart d x).symm) p.2)
        (univ ×ˢ Metric.closedBall 0 radius) := by
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
  let domain (ij : Λ × Λ) := (chartAt E ij.1.val).target ∩
    (H ∘ (chartAt E ij.1.val).symm) ⁻¹' (chartAt E ij.2.val).source
  have openDomain (ij : Λ × Λ) : IsOpen (domain ij) :=
    ((T.symm.continuous.iterate d.blockLength).comp_continuousOn (chartAt E ij.1.val).symm.continuousOn).isOpen_inter_preimage
      (chartAt E ij.1.val).open_target (chartAt E ij.2.val).open_source
  have tubes (ij : Λ × Λ) := (compactCenters ij).exists_cthickening_subset_open
    (openDomain ij) (validCenters ij)
  choose σ positiveσ coordinateInside using tubes
  let coordinateTube (ij : Λ × Λ) := Metric.cthickening (σ ij) (centers ij)
  have compactCoordinates (ij : Λ × Λ) : IsCompact (coordinateTube ij) := (compactCenters ij).cthickening
  let starts (ij : Λ × Λ) := (chartAt E ij.1.val).symm '' coordinateTube ij
  have compactStarts (ij : Λ × Λ) : IsCompact (starts ij) :=
    (compactCoordinates ij).image_of_continuousOn ((chartAt E ij.1.val).symm.continuousOn.mono
      (fun _ hz => (coordinateInside ij hz).1))
  have targetStarts (ij : Λ × Λ) : MapsTo H (starts ij) (chartAt E ij.2.val).source := by
    rintro _ ⟨z,hz,rfl⟩
    exact (coordinateInside ij hz).2
  have windows (ij : Λ × Λ) := J.exists_uniform_word_target d.blockLength
    (starts ij) (chartAt E ij.2.val).source (compactStarts ij) (chartAt E ij.2.val).open_source (targetStarts ij)
  choose noise positiveNoise targets using windows
  obtain ⟨radius,positiveRadius,commonRadius⟩ := LeanShared.CompactUniformCenteredCharts.common_positive
    (d.centers.product d.centers) (fun ij => σ ij / C) (fun ij _ => div_pos (positiveσ ij) positiveC)
  obtain ⟨η,positiveη,commonTarget⟩ := LeanShared.CompactUniformCenteredCharts.common_positive
    d.centers ρ (fun i _ => positiveρ i)
  obtain ⟨cutoff,positiveCutoff,commonNoise⟩ := LeanShared.CompactUniformCenteredCharts.common_positive
    (d.centers.product d.centers) (fun ij => (noise ij : ℝ)) (fun ij _ => by exact_mod_cast positiveNoise ij)
  refine ⟨radius,positiveRadius,η,positiveη,min J.window ⟨cutoff,positiveCutoff.le⟩,lt_min J.positive positiveCutoff,
    fun ε hp hw x y near => ?_⟩
  let ij : Λ × Λ := (d.index x,d.index y)
  have member : ij ∈ d.centers.product d.centers := Finset.mem_product.mpr ⟨d.index_mem x,d.index_mem y⟩
  have targetCenter : H x.val ∈ targetTube ij.2 :=
    Metric.mem_cthickening_of_dist_le _ y.val (ρ ij.2) (ambientPatch d ij.2)
      (selected_ambientPatch d y) (near.le.trans (commonTarget (d.index y) (d.index_mem y)))
  have center : x.val ∈ pairPatch ij := ⟨selected_ambientPatch d x,targetCenter⟩
  have localNoise : ε ≤ noise ij := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr (hw.trans (min_le_right _ _))).trans (commonNoise ij member))
  have valid (z : P) (hz : ‖z‖ ≤ radius) :
      chart d x x.val + linear d frame x z ∈ (chart d x).target ∧
      ∀ controls : ℕ → cube (ι := ι) ε,
        word (fun n => fun w => J.map ε ((controls n).val,w)) d.blockLength (decode d frame x z) ∈ (chart d y).source := by
    have displacement : dist ((chart d x) x.val + linear d frame x z) ((chart d x) x.val) ≤ σ ij := by
      rw [dist_eq_norm,add_sub_cancel_left]
      calc
        _ ≤ ‖(linear d frame x).toContinuousLinearMap‖ * ‖z‖ := (linear d frame x).toContinuousLinearMap.le_opNorm z
        _ ≤ C * (σ ij / C) := mul_le_mul (linearBounds x).1 (hz.trans (commonRadius ij member))
          (norm_nonneg z) positiveC.le
        _ = σ ij := by field_simp
    have inside := Metric.mem_cthickening_of_dist_le _ ((chart d x) x.val) (σ ij) (centers ij)
      (mem_image_of_mem _ center) displacement
    exact ⟨(coordinateInside ij inside).1,fun controls =>
      targets ij ε hp localNoise controls ⟨_,inside,rfl⟩⟩
  refine ⟨valid,?_⟩
  exact J.centered_word_continuousOn ε hp (hw.trans (min_le_left _ _)) d.blockLength
    (chart d x) (chart d y) (linear d frame x) (linear d frame y)
    ((chart d x) x.val) ((chart d y) y.val) radius
    (fun z hz => (valid z hz).1) (fun controls z hz => (valid z hz).2 controls)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
