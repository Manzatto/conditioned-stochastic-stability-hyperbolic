module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeWordAmplitudeSupport
public import LeanShared.Geometry.FiniteCaptureWordCutoffSupport
public import LeanShared.Geometry.ChartFractionalLocalization

/-! Actual beta-weighted source amplitudes are continuous and compactly
supported, including across the partial-chart boundary. Their entire
support lies in a constructed open physical itinerary cylinder. -/
public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

set_option maxHeartbeats 800000 in
theorem Maps.adapted_tubeWord_amplitude_continuity {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (atlas : ChartAtlas system)
    (radius : ℝ) (s : Finset atlas.NormalizedTubeIndex)
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    {N : ℕ} (control : Fin N → cube (ι := ι) ε)
    (labels : Fin (N+1) → s) (amplitude : M → ℂ) (continuousAmplitude : Continuous amplitude) :
    let κ := AdaptedTubeWord.chart atlas s labels
    let points := fun (m : M) (j : Fin (N+1)) => CylinderPrincipalCoefficient.prefixOrbit
      (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m
    let cutoff := fun m => (FiniteSmoothCapturePartition.wordCutoff d (points m) labels : ℂ)
    let g := ChartLocalization.coordinate (κ 0) cutoff amplitude
    Continuous g ∧ HasCompactSupport g ∧
      ∃ O : Set system.EuclideanModel, IsOpen O ∧ O ⊆ (κ 0).target ∧ tsupport g ⊆ O ∧
      ∀ z ∈ O, ∃ m : M, z = κ 0 m ∧
        ∀ j : Fin (N+1), points m j ∈ atlas.normalizedTube radius (labels j).val := by
  let := F.atlas.compactSpace
  dsimp only
  let κ := AdaptedTubeWord.chart atlas s labels
  let points := fun (m : M) (j : Fin (N+1)) => CylinderPrincipalCoefficient.prefixOrbit
    (fun k : Fin N => F.family ε (control k).val) (fun k => k) j.val m
  let realCutoff := fun m => FiniteSmoothCapturePartition.wordCutoff d (points m) labels
  let cutoff := fun m => (realCutoff m : ℂ)
  let g := ChartLocalization.coordinate (κ 0) cutoff amplitude
  have continuousPrefix (k : ℕ) : Continuous (CylinderPrincipalCoefficient.prefixOrbit
      (fun j : Fin N => F.family ε (control j).val) (fun j => j) k) := by
    induction k with
    | zero => exact continuous_id
    | succ k ih =>
      by_cases hk : k < N
      · simpa only [CylinderPrincipalCoefficient.prefixOrbit,dite_eq_left hk,Function.comp_def] using
          (F.map_regular ε positive window (control ⟨k,hk⟩)).differentiable.continuous.comp ih
      · simpa only [CylinderPrincipalCoefficient.prefixOrbit,dite_eq_right hk] using ih
  have continuousPoints (j : Fin (N+1)) : Continuous (fun m => points m j) := continuousPrefix j.val
  let cylinder := ⋂ j : Fin (N+1),
    (fun m => points m j) ⁻¹' atlas.normalizedTube radius (labels j).val
  have openCylinder : IsOpen cylinder := isOpen_iInter_of_finite (fun j =>
    (atlas.normalizedTube_open radius (labels j).val).preimage (continuousPoints j))
  have realSupport : tsupport realCutoff ⊆ cylinder :=
    FiniteSmoothCapturePartition.wordCutoff_tsupport_subset d
      (fun j m => points m j) continuousPoints labels
  have support : tsupport cutoff ⊆ cylinder := by
    change tsupport (Complex.ofRealCLM ∘ realCutoff) ⊆ cylinder
    exact (tsupport_comp_subset (map_zero Complex.ofRealCLM) realCutoff).trans realSupport
  have cylinderSource : cylinder ⊆ (κ 0).source := by
    intro m hm
    have member := (mem_iInter.mp hm (⟨0,Nat.zero_lt_succ N⟩ : Fin (N+1))).1
    rw [←AdaptedTubeWord.chart_eq atlas s labels (⟨0,Nat.zero_lt_succ N⟩ : Fin (N+1))] at member
    exact member
  have cutoffSource : tsupport cutoff ⊆ (κ 0).source := support.trans cylinderSource
  have compactCutoff : HasCompactSupport cutoff := HasCompactSupport.of_compactSpace cutoff
  have continuousReal : Continuous realCutoff :=
    FiniteSmoothCapturePartition.wordCutoff_continuous d
      (fun j m => points m j) continuousPoints labels
  have continuousCutoff : Continuous cutoff := Complex.continuous_ofReal.comp continuousReal
  have continuousG : Continuous g := ChartFractionalLocalization.continuous (κ 0) cutoff
    cutoffSource compactCutoff continuousCutoff continuousAmplitude
  have compactG : HasCompactSupport g :=
    ChartLocalization.coordinate_hasCompactSupport (κ 0) cutoff cutoffSource compactCutoff amplitude
  let O := (κ 0) '' cylinder
  have openO : IsOpen O := (κ 0).isOpen_image_of_subset_source openCylinder cylinderSource
  have targetO : O ⊆ (κ 0).target := by
    rintro _ ⟨m,hm,rfl⟩
    exact (κ 0).map_source (cylinderSource hm)
  have localCompact := ChartLocalization.localSupport_isCompact (κ 0) cutoff cutoffSource compactCutoff
  have localSupport : tsupport g ⊆ ChartLocalization.localSupport (κ 0) cutoff := by
    apply closure_minimal ?_ localCompact.isClosed
    intro z nonzero
    by_contra outside
    exact nonzero (ChartLocalization.coordinate_zero_outside (κ 0) cutoff amplitude z outside)
  refine ⟨continuousG,compactG,O,openO,targetO,localSupport.trans (image_mono support),?_⟩
  rintro z ⟨m,hm,rfl⟩
  exact ⟨m,rfl,fun j => mem_iInter.mp hm j⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
