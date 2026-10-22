module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseSourceCutoffWordLocalCore
public import LeanShared.Dynamics.HyperbolicAdaptedActualModelEquivalence
public import LeanShared.Geometry.LittleHolderLinearPrecomposition
public import LeanShared.Geometry.ManifoldLocalizationLinearRechart

/-! Actual beta-word outputs belong to the native Euclidean tube's exact
closed local little Holder core. The input manifold model keeps its given
norm. The original-to-Euclidean equivalence and the genuine original charts
are constructed from the same adapted frame system. -/
public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared HyperbolicBasicSet HyperbolicAdaptedPatchSystem CylinderPrincipalCoefficient
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] [Fintype ι]

theorem Maps.adapted_tube_source_cutoff_word_local_core (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    {Λ V : Set M} {base : BasicData (E := E) T Λ V} {system : PatchSystem base}
    (atlas : ChartAtlas system) {radius : ℝ} {s : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    {g : M → ℝ} {q b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbq : b < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (χ : M → ℂ) (smoothχ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ χ)
    (h : M → ℂ) (smoothh : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ h)
    (ε : NNReal) (hp : 0 < ε) (hw : ε ≤ F.window) {N : ℕ}
    (controls : Fin N → cube (ι := ι) ε) (labels : Fin (N + 1) → s) :
    let θ : M → ℂ := fun m => (d.beta (labels 0) m : ℂ)
    let supportθ : tsupport θ ⊆ (atlas.normalizedTubeChart (labels 0).val).source :=
      (tsupport_comp_subset Complex.ofReal_zero (d.beta (labels 0))).trans
        ((d.support (labels 0)).trans (fun _ hx => hx.1))
    ∃ output : EuclideanSmoothHolderCore.space
        (ChartLocalization.localSupport_isCompact (atlas.normalizedTubeChart (labels 0).val) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1,
      ∀ x, EuclideanSmoothHolderCore.physical
        (ChartLocalization.localSupport_isCompact (atlas.normalizedTubeChart (labels 0).val) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1 output x =
        ChartLocalization.coordinate (atlas.normalizedTubeChart (labels 0).val)
          (fun m => χ m * (FiniteSmoothCapturePartition.wordCutoff d
            (fun j : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls j.val m) labels : ℂ))
          (fun m => ActualFiniteRegularWord.weight
            (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
            h (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x := by
  classical
  dsimp only
  let e := atlas.originalModelEquiv
  let c : s → OpenPartialHomeomorph M E := fun i => atlas.originalTubeChart e i.val
  have charts (i : s) : c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M :=
    atlas.originalTubeChart_mem_maximal e i.val
  have source (i : s) : atlas.normalizedTube radius i.val ⊆ (c i).source := fun _ hx => hx.1
  obtain ⟨old, formula⟩ := F.source_cutoff_word_local_core μE hr hb hb1 hbq weight d c charts source χ smoothχ
    h smoothh ε hp hw controls labels
  let θ : M → ℂ := fun m => (d.beta (labels 0) m : ℂ)
  have supportOld : tsupport θ ⊆ (c (labels 0)).source :=
    (tsupport_comp_subset Complex.ofReal_zero (d.beta (labels 0))).trans
      ((d.support (labels 0)).trans (source (labels 0)))
  have supportNew : tsupport θ ⊆ (atlas.normalizedTubeChart (labels 0).val).source :=
    (tsupport_comp_subset Complex.ofReal_zero (d.beta (labels 0))).trans
      ((d.support (labels 0)).trans (fun _ hx => hx.1))
  let compactOld := ChartLocalization.localSupport_isCompact (c (labels 0)) θ supportOld
    (HasCompactSupport.of_compactSpace _)
  let compactNew := ChartLocalization.localSupport_isCompact
    (atlas.normalizedTubeChart (labels 0).val) θ supportNew (HasCompactSupport.of_compactSpace _)
  have cover : e '' ChartLocalization.localSupport (c (labels 0)) θ ⊆
      ChartLocalization.localSupport (atlas.normalizedTubeChart (labels 0).val) θ := by
    rw [← ConstructedManifoldLocalization.localSupport_linearRechart c e]
    rw [show LinearRechartedManifold.chartImage e (c (labels 0)) =
      atlas.normalizedTubeChart (labels 0).val from atlas.originalTubeChart_chartImage e (labels 0).val]
  let output := LittleHolderLinearPrecomposition.operator e cover hb hb1 compactOld.closure compactNew.closure old
  refine ⟨output, ?_⟩
  intro x
  have transported := LittleHolderLinearPrecomposition.physical_operator e cover hb hb1
    compactOld.closure compactNew.closure old x
  apply transported.trans
  rw [formula]
  have equal := ConstructedManifoldLocalization.coordinate_linearRechart c e (labels 0)
    (fun m => χ m * (FiniteSmoothCapturePartition.wordCutoff d
      (fun j : Fin (N + 1) => prefixOrbit
        (fun control : cube (ι := ι) ε => F.family ε control.val) controls j.val m) labels : ℂ))
    (fun m => ActualFiniteRegularWord.weight
      (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
      h (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) x
  simpa only [c, ChartAtlas.originalTubeChart_chartImage] using equal.symm

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
