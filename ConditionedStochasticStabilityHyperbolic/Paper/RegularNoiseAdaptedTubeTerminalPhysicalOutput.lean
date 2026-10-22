module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeWordLocalCore
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedTubeSourceCutoffWordLocalCore
public import LeanShared.Geometry.LocalizedChartWordRepresentation
public import LeanShared.Geometry.SupportedChartExtensionLinearRechart

/-! The closed native output for an independent terminal input slot. The
input is a supported Schwartz function in the chart of the slot `j`, which is
not identified with the final word label. The auxiliary terminal cutoff
stays in the amplitude, evaluated at the word endpoint, so the output is
represented globally by that terminal amplitude times the input composed
with the chosen global word. -/
public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff BoundedContinuousFunction NNReal SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared HyperbolicBasicSet HyperbolicAdaptedPatchSystem CylinderPrincipalCoefficient
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] [Fintype ι]

theorem Maps.adapted_tube_terminal_physical_output (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    {Λ V : Set M} {base : BasicData (E := E) T Λ V} {system : PatchSystem base}
    (atlas : ChartAtlas system) {radius : ℝ} {s : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    {g : M → ℝ} {q b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbq : b < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (ε : NNReal) (hp : 0 < ε) (hw : ε ≤ F.window) {N : ℕ}
    (controls : Fin N → cube (ι := ι) ε) (labels : Fin (N + 1) → s)
    (j : s) (τ : M → ℂ) (smoothτ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ τ)
    (f : 𝓢(system.EuclideanModel, ℂ)) (compactf : HasCompactSupport (f : system.EuclideanModel → ℂ))
    (supportf : tsupport (f : system.EuclideanModel → ℂ) ⊆
      (atlas.normalizedTubeChart j.val).target) :
    let κ := fun k : Fin (N + 1) => atlas.normalizedTubeChart (labels k).val
    let maps := fun control : cube (ι := ι) ε => F.family ε control.val
    let cutoff := fun m => (FiniteSmoothCapturePartition.wordCutoff d
      (fun k : Fin (N + 1) => prefixOrbit maps controls k.val m) labels : ℂ)
    let amplitude := fun m => ActualFiniteRegularWord.weight maps g (List.ofFn controls) m *
      τ (prefixOrbit maps controls N m)
    let θ : M → ℂ := fun m => (d.beta (labels 0) m : ℂ)
    let supportθ : tsupport θ ⊆ (κ 0).source :=
      (tsupport_comp_subset Complex.ofReal_zero (d.beta (labels 0))).trans
        ((d.support (labels 0)).trans (fun _ hx => hx.1))
    ∀ native : M ≃ₜ M, (native : M → M) = prefixOrbit maps controls N →
    ∀ G : system.EuclideanModel → system.EuclideanModel, ∀ O : Set system.EuclideanModel,
    tsupport (ChartLocalization.coordinate (κ 0) cutoff amplitude) ⊆ O →
    O ⊆ (ChartedHomeomorphCoordinateMap.coordinateMap (κ 0)
      (atlas.normalizedTubeChart j.val) native).source →
    EqOn G (ChartedHomeomorphCoordinateMap.coordinateMap (κ 0)
      (atlas.normalizedTubeChart j.val) native) O →
    ∃ output : EuclideanSmoothHolderCore.space
        (ChartLocalization.localSupport_isCompact (κ 0) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1,
      ∀ x, EuclideanSmoothHolderCore.physical
        (ChartLocalization.localSupport_isCompact (κ 0) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1 output x =
        ChartLocalization.coordinate (κ 0) cutoff amplitude x * f (G x) := by
  classical
  dsimp only
  intro native nativeIdentity G O support inside agree
  let e := atlas.originalModelEquiv
  let target := atlas.normalizedTubeChart j.val
  have decodedSmooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞
      (SupportedChartExtension.function target (f : system.EuclideanModel → ℂ)) := by
    have support' : tsupport (f : system.EuclideanModel → ℂ) ⊆
        (LinearRechartedManifold.chartImage e (atlas.originalTubeChart e j.val)).target := by
      simpa only [ChartAtlas.originalTubeChart_chartImage] using supportf
    have smooth := SupportedChartExtension.smooth_linearRechart e
      (atlas.originalTubeChart e j.val)
      (atlas.originalTubeChart_mem_maximal e _) (f.smooth ⊤) compactf support'
    simpa only [ChartAtlas.originalTubeChart_chartImage] using smooth
  have smoothProduct : ContMDiff (𝓘(ℝ, ℂ × ℂ)) (𝓘(ℝ, ℂ)) ∞
      (fun z : ℂ × ℂ => z.1 * z.2) :=
    (contDiff_mul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2)).contMDiff
  have smoothInput : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞
      (fun m => τ m * SupportedChartExtension.function target f m) :=
    smoothProduct.comp (smoothτ.prodMk_space decodedSmooth)
  obtain ⟨output, represented⟩ := F.adapted_tube_word_local_core μE hr atlas d hb hb1 hbq weight
    (fun m => τ m * SupportedChartExtension.function target f m) smoothInput ε hp hw controls labels
  refine ⟨output, ?_⟩
  intro x
  have sameAmplitude :
      (fun m => ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        τ (native m)) =
      (fun m => ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        τ (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) := by
    funext m
    rw [← congrFun nativeIdentity m]
  have sameInput :
      (fun m => ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        (τ (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m) *
          SupportedChartExtension.function target f
            (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m))) =
      (fun m => (ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        τ (native m)) * SupportedChartExtension.function target f (native m)) := by
    funext m
    rw [← congrFun nativeIdentity m, mul_assoc]
  rw [← sameAmplitude] at support
  have representation := LocalizedChartWordRepresentation.represented
    (atlas.normalizedTubeChart (labels 0).val) target native G
    (fun m => (FiniteSmoothCapturePartition.wordCutoff d
      (fun k : Fin (N + 1) => prefixOrbit
        (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ))
    _ f support inside agree x
  rw [sameAmplitude] at representation
  exact (represented x).trans ((congrArg (fun h : M → ℂ => ChartLocalization.coordinate
    (atlas.normalizedTubeChart (labels 0).val)
    (fun m => (FiniteSmoothCapturePartition.wordCutoff d
      (fun k : Fin (N + 1) => prefixOrbit
        (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ)) h x)
      sameInput).trans representation)


theorem Maps.adapted_tube_source_terminal_physical_output (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    {Λ V : Set M} {base : BasicData (E := E) T Λ V} {system : PatchSystem base}
    (atlas : ChartAtlas system) {radius : ℝ} {s : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    {g : M → ℝ} {q b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbq : b < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (ε : NNReal) (hp : 0 < ε) (hw : ε ≤ F.window) {N : ℕ}
    (controls : Fin N → cube (ι := ι) ε) (labels : Fin (N + 1) → s)
    (χ : M → ℂ) (smoothχ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ χ)
    (j : s) (τ : M → ℂ) (smoothτ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ τ)
    (f : 𝓢(system.EuclideanModel, ℂ)) (compactf : HasCompactSupport (f : system.EuclideanModel → ℂ))
    (supportf : tsupport (f : system.EuclideanModel → ℂ) ⊆
      (atlas.normalizedTubeChart j.val).target) :
    let κ := fun k : Fin (N + 1) => atlas.normalizedTubeChart (labels k).val
    let maps := fun control : cube (ι := ι) ε => F.family ε control.val
    let cutoff := fun m => χ m * (FiniteSmoothCapturePartition.wordCutoff d
      (fun k : Fin (N + 1) => prefixOrbit maps controls k.val m) labels : ℂ)
    let amplitude := fun m => ActualFiniteRegularWord.weight maps g (List.ofFn controls) m *
      τ (prefixOrbit maps controls N m)
    let θ : M → ℂ := fun m => (d.beta (labels 0) m : ℂ)
    let supportθ : tsupport θ ⊆ (κ 0).source :=
      (tsupport_comp_subset Complex.ofReal_zero (d.beta (labels 0))).trans
        ((d.support (labels 0)).trans (fun _ hx => hx.1))
    ∀ native : M ≃ₜ M, (native : M → M) = prefixOrbit maps controls N →
    ∀ G : system.EuclideanModel → system.EuclideanModel, ∀ O : Set system.EuclideanModel,
    tsupport (ChartLocalization.coordinate (κ 0) cutoff amplitude) ⊆ O →
    O ⊆ (ChartedHomeomorphCoordinateMap.coordinateMap (κ 0)
      (atlas.normalizedTubeChart j.val) native).source →
    EqOn G (ChartedHomeomorphCoordinateMap.coordinateMap (κ 0)
      (atlas.normalizedTubeChart j.val) native) O →
    ∃ output : EuclideanSmoothHolderCore.space
        (ChartLocalization.localSupport_isCompact (κ 0) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1,
      ∀ x, EuclideanSmoothHolderCore.physical
        (ChartLocalization.localSupport_isCompact (κ 0) θ supportθ
          (HasCompactSupport.of_compactSpace _)).closure hb hb1 output x =
        ChartLocalization.coordinate (κ 0) cutoff amplitude x * f (G x) := by
  classical
  dsimp only
  intro native nativeIdentity G O support inside agree
  let e := atlas.originalModelEquiv
  let target := atlas.normalizedTubeChart j.val
  have decodedSmooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞
      (SupportedChartExtension.function target (f : system.EuclideanModel → ℂ)) := by
    have support' : tsupport (f : system.EuclideanModel → ℂ) ⊆
        (LinearRechartedManifold.chartImage e (atlas.originalTubeChart e j.val)).target := by
      simpa only [ChartAtlas.originalTubeChart_chartImage] using supportf
    have smooth := SupportedChartExtension.smooth_linearRechart e
      (atlas.originalTubeChart e j.val)
      (atlas.originalTubeChart_mem_maximal e _) (f.smooth ⊤) compactf support'
    simpa only [ChartAtlas.originalTubeChart_chartImage] using smooth
  have smoothProduct : ContMDiff (𝓘(ℝ, ℂ × ℂ)) (𝓘(ℝ, ℂ)) ∞
      (fun z : ℂ × ℂ => z.1 * z.2) :=
    (contDiff_mul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2)).contMDiff
  have smoothInput : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞
      (fun m => τ m * SupportedChartExtension.function target f m) :=
    smoothProduct.comp (smoothτ.prodMk_space decodedSmooth)
  obtain ⟨output, represented⟩ := F.adapted_tube_source_cutoff_word_local_core μE hr atlas d hb hb1 hbq
    weight χ smoothχ (fun m => τ m * SupportedChartExtension.function target f m) smoothInput ε hp hw controls labels
  refine ⟨output, ?_⟩
  intro x
  have sameAmplitude :
      (fun m => ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        τ (native m)) =
      (fun m => ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        τ (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m)) := by
    funext m
    rw [← congrFun nativeIdentity m]
  have sameInput :
      (fun m => ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        (τ (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m) *
          SupportedChartExtension.function target f
            (prefixOrbit (fun control : cube (ι := ι) ε => F.family ε control.val) controls N m))) =
      (fun m => (ActualFiniteRegularWord.weight
        (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls) m *
        τ (native m)) * SupportedChartExtension.function target f (native m)) := by
    funext m
    rw [← congrFun nativeIdentity m, mul_assoc]
  rw [← sameAmplitude] at support
  have representation := LocalizedChartWordRepresentation.represented
    (atlas.normalizedTubeChart (labels 0).val) target native G
    (fun m => χ m * (FiniteSmoothCapturePartition.wordCutoff d
      (fun k : Fin (N + 1) => prefixOrbit
        (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ))
    _ f support inside agree x
  rw [sameAmplitude] at representation
  exact (represented x).trans ((congrArg (fun h : M → ℂ => ChartLocalization.coordinate
    (atlas.normalizedTubeChart (labels 0).val)
    (fun m => χ m * (FiniteSmoothCapturePartition.wordCutoff d
      (fun k : Fin (N + 1) => prefixOrbit
        (fun control : cube (ι := ι) ε => F.family ε control.val) controls k.val m) labels : ℂ)) h x)
      sameInput).trans representation)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
