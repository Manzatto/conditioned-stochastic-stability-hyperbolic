module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseRechartedCaptureAmplitude
public import LeanShared.Dynamics.HyperbolicAdaptedActualModelEquivalence

/-! Actual adapted tube charts inherit the full cutoff-word Holder bound
from the original normed-model ordinary actions. The Euclidean charts and
the original-to-Euclidean model equivalence are constructed by the adapted
frame system; no inner product on the original model is requested. -/
public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared HyperbolicBasicSet HyperbolicAdaptedPatchSystem CylinderPrincipalCoefficient
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] [Fintype ι]

theorem Maps.adapted_tube_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {Λ V : Set M} {base : BasicData (E := E) T Λ V} {system : PatchSystem base}
    (atlas : ChartAtlas system) {radius : ℝ} {s : Finset atlas.NormalizedTubeIndex}
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : s => atlas.normalizedTube radius i.val))
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ N : ℕ,
      ∀ controls : Fin N → cube (ι := ι) ε, ∀ labels : Fin (N + 1) → s,
      ∃ f : system.EuclideanModel →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate (atlas.normalizedTubeChart (labels 0).val)
          (fun m => (FiniteSmoothCapturePartition.wordCutoff d
            (fun j : Fin (N + 1) => prefixOrbit
              (fun control : cube (ι := ι) ε => F.family ε control.val) controls j.val m) labels : ℂ))
          (ActualFiniteRegularWord.weight
            (fun control : cube (ι := ι) ε => F.family ε control.val) g (List.ofFn controls)) x) ∧
        ‖f‖ ≤ C * B ^ N ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport
          (atlas.normalizedTubeChart (labels 0).val) (fun m => (d.beta (labels 0) m : ℂ)) ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ N) * dist x y ^ a := by
  let e := atlas.originalModelEquiv
  let c : s → OpenPartialHomeomorph M E := fun i => atlas.originalTubeChart e i.val
  have charts (i : s) : c i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M :=
    atlas.originalTubeChart_mem_maximal e i.val
  have source (i : s) : atlas.normalizedTube radius i.val ⊆ (c i).source := by
    intro x hx
    exact hx.1
  have estimates := F.recharted_capture_word_amplitude_holder μE hr regular ha ha1 haq weight
    d c charts source e
  simpa only [c, ChartAtlas.originalTubeChart_chartImage] using estimates

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
