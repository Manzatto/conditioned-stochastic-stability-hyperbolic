module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFiniteLabelledAmplitude
public import LeanShared.Geometry.FiniteCaptureLocalizedWeights

/-! The ordinary amplitude estimate is applied to the actual finite smooth
capture cutoffs. The finite weights are precisely g and g times beta_i,
and the terminal functions are precisely beta_j. All constants precede the
entire labelled word, its terminal label, and the noise controls. -/
@[expose] public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [Fintype ι] [Fintype I]

def captureWeights {K : Set M} {v : I → Set M}
    (d : FiniteSmoothCapturePartition.Data (E := E) K v) (g : M → ℝ) : Option I → M → ℂ
  | none, x => (g x : ℂ)
  | some i, x => (g x : ℂ) * (d.beta i x : ℂ)

def captureTerminals {K : Set M} {v : I → Set M}
    (d : FiniteSmoothCapturePartition.Data (E := E) K v) : Option I → M → ℂ
  | none, _ => 1
  | some i, x => (d.beta i x : ℂ)

theorem Maps.capture_labelled_amplitude_holder (μE : Measure E) [μE.IsAddHaarMeasure]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {g : M → ℝ} {q a : ℝ} (ha : 0 < a) (ha1 : a < 1) (haq : a < q)
    (weight : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    {K : Set M} {v : I → Set M} (d : FiniteSmoothCapturePartition.Data (E := E) K v)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (θ : M → ℂ) (smoothθ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
    (compactθ : HasCompactSupport θ) (supportθ : tsupport θ ⊆ c.source) :
    ∃ η : NNReal, 0 < η ∧ η ≤ F.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ ε : NNReal, 0 < ε → ε ≤ η → ∀ word : List (cube (ι := ι) ε × Option I),
      ∀ j : Option I, ∃ f : E →ᵇ ℂ,
        (∀ x, f x = ChartLocalization.coordinate c θ
          (ActualFiniteLabelledWord.amplitude
            (fun control : cube (ι := ι) ε => F.family ε control.val)
            (captureWeights d g) (captureTerminals d j) word) x) ∧
        ‖f‖ ≤ C * B ^ word.length ∧
        tsupport (fun x => f x) ⊆ ChartLocalization.localSupport c θ ∧
        ∀ x y, ‖f x - f y‖ ≤ (C * B ^ word.length) * dist x y ^ a := by
  obtain ⟨u, hau, hu1, huq, localized⟩ := d.exists_common_localized_order weight ha ha1 haq
  have weightRegular (i : Option I) :
      FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u (captureWeights d g i) := by
    cases i with
    | none => exact FractionalManifoldRegularity.lower_subunit (ha.trans hau) hu1 huq weight.ofReal
    | some i => exact localized i
  have terminalSmooth (j : Option I) :
      ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (captureTerminals d j) := by
    cases j with
    | none => exact contMDiff_const
    | some j => exact Complex.ofRealCLM.contMDiff.comp (d.smooth j)
  exact F.finite_labelled_amplitude_holder μE hr regular ha ha1 hau hu1
    (captureWeights d g) weightRegular (captureTerminals d) terminalSmooth
    c hc θ smoothθ compactθ supportθ

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
