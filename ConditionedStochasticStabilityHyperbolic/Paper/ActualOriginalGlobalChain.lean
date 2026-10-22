module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAmbientStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Global.PositiveNoiseContinuation

/-! The original endpoint process has a genuine all-scale chain family
without any original anisotropic model or representation. Scale continuation
only serves the all-positive spectral interface; on the original noise
window its driving law, maps, target killing and normalization are exact. -/
@[expose] public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.ActualOriginalGlobalChain
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
  (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
local instance actualOriginalProbability (ε : ℝ≥0) : IsProbabilityMeasure (L.law ε) := L.probability ε

def rawMap (ε : ℝ≥0) : M × cube (ι := ι) ε → M :=
  if _small : 0 < ε ∧ ε ≤ F.window then
    fun z => F.family ε z.2.val z.1
  else fun z => T z.1

theorem rawMap_measurable (ε : ℝ≥0) : Measurable (rawMap F ε) := by
  unfold rawMap
  split
  · rename_i small
    exact F.raw_measurable ε small.1 small.2
  · exact T.continuous.measurable.comp measurable_fst

variable (K : Set M) (hK : MeasurableSet K)
  (w : M → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)

def rawChain (ε : ℝ≥0) : AbsorbingMarkovChains.CanonicalChain M :=
  NoiseKernel.chain (L.law ε) (rawMap F ε) (rawMap_measurable F ε) K hK w hw R hR bound

def chain : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain M :=
  Global.PositiveNoiseContinuation.chain (rawChain F L K hK w hw R hR bound) F.window

theorem rawChain_eq (ε : ℝ≥0) (hε : 0 < ε) (window : ε ≤ F.window) :
    rawChain F L K hK w hw R hR bound ε =
      NoiseKernel.chain (L.law ε)
        (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
        (F.raw_measurable ε hε window) K hK w hw R hR bound := by
  simp only [rawChain, rawMap, dite_eq_left (show 0 < ε ∧ ε ≤ F.window from ⟨hε, window⟩)]

theorem chain_eq (ε : ℝ≥0) (hε : 0 < ε) (window : ε ≤ F.window) :
    chain F L K hK w hw R hR bound ε =
      NoiseKernel.chain (L.law ε)
        (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
        (F.raw_measurable ε hε window) K hK w hw R hR bound := by
  change rawChain F L K hK w hw R hR bound (min ε F.window) = _
  rw [min_eq_left window]
  exact rawChain_eq F L K hK w hw R hR bound ε hε window

/-- All-positive regularity is derived from ordinary original-cube smoothing;
no endpoint spectral or anisotropic source is required. -/
theorem strongFeller (hwc : Continuous w) (nonnegative : ∀ x, 0 ≤ w x)
    (smoothSource : ∀ ε (_hε : 0 < ε) (_window : ε ≤ F.window),
      ∀ q : Control (ι := ι) → ℝ, HasCompactSupport q → ContDiff ℝ ∞ q →
        ∀ f : M → ℝ, Measurable f → (∃ B ≥ 0, ∀ x, ‖f x‖ ≤ B) →
          Continuous (fun x => ∫ z : cube (ι := ι) ε,
            q z.val * f (F.family ε z.val x) ∂cubeVolume ε)) :
    ∀ ε, 0 < ε → HasStrongFellerKernel (chain F L K hK w hw R hR bound ε) := by
  apply Global.PositiveNoiseContinuation.strongFeller
    (rawChain F L K hK w hw R hR bound) F.window F.window_positive
  intro ε hε window
  rw [rawChain_eq F L K hK w hw R hR bound ε hε window]
  exact F.strongFeller_ambient_raw_cube L ε hε window K hK w hwc nonnegative R hR bound
    (smoothSource ε hε window)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.ActualOriginalGlobalChain
