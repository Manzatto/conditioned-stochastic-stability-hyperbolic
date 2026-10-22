module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseStrongFeller

/-! The actual original factor's killed chain is strong Feller directly
from the ordinary smooth-density submersion source. No anisotropic model,
hyperbolic dimension condition, or noisy spectral conclusion is needed. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}

local instance liveStrongFellerProbability (L : Laws (ι := ι)) (ε : ℝ≥0) :
    IsProbabilityMeasure (L.law ε) := L.probability ε

/-- Arbitrary measurable live sets are allowed. The only regularity source
is the ordinary unweighted integral for smooth compact control densities;
the actual bounded density and continuous departure weight are handled by
proved approximation and kernel identities. -/
theorem Maps.strongFeller_live_raw_cube
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (K : Set M) (hK : MeasurableSet K)
    (w : K → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ f : M → ℝ, Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
        Continuous (fun x => ∫ z : cube (ι := ι) ε,
          g z.val * f (F.family ε z.val x) ∂cubeVolume ε)) :
    HasStrongFellerKernel (RestrictedNoise.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) K hK w hw.measurable R hR hwR) :=
  RestrictedStrongFeller.hasStrongFeller_chain (L.law ε)
    (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
    (F.raw_measurable ε hε hwindow) K hK w hw hw0 R hR hwR
    (F.strongFeller_raw_cube L ε hε hwindow smoothSource)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
