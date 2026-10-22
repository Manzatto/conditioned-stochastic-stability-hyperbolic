module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseKernel

/-! Ambient strong Feller regularity for the literal shrinking-cube process.
This original-factor source does not require an anisotropic model or a
Whitney representation, so it applies unchanged at hyperbolic endpoints. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
local instance ambientRawProbability (L : Laws (ι := ι)) (ε : ℝ≥0) :
    IsProbabilityMeasure (L.law ε) := L.probability ε

/-- The continuous departure weight and target killing are handled by the
proved kernel identity. The only source is ordinary submersion smoothing for
smooth compactly supported control densities. -/
theorem Maps.strongFeller_ambient_raw_cube
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (K : Set M) (hK : MeasurableSet K)
    (w : M → ℝ) (hw : Continuous w) (nonnegative : ∀ x, 0 ≤ w x)
    (R : ℝ) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (smoothSource : ∀ q : Control (ι := ι) → ℝ, HasCompactSupport q → ContDiff ℝ ∞ q →
      ∀ f : M → ℝ, Measurable f → (∃ C ≥ 0, ∀ x, ‖f x‖ ≤ C) →
        Continuous (fun x => ∫ z : cube (ι := ι) ε,
          q z.val * f (F.family ε z.val x) ∂cubeVolume ε)) :
    HasStrongFellerKernel (NoiseKernel.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) K hK w hw.measurable R hR bound) := by
  intro f hf bounded
  obtain ⟨B, hB, hb⟩ := bounded
  have hi : Measurable (K.indicator f) := hf.indicator hK
  have hib : ∀ y, ‖K.indicator f y‖ ≤ B := by
    intro y
    by_cases hy : y ∈ K
    · simpa only [indicator_of_mem hy] using hb y
    · simpa only [indicator_of_notMem hy, norm_zero] using hB
  have cont := F.strongFeller_raw_cube L ε hε hwindow smoothSource
    (K.indicator f) hi ⟨B, hB, hib⟩
  have eq : (fun x => ∫ y, f y ∂(NoiseKernel.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) K hK w hw.measurable R hR bound).killedTransition x) =
      (fun x => (w x / R) * ∫ y, K.indicator f y ∂RandomMapKernel.transition
        (L.law ε) (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
        (F.raw_measurable ε hε hwindow) x) := by
    funext x
    rw [RandomMapKernel.integral_transition _ _ _ _ hi]
    exact NoiseKernel.integral_chain (L.law ε) _ (F.raw_measurable ε hε hwindow)
      K hK w hw.measurable nonnegative R hR bound f hf x
  rw [eq]
  exact (hw.div_const R).mul cont

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
