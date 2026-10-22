module

public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalControlSubmersionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAmbientStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseLiveStrongFeller

/-! The literal compact-manifold noise assumptions imply smoothing and strong
Feller regularity. No smooth-density source, chosen reference measure, or
anisotropic representation is supplied by the caller. -/

public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M]

/-- The explicit ordinary smoothing source is a theorem. -/
theorem proved_smoothCubeSubmersionContract :
    SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι) := by
  obtain ⟨_σ, _finite, _positive, source⟩ :=
    exists_finite_reference_controlSubmersionSources (E := E) (M := M) (ι := ι)
  exact source.smooth_density

variable {T : M ≃ₜ M} {r : ℝ}

theorem Maps.strongFeller_proved (F : Maps (E := E) (ι := ι) T r)
    (L : Laws (ι := ι)) (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window) :
    RestrictedStrongFeller.HasStrongFellerNoise (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε positive window) :=
  F.strongFeller_from_submersion L proved_smoothCubeSubmersionContract ε positive window

theorem Maps.strongFeller_ambient_proved (F : Maps (E := E) (ι := ι) T r)
    (L : Laws (ι := ι)) (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    (K : Set M) (measurableK : MeasurableSet K)
    (w : M → ℝ) (continuousW : Continuous w) (nonnegative : ∀ x, 0 ≤ w x)
    (R : ℝ) (positiveR : 0 < R) (bound : ∀ x, w x ≤ R) :
    HasStrongFellerKernel (NoiseKernel.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε positive window) K measurableK w continuousW.measurable
      R positiveR bound) :=
  F.strongFeller_ambient_raw_cube L ε positive window K measurableK w continuousW
    nonnegative R positiveR bound
    (proved_smoothCubeSubmersionContract ε positive (fun z => F.family ε z.1 z.2)
      (F.joint_C1 ε positive window) (F.control_surjective ε positive window))

theorem Maps.strongFeller_live_proved (F : Maps (E := E) (ι := ι) T r)
    (L : Laws (ι := ι)) (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    (K : Set M) (measurableK : MeasurableSet K)
    (w : K → ℝ) (continuousW : Continuous w) (nonnegative : ∀ x, 0 ≤ w x)
    (R : ℝ) (positiveR : 0 < R) (bound : ∀ x, w x ≤ R) :
    HasStrongFellerKernel (RestrictedNoise.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε positive window) K measurableK w continuousW.measurable
      R positiveR bound) :=
  F.strongFeller_live_raw_cube L ε positive window K measurableK w continuousW
    nonnegative R positiveR bound
    (proved_smoothCubeSubmersionContract ε positive (fun z => F.family ε z.1 z.2)
      (F.joint_C1 ε positive window) (F.control_surjective ε positive window))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
