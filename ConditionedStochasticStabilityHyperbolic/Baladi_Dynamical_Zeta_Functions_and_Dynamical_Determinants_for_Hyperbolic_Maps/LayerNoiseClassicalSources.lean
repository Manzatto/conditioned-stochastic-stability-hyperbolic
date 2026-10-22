module

public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportCollarDensityCertificate
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualInverseAdjointSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseRegularNoiseContinuity
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCutoffAdjoint
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerSquareCompact
public import ConditionedStochasticStabilityHyperbolic.Spectral.PowerCompactRealLeadingPair

/-! Ordinary noise, Jacobian and random-plaque inputs for one actual layer.
There are no spectral projectors, eigenfunctions, QEMs or weak-limit outputs
in this record. The finite-window smoothing and independent density sources
are supplied by the cited smooth-control theorem and the checked bounded-law
and Jacobian constructions. Only the open live region needs reference support.
-/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.LayerNoiseClassicalSources
open LeanShared KellerLiverani1999
variable {X Ω Test TestCore : Type*}
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
  [SecondCountableTopology Ω] [OpensMeasurableSpace Ω]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
  [AddCommGroup TestCore] [Module ℂ TestCore]

structure Data
    (T : X ≃ₜ X) (V K G B : Set X) (hK : IsCompact K) [CompactSpace K]
    (law : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (law ε)]
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w : K → ℝ) (hw : Continuous w) (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (σ : Measure K) [IsFiniteMeasure σ]
    (view : Test →ₗ[ℂ] (X → ℂ)) (view_injective : Function.Injective view)
    (qt : TestCore →ₗ[ℂ] Test) where
  live_open : IsOpen V
  live_subset : V ⊆ K
  retained_open : IsOpen B
  core_retained : isolatedCore T K ⊆ B
  retained_live : closure B ⊆ V
  no_return : (T '' closure B) ∩ forwardTrapped T K ⊆ B
  weight_nonnegative : ∀ x, 0 ≤ w x
  cutoff_continuous : Continuous wc
  cutoff_nonnegative : ∀ x, 0 ≤ wc x
  cutoff_support : tsupport wc ⊆ {x : K | x.val ∈ V}
  weight_agreement : ∀ x : K, x.val ∈ closure B → wc x = w x
  close : ∀ η : ℝ, 0 < η → ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    ∀ x ∈ K, ∀ z, dist (F ε (x, z)) (T x) < η
  plaques : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    Nonempty (LocalPositiveCollar.ForwardCollarPlaqueInputs T (F ε) V K G)
  smoothingWindow : ℝ≥0
  smoothingWindow_positive : 0 < smoothingWindow
  noise_smoothing : ∀ ε : ℝ≥0, 0 < ε → ε ≤ smoothingWindow →
    RestrictedStrongFeller.HasStrongFellerNoise (law ε) (F ε) (hF ε)
  inverse_density : ∀ η : ℝ, 0 < η → ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    Nonempty (Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (law ε)
      (F ε) (hF ε) w hw.measurable R η)
  reference_positive : {x : K | x.val ∈ V} ⊆ σ.support
  inverseWindow : ℝ≥0
  inverseWindow_positive : 0 < inverseWindow
  inverseMap : ℝ≥0 → Ω → X → X
  inverseWeight : ℝ≥0 → X × Ω → ℝ
  inverseRegular : ∀ ε, 0 < ε → ε ≤ inverseWindow → InverseRegularTransfer.OrdinarySources view (inverseMap ε) (inverseWeight ε)
  inverse_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : Ω × X => inverseMap ε z.1 z.2)
  inverse_weight_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : Ω × X => inverseWeight ε (z.2, z.1))
  smooth_continuous : ∀ c, Continuous (view (qt c))
  inverseExponent : ℝ
  inverseExponent_positive : 0 < inverseExponent
  inverseInterpolationConstant : ℝ≥0 → TestCore → Ω → ℝ
  inverse_interpolation : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) c z₀ z e, 0 ≤ e →
    (∀ x, ‖view ((inverseRegular ε hp hw).operator view_injective z (qt c)) x -
      view ((inverseRegular ε hp hw).operator view_injective z₀ (qt c)) x‖ ≤ e) →
    dist ((inverseRegular ε hp hw).operator view_injective z (qt c))
      ((inverseRegular ε hp hw).operator view_injective z₀ (qt c)) ≤
        inverseInterpolationConstant ε c z₀ * e ^ inverseExponent
  jacobian : ∀ ε, 0 < ε → ε ≤ inverseWindow → ∀ z (f : K →ᵇ ℂ) v,
    (∫ x, ActualCutoffAdjoint.raw K (F ε) wc z f x * view v x.val ∂σ) =
      ∫ x, f x * ((inverseWeight ε (x.val, z) : ℂ) * view v (inverseMap ε z x.val)) ∂σ
  ultra : StrongFellerSquareCompact.UltraFellerContract (X := K)
  fredholm : PowerCompactGap.SquareCompactFredholm (F := K →ᵇ ℂ)
  riesz : PowerCompactRealLeadingPair.ClassicalContract (X := K)



namespace Data
variable {T : X ≃ₜ X} {V K G B : Set X} {hK : IsCompact K} [CompactSpace K]
  {law : ℝ≥0 → Measure Ω} [∀ ε, IsProbabilityMeasure (law ε)]
  {F : ℝ≥0 → X × Ω → X} {hF : ∀ ε, Measurable (F ε)}
  {w : K → ℝ} {hw : Continuous w} {wc : K → ℝ} {hwc : Measurable wc}
  {R : ℝ} {hR : 0 < R} {hwR : ∀ x, w x ≤ R} {hwcR : ∀ x, wc x ≤ R}
  {σ : Measure K} [IsFiniteMeasure σ]
  {view : Test →ₗ[ℂ] (X → ℂ)} {inj : Function.Injective view} {qt : TestCore →ₗ[ℂ] Test}
  (d : Data T V K G B hK law F hF w hw wc hwc R hR hwR hwcR σ view inj qt)

omit [CompactSpace X] [CompactSpace Ω] [SecondCountableTopology Ω] [OpensMeasurableSpace Ω] [CompleteSpace Test] in
theorem originalSF (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ d.smoothingWindow) :
    HasStrongFellerKernel
      (RestrictedNoise.chain (law ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR) :=
  RestrictedStrongFeller.hasStrongFeller_chain (law ε) (F ε) (hF ε) K hK.measurableSet
    w hw d.weight_nonnegative R hR hwR (d.noise_smoothing ε hε hwindow)

omit [CompactSpace X] [CompactSpace Ω] [SecondCountableTopology Ω] [OpensMeasurableSpace Ω] [CompleteSpace Test] in
theorem cutoffSF (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ d.smoothingWindow) :
    HasStrongFellerKernel
      (RestrictedNoise.chain (law ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR) := by
  exact RestrictedStrongFeller.hasStrongFeller_chain (law ε) (F ε) (hF ε) K hK.measurableSet
    wc d.cutoff_continuous d.cutoff_nonnegative R hR hwcR (d.noise_smoothing ε hε hwindow)
end Data

end ConditionedStochasticStabilityHyperbolic.LayerNoiseClassicalSources
