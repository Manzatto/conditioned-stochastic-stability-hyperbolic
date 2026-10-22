module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedInverseDensityFamily
public import ConditionedStochasticStabilityHyperbolic.Paper.NoiseSmallness
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LayerNoiseClassicalSources
public import LeanShared.Probability.SubtypeReferenceSupport

/-! A literal regular perturbation and ordinary cited plaque/Jacobian facts
produce the actual layer's noise source. No noisy spectral gap, smoothing,
inverse density certificate or full closed-boundary support is a source field.
The inverse action used for analytic comparison is the raw cutoff action;
the independent positivity density uses the normalized ORIGINAL weight. -/

public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerNoiseSources
open LeanShared ControlledPlaqueClosure RegularNoise
variable {E M ι Parameters Test TestCore : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
  [AddCommGroup TestCore] [Module ℂ TestCore]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}

structure Data (p : Representation F Parameters evaluate)
    (σ : Measure M) (V K G B : Set M) (hK : IsCompact K) [CompactSpace K]
    (w wc : K → ℝ) (R : ℝ)
    (view : Test →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
    (qt : TestCore →ₗ[ℂ] Test) where
  live_open : IsOpen V
  live_subset : V ⊆ K
  collar_open : IsOpen G
  core_collar : isolatedCore T K ⊆ G
  retained_open : IsOpen B
  core_retained : isolatedCore T K ⊆ B
  retained_live : closure B ⊆ V
  no_return : (T '' closure B) ∩ forwardTrapped T K ⊆ B
  weight_nonnegative : ∀ x, 0 ≤ w x
  cutoff_continuous : Continuous wc
  cutoff_nonnegative : ∀ x, 0 ≤ wc x
  cutoff_support : tsupport wc ⊆ {x : K | x.val ∈ V}
  weight_agreement : ∀ x : K, x.val ∈ closure B → wc x = w x
  plaqueWindow : ℝ≥0
  plaqueWindow_positive : 0 < plaqueWindow
  plaqueWindow_le : plaqueWindow ≤ p.window
  forward_plaques : ∀ ε : ℝ≥0, 0 < ε → ε ≤ plaqueWindow →
    ClassicalPlaqueGeometry
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) V K G
  inverse_density_geometry : InverseDensityOrdinarySources F σ V K G w R
  inverseWindow : ℝ≥0
  inverseWindow_positive : 0 < inverseWindow
  inverseMap : ℝ≥0 → FixedControl (ι := ι) → M → M
  inverseWeight : ℝ≥0 → M × FixedControl (ι := ι) → ℝ
  inverseRegular : ∀ ε, 0 < ε → ε ≤ inverseWindow → InverseRegularTransfer.OrdinarySources view (inverseMap ε) (inverseWeight ε)
  inverse_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : FixedControl (ι := ι) × M => inverseMap ε z.1 z.2)
  inverse_weight_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : FixedControl (ι := ι) × M => inverseWeight ε (z.2, z.1))
  smooth_continuous : ∀ c, Continuous (view (qt c))
  inverseExponent : ℝ
  inverseExponent_positive : 0 < inverseExponent
  inverseInterpolationConstant : ℝ≥0 → TestCore → FixedControl (ι := ι) → ℝ
  inverse_interpolation : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) c z₀ z e, 0 ≤ e →
    (∀ x, ‖view ((inverseRegular ε hp hw).operator inj z (qt c)) x -
      view ((inverseRegular ε hp hw).operator inj z₀ (qt c)) x‖ ≤ e) →
    dist ((inverseRegular ε hp hw).operator inj z (qt c))
      ((inverseRegular ε hp hw).operator inj z₀ (qt c)) ≤
        inverseInterpolationConstant ε c z₀ * e ^ inverseExponent
  jacobian : ∀ ε, 0 < ε → ε ≤ inverseWindow → ∀ z (f : K →ᵇ ℂ) v,
    (∫ x, ActualCutoffAdjoint.raw K
      (fun y : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε y.2) y.1) wc z f x *
      view v x.val ∂σ.comap Subtype.val) =
      ∫ x, f x * ((inverseWeight ε (x.val, z) : ℂ) * view v (inverseMap ε z x.val)) ∂σ.comap Subtype.val
  ultra : StrongFellerSquareCompact.UltraFellerContract (X := K)
  fredholm : PowerCompactGap.SquareCompactFredholm (F := K →ᵇ ℂ)
  riesz : PowerCompactRealLeadingPair.ClassicalContract (X := K)

namespace Data
variable {p : Representation F Parameters evaluate} {σ : Measure M}
  {V K G B : Set M} {hK : IsCompact K} [CompactSpace K]
  {w wc : K → ℝ} {R : ℝ}
  {view : Test →ₗ[ℂ] (M → ℂ)} {inj : Function.Injective view} {qt : TestCore →ₗ[ℂ] Test}

omit [FiniteDimensional ℝ E] in
def produce (d : Data p σ V K G B hK w wc R view inj qt)
    [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (L : Laws (ι := ι)) (hw : Continuous w) (hwc : Measurable wc)
    (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (hF : ∀ ε, Measurable (fun z : M × FixedControl (ι := ι) =>
      evaluate (p.fixedParameters ε z.2) z.1)) :
    LayerNoiseClassicalSources.Data T V K G B hK L.fixedLaw
      (fun ε (z : M × FixedControl (ι := ι)) => evaluate (p.fixedParameters ε z.2) z.1) hF
      w hw wc hwc R hR hwR hwcR (σ.comap Subtype.val) view inj qt := by
  have hp : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), 0 < ε ∧ ε ≤ p.window := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds p.window_positive)] with ε he hb
    exact ⟨he, hb.le⟩
  have hcoreV : isolatedCore T K ⊆ V := d.core_retained.trans (subset_closure.trans d.retained_live)
  refine {
    live_open := d.live_open
    live_subset := d.live_subset
    retained_open := d.retained_open
    core_retained := d.core_retained
    retained_live := d.retained_live
    no_return := d.no_return
    weight_nonnegative := d.weight_nonnegative
    cutoff_continuous := d.cutoff_continuous
    cutoff_nonnegative := d.cutoff_nonnegative
    cutoff_support := d.cutoff_support
    weight_agreement := d.weight_agreement
    close := ?_
    plaques := ?_
    smoothingWindow := p.window
    smoothingWindow_positive := p.window_positive
    noise_smoothing := fun ε he hb => p.strongFeller_from_submersion L source.smooth_density ε he hb (hF ε)
    inverse_density := ?_
    reference_positive := fun x hx => SubtypeReferenceSupport.open_subset_support_comap σ K V
      hK.measurableSet d.live_open d.live_subset x hx
    inverseWindow := d.inverseWindow
    inverseWindow_positive := d.inverseWindow_positive
    inverseMap := d.inverseMap
    inverseWeight := d.inverseWeight
    inverseRegular := d.inverseRegular
    inverse_joint := d.inverse_joint
    inverse_weight_joint := d.inverse_weight_joint
    smooth_continuous := d.smooth_continuous
    inverseExponent := d.inverseExponent
    inverseExponent_positive := d.inverseExponent_positive
    inverseInterpolationConstant := d.inverseInterpolationConstant
    inverse_interpolation := d.inverse_interpolation
    jacobian := d.jacobian
    ultra := d.ultra
    fredholm := d.fredholm
    riesz := d.riesz }
  · intro η hη
    filter_upwards [F.eventually_uniform_close η hη, hp] with ε close positive
    intro x _ z
    rw [p.actual_fixedMap ε positive.1 positive.2]
    exact close.2.2 x z
  · have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ε < d.plaqueWindow :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds d.plaqueWindow_positive)
    filter_upwards [hp, hb] with ε he hb
    exact ⟨p.forwardPlaqueInputs source.open_image ε he.1 he.2 V K G d.live_open d.collar_open
      hcoreV d.core_collar (d.forward_plaques ε he.1 hb.le)⟩
  · intro η hη
    filter_upwards [p.eventually_inverse_density_inputs d.inverse_density_geometry source hK
      d.live_open d.collar_open d.live_subset hcoreV d.core_collar hw.measurable hR hwR hF η hη]
      with ε he
    exact he L

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerNoiseSources
