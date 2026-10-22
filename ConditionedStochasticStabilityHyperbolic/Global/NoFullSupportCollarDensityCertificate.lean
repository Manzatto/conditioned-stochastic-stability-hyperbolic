module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ChainDensityCertificate
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveCollar
public import LeanShared.Probability.KernelEigenmeasureDensityNoFullSupport

/-! Independent classical noise/volume data and constructed inverse density
with positivity required only on a fixed two-sided collar. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportCollarDensityCertificate
open LeanShared LocalPositiveEigenfunction ComparedLocalQuasiErgodic NoiseDensityCertificate

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace Ω] [MeasurableSpace Ω]

structure Inputs (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K)
    (noise : Measure Ω) [IsProbabilityMeasure noise]
    (F : X × Ω → X) (hF : Measurable F)
    (w : K → ℝ) (hw : Measurable w) (R δ : ℝ) where
  inverseMap : X × Ω → X
  inverse_measurable : Measurable inverseMap
  inverse_close : ∀ x ∈ K, ∀ ω, dist (inverseMap (x, ω)) (T.symm x) < δ
  inverse_plaques : LocalPositiveCollar.ForwardCollarPlaqueInputs T.symm inverseMap V K G
  inverseWeight : X × Ω → ℝ
  weight_measurable : Measurable inverseWeight
  weightBound : ℝ
  weight_bounded : ∀ x ω, inverseWeight (x, ω) ≤ weightBound
  weight_positive : ∀ x ∈ K, x ∈ G → ∀ ω, 0 < inverseWeight (x, ω)
  reference : Measure X
  reference_finite : IsFiniteMeasure reference
  reference_conull : ∀ᵐ x ∂reference, x ∈ K
  reference_core_support : isolatedCore T K ⊆ reference.support
  transitionDensity : X × X → ℝ≥0∞
  transition_measurable : Measurable transitionDensity
  densityBound : ℝ≥0∞
  densityBound_finite : densityBound ≠ ∞
  transition_bounded : ∀ x y, transitionDensity (x, y) ≤ densityBound
  transition_representation : ∀ x, ambientKernel noise F hF K hK w hw R x =
    reference.withDensity (fun y => transitionDensity (x, y))
  duality : KernelAdjointDensity.IsAdjoint (ambientKernel noise F hF K hK w hw R)
    (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) reference
  inverse_absoluteContinuous : ∀ x ∈ K,
    (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) x ≪ reference
  inverse_smoothing : ∀ f : X → ℝ, Measurable f →
    (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
    ContinuousOn (fun x => ∫ y, f y ∂
      (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) x) K

structure CollarInverseDensityInputs
    (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K)
    (noise : Measure Ω) [IsProbabilityMeasure noise]
    (F : X × Ω → X) (hF : Measurable F)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ)
    (ν : Measure K) (δ r : ℝ) where
  inverseMap : X × Ω → X
  inverse_measurable : Measurable inverseMap
  inverse_close : ∀ x ∈ K, ∀ ω, dist (inverseMap (x, ω)) (T.symm x) < δ
  inverse_plaques : LocalPositiveCollar.ForwardCollarPlaqueInputs T.symm inverseMap V K G
  inverseWeight : X × Ω → ℝ
  weight_measurable : Measurable inverseWeight
  weightBound : ℝ
  weight_bounded : ∀ x ∈ K, ∀ ω, inverseWeight (x, ω) ≤ weightBound
  weight_positive : ∀ x ∈ K, x ∈ G → ∀ ω, 0 < inverseWeight (x, ω)
  reference : Measure X
  reference_finite : IsFiniteMeasure reference
  reference_conull : ∀ᵐ x ∂reference, x ∈ K
  reference_core_support : isolatedCore T K ⊆ reference.support
  density : X → ℝ
  density_measurable : Measurable density
  density_nonnegative : ∀ x, 0 ≤ density x
  density_continuous : ContinuousOn density K
  density_representation : ν.map Subtype.val = eigenvectorMeasure reference density
  duality : KernelAdjointDensity.IsAdjoint
    (WeightedConditioning.normalizedKernel (RandomMapKernel.killed noise F hF K hK.measurableSet)
      (SubtypeKernel.zeroExtend K w) R (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw))
    (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) reference
  inverse_density_continuous : ContinuousOn
    (fun x => ∫ y, density y ∂(WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) x) K
  inverse_density_law : ∀ x ∈ K, (∫ y, density y ∂
    (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) x) = r * density x

variable (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K)
  (noise : Measure Ω) [IsProbabilityMeasure noise]
  (F : X × Ω → X) (hF : Measurable F)
  (w : K → ℝ) (hw : Continuous w)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hSF : HasStrongFellerKernel
    (RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR))
  (d : RankOneSpectralData
    (strongFellerTransferOperator
      (RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR) hSF)
    (1 : K →ᵇ ℝ))
  (ν : Measure K) [IsFiniteMeasure ν]
  (hmean : ∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂ν)

omit [CompactSpace X] in
include d hmean in
theorem exists_certificate_of_chain_data (δ : ℝ)
    (c : Inputs T V K G hK noise F hF w hw.measurable R δ) :
    Nonempty (CollarInverseDensityInputs T V K G hK noise F hF w hw.measurable R ν δ d.rate) := by
  let _ := c.reference_finite
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
  let _ : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let P := strongFellerTransferOperator C hSF
  have hP (f : K →ᵇ ℝ) (x : K) : P f x = ∫ y, f y ∂C.killedTransition x :=
    strongFellerTransferOperator_represents C hSF f x
  have hleft := rankOne_left_eigenmeasure d C.killedTransition hP ν hmean
  let J := ambientKernel noise F hF K hK w hw.measurable R
  let L := WeightedRandomMapKernel.killed noise c.inverseWeight c.inverseMap K hK.measurableSet
  let _ : IsFiniteKernel L := WeightedRandomMapKernel.killed_isFinite noise c.inverseWeight
    c.inverseMap K hK.measurableSet c.weightBound c.weight_bounded
  have hlefta : J ∘ₘ ν.map Subtype.val = ENNReal.ofReal d.rate • ν.map Subtype.val :=
    map_left_eigenmeasure C.killedTransition J Subtype.val measurable_subtype_coe
      (map_live_killedTransition noise F hF K hK.measurableSet w hw.measurable R hR hwR) ν _ hleft
  obtain ⟨m, hm, hm0, hmc, hrepr, himage, hharm⟩ :=
    KernelEigenmeasureDensity.exists_continuous_harmonic_density_of_inverse_ac J L c.reference (ν.map Subtype.val)
      c.transitionDensity c.transition_measurable c.transition_representation c.densityBound
      c.densityBound_finite c.transition_bounded c.duality K c.inverse_absoluteContinuous
      c.inverse_smoothing d.rate_pos hlefta
  exact ⟨{
    inverseMap := c.inverseMap
    inverse_measurable := c.inverse_measurable
    inverse_close := c.inverse_close
    inverse_plaques := c.inverse_plaques
    inverseWeight := c.inverseWeight
    weight_measurable := c.weight_measurable
    weightBound := c.weightBound
    weight_bounded := fun x _ ω => c.weight_bounded x ω
    weight_positive := c.weight_positive
    reference := c.reference
    reference_finite := c.reference_finite
    reference_conull := c.reference_conull
    reference_core_support := c.reference_core_support
    density := m
    density_measurable := hm
    density_nonnegative := hm0
    density_continuous := hmc
    density_representation := hrepr
    duality := c.duality
    inverse_density_continuous := himage
    inverse_density_law := hharm }⟩

end ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportCollarDensityCertificate
