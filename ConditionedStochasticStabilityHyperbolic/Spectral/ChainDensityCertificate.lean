module

public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseDensityCertificate

/-! # The inverse density certificate from actual live-chain smoothing

Only the actual killed chain needs to be strong Feller. That property can be
constructed directly from its restricted transition density, without requiring
an ambient unweighted noise operator to regularize every observable.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.NoiseDensityCertificate
open LeanShared LocalPositiveEigenfunction ComparedLocalQuasiErgodic

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace Ω] [MeasurableSpace Ω]

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

include d hmean in
theorem exists_certificate_of_chain_data (δ : ℝ)
    (c : Inputs T V K G hK noise F hF w hw.measurable R δ) :
    Nonempty (InverseDensityInputs T V K G hK noise F hF w hw.measurable R ν δ) := by
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
  have hLtarget : ∀ x ∈ K, (L x).restrict K = L x := by
    intro x _
    change ((WeightedRandomMapKernel.transition noise c.inverseWeight c.inverseMap x).restrict K).restrict K = _
    rw [Measure.restrict_restrict hK.measurableSet, inter_self]
    rfl
  obtain ⟨m, hm, hm0, hmc, hrepr, himage, _hharm⟩ :=
    KernelEigenmeasureDensity.exists_continuous_harmonic_density J L c.reference (ν.map Subtype.val)
      c.transitionDensity c.transition_measurable c.transition_representation c.densityBound
      c.densityBound_finite c.transition_bounded c.duality K hK c.reference_support hLtarget
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
    reference_support := c.reference_support
    density := m
    density_measurable := hm
    density_nonnegative := hm0
    density_continuous := hmc
    density_representation := hrepr
    duality := c.duality
    inverse_density_continuous := himage }⟩

end ConditionedStochasticStabilityHyperbolic.NoiseDensityCertificate
