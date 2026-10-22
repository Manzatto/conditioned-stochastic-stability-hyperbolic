module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedLocalQuasiErgodic
public import LeanShared.Probability.KernelEigenmeasureDensity

/-!
# Constructing the inverse density certificate from noise facts

The classical data here concern only the actual forward transition density,
inverse weighted noise, reference volume, duality and plaque geometry. They
contain no measure-dependent density witness. The left eigenmeasure law
constructs that witness and both continuity conclusions internally.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction ENNReal

namespace ConditionedStochasticStabilityHyperbolic.NoiseDensityCertificate

open LeanShared LocalPositiveEigenfunction ComparedLocalQuasiErgodic

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

def ambientKernel (noise : Measure Ω) [IsProbabilityMeasure noise]
    (F : X × Ω → X) (hF : Measurable F) (K : Set X) (hK : IsCompact K)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) : Kernel X X :=
  WeightedConditioning.normalizedKernel (RandomMapKernel.killed noise F hF K hK.measurableSet)
    (SubtypeKernel.zeroExtend K w) R (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw)

/-- Named classical noise/volume data, independent of any eigenmeasure. The
global inverse weight bound follows in the manuscript model from compactness
and nonzero spatial Jacobians; it is distinct from basic-set positivity. -/
structure Inputs (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K)
    (noise : Measure Ω) [IsProbabilityMeasure noise]
    (F : X × Ω → X) (hF : Measurable F)
    (w : K → ℝ) (hw : Measurable w) (R δ : ℝ) where
  inverseMap : X × Ω → X
  inverse_measurable : Measurable inverseMap
  inverse_close : ∀ x ∈ K, ∀ ω, dist (inverseMap (x, ω)) (T.symm x) < δ
  inverse_plaques : ForwardPlaqueInputs T.symm inverseMap V K G
  inverseWeight : X × Ω → ℝ
  weight_measurable : Measurable inverseWeight
  weightBound : ℝ
  weight_bounded : ∀ x ω, inverseWeight (x, ω) ≤ weightBound
  weight_positive : ∀ x ∈ K, ∀ ω, 0 < inverseWeight (x, ω)
  reference : Measure X
  reference_finite : IsFiniteMeasure reference
  reference_support : reference.support = K
  transitionDensity : X × X → ℝ≥0∞
  transition_measurable : Measurable transitionDensity
  densityBound : ℝ≥0∞
  densityBound_finite : densityBound ≠ ∞
  transition_bounded : ∀ x y, transitionDensity (x, y) ≤ densityBound
  transition_representation : ∀ x, ambientKernel noise F hF K hK w hw R x =
    reference.withDensity (fun y => transitionDensity (x, y))
  duality : KernelAdjointDensity.IsAdjoint (ambientKernel noise F hF K hK w hw R)
    (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) reference
  inverse_smoothing : ∀ f : X → ℝ, Measurable f →
    (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f x‖ ≤ B) →
    ContinuousOn (fun x => ∫ y, f y ∂
      (WeightedRandomMapKernel.killed noise inverseWeight inverseMap K hK.measurableSet) x) K

variable (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K) [CompactSpace K]
  (noise : Measure Ω) [IsProbabilityMeasure noise]
  (F : X × Ω → X) (hF : Measurable F)
  (w : K → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hSF : RestrictedStrongFeller.HasStrongFellerNoise noise F hF)
  (d : RankOneSpectralData
    (RestrictedStrongFeller.transferOperator noise F hF K hK.measurableSet
      w hw hw0 R hR hwR hSF) (1 : K →ᵇ ℝ))
  (ν : Measure K) [IsFiniteMeasure ν]
  (hmean : ∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂ν)

include d hmean in
omit [SecondCountableTopology X] [CompactSpace Ω] [CompactSpace K] in
/-- The full local inverse certificate is produced for the actual represented
leading measure. No density, density continuity or support is supplied. -/
theorem exists_certificate (δ : ℝ)
    (c : Inputs T V K G hK noise F hF w hw.measurable R δ) :
    Nonempty (InverseDensityInputs T V K G hK noise F hF w hw.measurable R ν δ) := by
  let _ := c.reference_finite
  let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
  let _ : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let P := RestrictedStrongFeller.transferOperator noise F hF K hK.measurableSet
    w hw hw0 R hR hwR hSF
  have hP (f : K →ᵇ ℝ) (x : K) : P f x = ∫ y, f y ∂C.killedTransition x :=
    RestrictedStrongFeller.transferOperator_represents noise F hF K hK.measurableSet
      w hw hw0 R hR hwR hSF f x
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

variable {A W : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [SecondCountableTopology X] [CompactSpace Ω] in
/-- This is exactly the density-producer premise of the full compared local theorem. It follows from
eigenmeasure-independent classical noise facts. -/
theorem certificateProducer (δ : ℝ)
    (c : Inputs T V K G hK noise F hF w hw.measurable R δ)
    (s : ComparedRawSpectralInputs (A := A) (W := W)
      (RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR)
      (RestrictedStrongFeller.hasStrongFeller_chain noise F hF K hK.measurableSet
        w hw hw0 R hR hwR hSF) R) :
    ∀ (ν : Measure K) [IsFiniteMeasure ν],
      (∀ f : K →ᵇ ℝ, s.mean f = ∫ y, f y ∂ν) →
      Nonempty (InverseDensityInputs T V K G hK noise F hF w hw.measurable R ν δ) := by
  intro ν _ hm
  obtain ⟨dr, _hrate, hmean, _hvector⟩ := s.exists_rawRankOne
  let d' : RankOneSpectralData
      (RestrictedStrongFeller.rawTransferOperator noise F hF K hK.measurableSet
        w hw hw0 R hR hwR hSF) (1 : K →ᵇ ℝ) := dr
  have hmean' : d'.mean = s.mean := hmean
  let dn := d'.ofRawNormalization R hR
    (RestrictedStrongFeller.inv_smul_rawTransferOperator noise F hF K hK.measurableSet
      w hw hw0 R hR hwR hSF)
  have hmn (f : K →ᵇ ℝ) : dn.mean f = ∫ y, f y ∂ν := by
    simpa only [dn, RankOneSpectralData.ofRawNormalization_mean, hmean'] using hm f
  exact exists_certificate T V K G hK noise F hF w hw hw0 R hR hwR hSF dn ν hmn δ c

end ConditionedStochasticStabilityHyperbolic.NoiseDensityCertificate
