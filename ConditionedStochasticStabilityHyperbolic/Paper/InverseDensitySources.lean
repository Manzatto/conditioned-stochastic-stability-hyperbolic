module

public import ConditionedStochasticStabilityHyperbolic.Paper.ControlSubmersionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseCubeGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseSubmersionSmoothing
public import ConditionedStochasticStabilityHyperbolic.Paper.ControlWeightedSmoothing
public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportDensityReparametrization
public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedNoiseAbsoluteContinuity
public import LeanShared.Probability.DepartureWeightedRandomMap
public import LeanShared.Probability.RestrictedOpenSupport

/-! Ordinary inverse calculus, random plaques and individual Jacobian change
of variables construct the actual inverse density source. Joint densities,
averaged duality, inverse absolute continuity and smoothing are conclusions.
The reference is restricted volume; no full support on a closed live boundary
is assumed. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped NNReal ENNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared ControlledPlaqueClosure
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
/-- Only ordinary volume, plaque and scalar Jacobian facts enter this producer.
In particular its inputs mention neither eigenmeasures nor spectral data. -/
theorem Maps.inverse_density_inputs
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (V K G : Set M) (hK : IsCompact K) (hV : IsOpen V) (hG : IsOpen G)
    (hVK : V ⊆ K) (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (d : InverseCubeGeometry F ε V G)
    (δ : ℝ) (close : ∀ x ∈ K, ∀ a : cube (ι := ι) ε,
      dist (d.actualMap (x, a)) (T.symm x) < δ)
    (w : K → ℝ) (hwt : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (W : M × cube (ι := ι) ε → ℝ) (hW : Measurable W)
    (hW0 : ∀ x a, 0 ≤ W (x, a))
    (hWc : ∀ a, Continuous (fun x => W (x, a)))
    (B : ℝ) (hB : 0 ≤ B) (hWB : ∀ x a, ‖W (x, a)‖ ≤ B)
    (hWp : ∀ x ∈ K, x ∈ G → ∀ a, 0 < W (x, a))
    (change_variables : ∀ f g : M → ℝ≥0∞, Measurable f → Measurable g →
      ∀ a : cube (ι := ι) ε,
      (∫⁻ x, g x * (ENNReal.ofReal (W (x, a)) * K.indicator f (d.actualMap (x, a))) ∂σ.restrict K) =
        ∫⁻ x, f x * (ENNReal.ofReal (SubtypeKernel.zeroExtend K w x / R) *
          K.indicator g (F.family ε a.val x)) ∂σ.restrict K) :
    Nonempty (Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_continuous ε hε hw).measurable w hwt R δ) := by
  let H : M × cube (ι := ι) ε → M := fun z => F.family ε z.2.val z.1
  have hH : Measurable H := (F.raw_continuous ε hε hw).measurable
  have hD : Measurable d.actualMap := d.continuous_actualMap.measurable
  let : IsProbabilityMeasure (L.law ε) := L.probability ε
  obtain ⟨C, hC, vol⟩ := F.volume_bound_from_submersion σ source ε hε hw
  obtain ⟨Q, hQ, q, hq, hqB, repr⟩ := F.exists_bounded_transition_density L σ ε hε hw C hC vol
  obtain ⟨q', hq', hqB', repr'⟩ := NormalizedKilledDensity.exists_density (L.law ε) H hH
    σ q hq repr Q hqB K hK.measurableSet (SubtypeKernel.zeroExtend K w)
    (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hwt) R hR
    (SubtypeKernel.zeroExtend_le K w R hR.le hwR)
  have hac := F.inverse_transition_ac_from_submersion σ source ε hε hw d.map d.joint d.identity d.spatial L hD
  have hs := F.inverse_smooth_density_source source.smooth_density ε hε hw d.map d.joint d.identity d.spatial
  refine ⟨{
    inverseMap := d.actualMap
    inverse_measurable := hD
    inverse_close := close
    inverse_plaques := d.plaqueInputs source.open_image hε hw K hV hG hcoreV hcoreG
    inverseWeight := W
    weight_measurable := hW
    weightBound := B
    weight_bounded := fun x a => (le_abs_self _).trans (hWB x a)
    weight_positive := hWp
    reference := σ.restrict K
    reference_finite := inferInstance
    reference_conull := ae_restrict_mem hK.measurableSet
    reference_core_support := subset_support_restrict_of_subset_interior σ
      (hcoreV.trans (interior_maximal hVK hV))
    transitionDensity := q'
    transition_measurable := hq'
    densityBound := Q
    densityBound_finite := hQ
    transition_bounded := fun x y => hqB' (x, y)
    transition_representation := repr'
    duality := DepartureWeightedRandomMap.normalized_isAdjoint (σ.restrict K) (L.law ε)
      (SubtypeKernel.zeroExtend K w) R (SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hwt)
      W hW H d.actualMap hH hD K hK.measurableSet change_variables
    inverse_absoluteContinuous := WeightedNoiseAbsoluteContinuity.killed_ac_restricted_reference
      (L.law ε) d.actualMap hD W hW σ K hK.measurableSet (fun x _ => hac x)
    inverse_smoothing := ?_ }⟩
  intro f hf hb
  exact (L.continuous_weighted_killed_from_unweighted_source ε hε d.actualMap hD W hW
    hW0 hWc B hB hWB K hK.measurableSet hs f hf hb).continuousOn

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
