module

public import ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-! # The produced local noisy operator is the actual global closed-layer operator

Restricting the full process, killed on the fixed live set, to any contained
closed analytic layer gives the actual noise chain used by the local KL and
collar producers. Departure weights agree by restriction, with one common
normalization. The operator identity is proved from the actual kernels.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualNoiseClosedLayer
open LeanShared.RandomMapKernel LeanShared.WeightedConditioning RestrictedLayerChain ComplexStrongFeller
variable {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
  (V K : Set X) (hV : MeasurableSet V) (hK : MeasurableSet K) (hKV : K ⊆ V)
  (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
include hKV in
/-- Actual closed-layer restriction agrees with the literal local noise
chain, including weight normalization and departure state indexing. -/
theorem local_killedTransition_eq_global_layer :
    (RestrictedNoise.chain ρ F hF K hK (fun x : K => w x.val)
      (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)).killedTransition =
      (chain (NoiseKernel.chain ρ F hF V hV w hw R hR hwR) K hK).killedTransition := by
  rw [killedTransition]
  ext x S hS
  rw [RestrictedNoise.killedTransition, LeanShared.SubtypeKernel.restrict_apply_set _ K hK x S hS,
    NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  simp only [normalizedKernel, realWeightedKernel_apply, Measure.smul_apply, smul_eq_mul]
  rw [RestrictedNoise.liveKernel, LeanShared.SubtypeKernel.restrict_apply_set _ K hK x S hS]
  have hi : Subtype.val '' S ⊆ V := by
    rintro y ⟨z, _, rfl⟩
    exact hKV z.property
  change _ = _ * ((transition ρ F hF x.val).restrict V) (Subtype.val '' S)
  rw [Measure.restrict_eq_self _ hi]

include hKV in
/-- The local KL raw operator is exactly the raw actual global layer
operator, so no spectral comparison across a different killed process is
needed at this final source application. -/
theorem raw_local_transfer_eq_global_layer
    (hSF : HasStrongFellerKernel (NoiseKernel.chain ρ F hF V hV w hw R hR hwR))
    (hSFLocal : HasStrongFellerKernel (RestrictedNoise.chain ρ F hF K hK
      (fun x : K => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val))) :
    R • strongFellerTransferOperator (RestrictedNoise.chain ρ F hF K hK
      (fun x : K => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)) hSFLocal =
    R • transferOperator (𝕜 := ℝ)
      (chain (NoiseKernel.chain ρ F hF V hV w hw R hR hwR) K hK)
      (strongFeller (NoiseKernel.chain ρ F hF V hV w hw R hR hwR) hSF K hK) := by
  congr 1
  ext f x
  rw [strongFellerTransferOperator_represents, transferOperator_apply,
    local_killedTransition_eq_global_layer ρ F hF V K hV hK hKV w hw R hR hwR]

end ConditionedStochasticStabilityHyperbolic.Global.ActualNoiseClosedLayer
