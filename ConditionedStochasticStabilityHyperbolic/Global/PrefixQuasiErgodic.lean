module

public import ConditionedStochasticStabilityHyperbolic.Global.PrefixCorrespondence

/-!
# Invariant-prefix quasi-ergodic probabilities are full-process probabilities

A genuine prefix QEM transfers to the original chain. This proves that the
several HG2 prefix products are actual QEMs for killing on the fixed absorbing
region, in addition to their pointwise conditioned-limit correspondence.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.PrefixQuasiErgodic
open AbsorbingMarkovChains RestrictedLayerChain PrefixCorrespondence
variable {X : Type*} [MeasurableSpace X]
  (C : CanonicalChain X) (U : Set X) (hU : MeasurableSet U)

/-- Kernel-invariant prefix restriction preserves the complete actual
quasi-ergodic probability property under state-space inclusion. -/
theorem full_process_isQuasiErgodic_of_prefix
    (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
    (ν : Measure U) (hq : (chain C U hU).IsQuasiErgodic ν) :
    C.IsQuasiErgodic (ν.map Subtype.val) := by
  let : IsProbabilityMeasure ν := hq.1
  refine ⟨by
    rw [Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable]
    infer_instance, ?_⟩
  intro f hf hb
  rw [(MeasurableEmbedding.subtype_coe hU).ae_map_iff]
  have hlim := hq.2 (fun y : U => f y.val) (hf.comp measurable_subtype_coe)
    (by obtain ⟨B, hB⟩ := hb; exact ⟨B, fun y => hB y.val⟩)
  filter_upwards [hlim] with x hx
  rw [(MeasurableEmbedding.subtype_coe hU).integral_map f]
  convert hx using 1
  funext n
  obtain ⟨B, hB⟩ := hb
  have hnorm : ∀ y, ‖f y‖ ≤ max B 0 := fun y => by
    simpa only [Real.norm_eq_abs] using (hB y).trans (le_max_left B 0)
  have he := conditioned_average_eq C U hU hsupport f hf (max B 0)
    (le_max_right _ _) hnorm n x
  have hextX : FeynmanKac.ext f = zeroExtension f := by
    funext z
    cases z <;> rfl
  have hextU : FeynmanKac.ext (fun y : U => f y.val) = zeroExtension (fun y : U => f y.val) := by
    funext z
    cases z <;> rfl
  rw [hextX, hextU] at he
  simpa only [pathBirkhoffSum, birkhoffSum] using he.symm

end ConditionedStochasticStabilityHyperbolic.Global.PrefixQuasiErgodic
