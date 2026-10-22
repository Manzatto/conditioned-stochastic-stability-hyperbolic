module

public import ConditionedStochasticStabilityHyperbolic.Global.LiveClosedLayerSource
public import ConditionedStochasticStabilityHyperbolic.Global.ClosedLayerReference
public import ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer

/-! # Actual prefix references delete only the proved null stratum boundary

Ambient transition density and the proved positive-boundary nullity descend
to the literal relative closed layer inside any selected trapping prefix.
No assumption on absorbing-boundary volume or full reference support is used.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace ConditionedStochasticStabilityHyperbolic.Global.PrefixReferenceNullity
open NestedLayerKernel RestrictedLayerChain LiveClosedLayerSource ClosedLayerReference
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- Ambient null closure discrepancy pulls back to the actual prefix
reference, even when the first stratum has an irregular absorbing boundary. -/
theorem relative_closed_stratum_extra_zero (σ : Measure X) (S V : Set X)
    (hV : MeasurableSet V) (hSV : S ⊆ V) (hnull : σ (closure S \ S) = 0) :
    (σ.comap (Subtype.val : V → X))
      (closure (innerLevel S V) \ innerLevel S V) = 0 := by
  rw [closure_live_stratum S V hSV, (MeasurableEmbedding.subtype_coe hV).comap_apply]
  apply le_antisymm _ bot_le
  apply (measure_mono ?_).trans_eq hnull
  rintro x ⟨y, hy, rfl⟩
  exact hy

/-- The actual twice restricted closed kernel has no mass on the deleted
literal-stratum complement, derived entirely from actual ambient density. -/
theorem actual_prefix_closed_complement_zero
    (C : AbsorbingMarkovChains.CanonicalChain X) (S V : Set X)
    (hS : MeasurableSet S) (hV : MeasurableSet V) (hSV : S ⊆ V)
    (σ : Measure X) (q : X × X → ENNReal)
    (hdensity : ∀ x, C.killedTransition x = σ.withDensity (fun y => q (x, y)))
    (hnull : σ (closure S \ S) = 0) :
    ∀ x : closure (innerLevel S V),
      (chain (chain C V hV) (closure (innerLevel S V)) isClosed_closure.measurableSet).killedTransition x
        (innerLevel (innerLevel S V) (closure (innerLevel S V)))ᶜ = 0 := by
  let CP := chain C V hV
  let σP := σ.comap (Subtype.val : V → X)
  let qP : V × V → ENNReal := fun y => q (y.1.val, y.2.val)
  let Sp := innerLevel S V
  let Kp := closure Sp
  have hSp : MeasurableSet Sp := hS.preimage measurable_subtype_coe
  have hKp : MeasurableSet Kp := isClosed_closure.measurableSet
  have hdenP : ∀ x : V, CP.killedTransition x = σP.withDensity (fun y => qP (x, y)) :=
    restricted_density_law C V hV σ q hdensity
  have hdenK := restricted_density_law CP Kp hKp σP qP hdenP
  have hn := relative_closed_stratum_extra_zero σ S V hV hSV hnull
  exact NullBoundaryLayer.boundary_mass_zero_of_density (chain CP Kp hKp) (innerLevel Sp Kp)
    (σP.comap (Subtype.val : Kp → V)) (fun y => qP (y.1.val, y.2.val)) hdenK
    (relative_stratum_complement_zero σP Sp Kp hKp hn)

end ConditionedStochasticStabilityHyperbolic.Global.PrefixReferenceNullity
