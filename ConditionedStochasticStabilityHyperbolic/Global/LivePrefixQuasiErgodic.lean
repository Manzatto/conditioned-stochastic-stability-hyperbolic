module

public import ConditionedStochasticStabilityHyperbolic.Global.PrefixQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.LiteralNoiseLiveChain

/-! # Literal live-state QEMs for every HG2 selected prefix

The full ambient process need not have a global dominant gap for a subordinate
selected prefix. Exact finite-prefix correspondence instead transports the
produced QEM directly to the literal live chain. No global gap is required.
-/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.LivePrefixQuasiErgodic
open AbsorbingMarkovChains RestrictedLayerChain PrefixCorrespondence ComplexStrongFeller
variable {X : Type*} [MeasurableSpace X]

theorem prefix_isQuasiErgodic_of_full_map
    (C : CanonicalChain X) (U : Set X) (hU : MeasurableSet U)
    (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
    (ν : Measure U) (hq : C.IsQuasiErgodic (ν.map Subtype.val)) :
    (chain C U hU).IsQuasiErgodic ν := by
  have : IsProbabilityMeasure (ν.map Subtype.val) := hq.1
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mp inferInstance
  refine ⟨inferInstance, ?_⟩
  intro f hf hb
  let fX := zeroExtend U f
  have hfX : Measurable fX := measurable_zeroExtend U hU f hf
  obtain ⟨B, hB⟩ := hb
  have hbound : ∀ y, ‖fX y‖ ≤ max B 0 := norm_zeroExtend_le U f (le_max_right B 0)
    (fun y => (hB y).trans (le_max_left B 0))
  have hlim := hq.2 fX hfX ⟨max B 0, hbound⟩
  rw [(MeasurableEmbedding.subtype_coe hU).ae_map_iff] at hlim
  filter_upwards [hlim] with x hx
  rw [(MeasurableEmbedding.subtype_coe hU).integral_map fX] at hx
  have hrestrict : (fun y : U => fX y.val) = f := by
    funext y
    exact zeroExtend_coe U f y
  rw [hrestrict] at hx
  convert hx using 1
  funext n
  have he := conditioned_average_eq C U hU hsupport fX hfX (max B 0)
    (le_max_right B 0) hbound n x
  have hextX : FeynmanKac.ext fX = AbsorbingMarkovChains.zeroExtension fX := by
    funext z
    cases z <;> rfl
  have hextU : FeynmanKac.ext (fun y : U => fX y.val) =
      AbsorbingMarkovChains.zeroExtension (fun y : U => fX y.val) := by
    funext z
    cases z <;> rfl
  rw [hextX, hextU, hrestrict] at he
  simpa only [pathBirkhoffSum, birkhoffSum] using he

theorem prefix_isQuasiErgodic_iff_full_map
    (C : CanonicalChain X) (U : Set X) (hU : MeasurableSet U)
    (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0) (ν : Measure U) :
    (chain C U hU).IsQuasiErgodic ν ↔ C.IsQuasiErgodic (ν.map Subtype.val) :=
  ⟨PrefixQuasiErgodic.full_process_isQuasiErgodic_of_prefix C U hU hsupport ν,
    prefix_isQuasiErgodic_of_full_map C U hU hsupport ν⟩

/-- A closed-layer product already produced as an ambient QEM becomes an
actual live-state QEM by its explicit state map, even for a non-global root. -/
theorem live_QEM_of_produced_closed_product
    (C : CanonicalChain X) (Live K : Set X) (hLive : MeasurableSet Live)
    (hKLive : K ⊆ Live) (hsupport : ∀ x ∈ Live, C.killedTransition x Liveᶜ = 0)
    (ν : Measure K) (hq : C.IsQuasiErgodic (ν.map Subtype.val)) :
    (chain C Live hLive).IsQuasiErgodic
      (ν.map (fun x : K => (⟨x.val, hKLive x.property⟩ : Live))) := by
  apply prefix_isQuasiErgodic_of_full_map C Live hLive hsupport
  have hm : Measurable (fun x : K => (⟨x.val, hKLive x.property⟩ : Live)) :=
    measurable_subtype_coe.subtype_mk
  rw [Measure.map_map measurable_subtype_coe hm]
  exact hq

end ConditionedStochasticStabilityHyperbolic.Global.LivePrefixQuasiErgodic
