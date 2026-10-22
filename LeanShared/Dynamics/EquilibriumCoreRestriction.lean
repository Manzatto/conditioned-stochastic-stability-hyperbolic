module

public import LeanShared.Dynamics.EquilibriumInvariantSubtype

/-! Every actual ambient equilibrium supported on a measurable invariant
core restricts to an actual equilibrium on the core, with exactly the same
pushed probability. No ambient potential measurability is required. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem IsEquilibriumState.exists_core_restriction (T : X → X) (K : Set X)
    (measurableK : MeasurableSet K) (S : K → K) (measurableS : Measurable S)
    (same : ∀ x, (S x).val=T x.val) (φ : X → ℝ) (μ : ProbabilityMeasure X)
    (state : IsEquilibriumState T φ K μ) :
    ∃ ν : ProbabilityMeasure K, (ν : Measure K).map Subtype.val=(μ : Measure X) ∧
      IsEquilibriumState S (fun x => φ x.val) univ ν := by
  let ρ := (μ : Measure X).comap (Subtype.val : K → X)
  have embedding := MeasurableEmbedding.subtype_coe measurableK
  have push : ρ.map Subtype.val=(μ : Measure X) := by
    rw [map_comap_subtype_coe measurableK,Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr state.2.2.1)]
  have probability : IsProbabilityMeasure ρ := by
    constructor
    have h : ρ.map Subtype.val univ=1 := by rw [push]; exact measure_univ
    rwa [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,preimage_univ] at h
  let ν : ProbabilityMeasure K := ⟨ρ,probability⟩
  have pushν : (ν : Measure K).map Subtype.val=(μ : Measure X) := push
  let : Nonempty K := nonempty_of_isProbabilityMeasure (ν : Measure K)
  have invariant : (ν : Measure K).map S=(ν : Measure K) := by
    apply embedding.map_injective
    rw [Measure.map_map measurable_subtype_coe measurableS]
    have composition : (Subtype.val : K → X) ∘ S=T ∘ Subtype.val := funext same
    rw [composition,←Measure.map_map state.1 measurable_subtype_coe]
    rw [pushν,state.2.1]
  have entropyEq := entropy_map_embedding (Subtype.val : K → X) embedding S T same state.1 (ν : Measure K)
  have integrable : Integrable φ ((ν : Measure K).map Subtype.val) := by
    rw [pushν]
    exact state.2.2.2.1
  have equality := state.2.2.2.2
  rw [←pushν] at equality
  change entropy T ((ν : Measure K).map Subtype.val) +
    ((∫ x, φ x ∂((ν : Measure K).map Subtype.val) : ℝ) : EReal) = _ at equality
  rw [entropyEq,embedding.integral_map φ,←pressure_restriction S same φ] at equality
  exact ⟨ν,pushν,measurableS,invariant,by simp,embedding.integrable_map_iff.mp integrable,equality⟩

end LeanShared.ThermodynamicDefinitions
