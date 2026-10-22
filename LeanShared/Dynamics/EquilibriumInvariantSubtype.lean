module

public import LeanShared.Dynamics.EntropyMeasurableEmbedding
public import LeanShared.Dynamics.PressureInvariantSubtype
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual equilibrium probabilities on an invariant subtype push to
literal ambient equilibrium probabilities, preserving full metric entropy. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem IsEquilibriumState.map_subtype (T : X → X) (K : Set X) (measurableK : MeasurableSet K)
    (measurableT : Measurable T) (S : K → K) (same : ∀ x, (S x).val=T x.val)
    (φ : X → ℝ) (measurableφ : Measurable φ) (μ : ProbabilityMeasure K)
    (state : IsEquilibriumState S (fun x => φ x.val) univ μ) :
    IsEquilibriumState T φ K (μ.map Subtype.val) := by
  let : Nonempty K := nonempty_of_isProbabilityMeasure (μ : Measure K)
  have measurableS := state.1
  have equivariance : Semiconj (Subtype.val : K → X) S T := same
  have entropyEq := entropy_map_embedding (Subtype.val : K → X)
    (MeasurableEmbedding.subtype_coe measurableK) S T equivariance measurableT (μ : Measure K)
  have mapEq : ((μ : Measure K).map Subtype.val).map T=(μ : Measure K).map Subtype.val := by
    rw [Measure.map_map measurableT measurable_subtype_coe]
    have composition : T ∘ (Subtype.val : K → X)=Subtype.val ∘ S := funext (fun x => (same x).symm)
    rw [composition,←Measure.map_map measurable_subtype_coe measurableS,state.2.1]
  refine ⟨measurableT,mapEq,?_,?_,?_⟩
  · change (μ : Measure K).map Subtype.val Kᶜ=0
    rw [Measure.map_apply measurable_subtype_coe measurableK.compl]
    have empty : (Subtype.val : K → X) ⁻¹' Kᶜ=∅ := by ext x; simp only [mem_preimage,mem_compl_iff,mem_empty_iff_false,iff_false]; exact not_not_intro x.property
    rw [empty,measure_empty]
  · exact (integrable_map_measure measurableφ.aestronglyMeasurable measurable_subtype_coe.aemeasurable).mpr state.2.2.2.1
  · change entropy T ((μ : Measure K).map Subtype.val) +
      ((∫ x, φ x ∂((μ : Measure K).map Subtype.val) : ℝ) : EReal) = pressure T φ K
    rw [entropyEq,integral_map_of_stronglyMeasurable measurable_subtype_coe measurableφ.stronglyMeasurable,
      ←pressure_restriction S same φ]
    exact state.2.2.2.2

end LeanShared.ThermodynamicDefinitions
