module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCanonicalDistribution
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafOrderedConeCoreComparison
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.CrossConeComparisonWitness

/-! The ordered-cone completed injection is constructed with its actual
physical core, exact common distribution and faithful realization. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalCrossCone
open LeanShared AllFakeLeafModel AllFakeLeafCanonicalDistribution
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι:Type*} [Fintype ι] [DecidableEq ι]
  (U:Submodule ℝ E) {C D Cm Dm:Set E} (coneC:ConeData U C) (coneD:ConeData U D)
  (basis:OrthonormalBasis ι ℝ U)
  (χ ψ:ConeDyadicSymbols.RadialCutoff)
  (Φ:ConeDyadicSymbols.AngularCutoff C Cm) (Ψ:ConeDyadicSymbols.AngularCutoff D Dm)
  {K:Set E} (compact:IsCompact K) (t s:ℝ)

include coneD Ψ in
theorem comparison (inside:C⊆D) (ordered:∀ξ:E,‖ξ‖=1→ξ∉D→ξ∈Cm) (order:s≤t) :
    ∃ A:ℝ,0≤A ∧ ∀ f:SchwartzJetSpace.supportedCore K,
      ‖core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s) f‖≤
        A*‖core U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s) f‖ :=
  exists_ordered_core_comparison U coneC coneD volume basis
    (ClassicalGeometry.proved U volume basis) (ClassicalGeometry.proved U volume basis)
    K χ ψ Φ Ψ t s inside ordered order
    (bounded U C coneC basis χ Φ compact _) (bounded U D coneD basis ψ Ψ compact _)

variable {η:ℝ} (positive:0<η) (δ:Bool→ℝ) (nonnegative:∀b,0≤δ b)

@[expose] def embedding :
    Space U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s)→L[ℂ]
      DyadicCompletion.closedCore (DyadicCompletion.finalCore
        (core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s)) η positive δ nonnegative) :=
  CrossConeCompactEmbedding.Canonical.embedding
    (core U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s))
    (core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s)) positive δ nonnegative

theorem embedding_core (inside:C⊆D) (ordered:∀ξ:E,‖ξ‖=1→ξ∉D→ξ∈Cm) (order:s≤t)
    (f:SchwartzJetSpace.supportedCore K) :
    embedding U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative
      (DyadicCompletion.coreLift (core U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s)) f)=
      DyadicCompletion.coreLift (DyadicCompletion.finalCore
        (core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s)) η positive δ nonnegative) f := by
  exact CrossConeCompactEmbedding.Canonical.embedding_core_of_comparison
    (core U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s))
    (core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s)) positive δ nonnegative
    (comparison U coneC coneD basis χ ψ Φ Ψ compact t s inside ordered order) f

theorem embedding_injective (inside:C⊆D) (ordered:∀ξ:E,‖ξ‖=1→ξ∉D→ξ∈Cm) (order:s≤t) :
    Function.Injective (embedding U coneC coneD basis χ ψ Φ Ψ compact t s positive δ nonnegative) := by
  apply CrossConeCompactEmbedding.Canonical.embedding_injective_of_comparison
    (core U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s))
    (core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s)) positive δ nonnegative
    (comparison U coneC coneD basis χ ψ Φ Ψ compact t s inside ordered order)
    (distribution U D coneD basis ψ Ψ compact _) (distribution U C coneC basis χ Φ compact _) ?_
    (distribution_injective U D coneD basis ψ Ψ compact _)
  intro f
  funext test
  exact (distribution_core U C coneC basis χ Φ compact (BTLinkedDyadicWeights.exponent t s) f test).trans
    (distribution_core U D coneD basis ψ Ψ compact (BTLinkedDyadicWeights.exponent t s) f test).symm
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalCrossCone
