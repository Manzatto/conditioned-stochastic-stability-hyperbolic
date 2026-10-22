module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCompletedDistribution
public import LeanShared.Analysis.ConeSmoothCoreBounded
public import LeanShared.Analysis.CompactCompletedDistributionFaithful
public import LeanShared.Analysis.CompletedCorePairingContinuousRealization

/-! The actual all-fake-leaf block space and its faithful common distribution
realization are constructed from compact support and the finite exponents.
No block boundedness, distribution pairing, or faithfulness input remains. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalDistribution
open LeanShared AllFakeLeafModel AllFakeLeafDyadicDistribution
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι:Type*} [Fintype ι] [DecidableEq ι]
  (U:Submodule ℝ E) (C:Set E) (cone:ConeData U C) (basis:OrthonormalBasis ι ℝ U)
  {Cp Cm:Set E} (χ:ConeDyadicSymbols.RadialCutoff) (Φ:ConeDyadicSymbols.AngularCutoff Cp Cm)
  {K:Set E} (compact:IsCompact K) (t:Bool→ℝ)

include compact in
theorem bounded : Bounded U C cone basis χ Φ K t :=
  ConeSmoothCoreBounded.smoothCoreBounded volume (slopeBound U C cone basis)
    (family U C cone basis) χ Φ compact t

@[expose] def core := raw U C cone basis χ Φ K t (bounded U C cone basis χ Φ compact t)

abbrev Space := DyadicCompletion.closedCore (core U C cone basis χ Φ compact t)

@[expose] def pair : Space U C cone basis χ Φ compact t→ₗ[ℂ](𝓢(E,ℂ)→ₗ[ℂ]ℂ) :=
  pairing U C cone basis χ Φ K t (bounded U C cone basis χ Φ compact t)

theorem pairBound : ∀ test,∃coefficient:ℝ,∀f,
    ‖SchwartzAmbientBlocks.pairing K f test‖≤coefficient*‖core U C cone basis χ Φ compact t f‖ :=
  SchwartzCoreDistribution.bounded K (core U C cone basis χ Φ compact t)
    (constant U C cone basis χ Φ t) (growth t+1) (AllFakeLeafDistribution.order U)
    (core_bound U C cone basis χ Φ K t (bounded U C cone basis χ Φ compact t))

@[expose] def distribution : Space U C cone basis χ Φ compact t→L[ℂ](𝓢(E,ℂ)→ℂ) :=
  CompletedCorePairing.realization (core U C cone basis χ Φ compact t) (SchwartzAmbientBlocks.pairing K)

theorem distribution_core (f:SchwartzJetSpace.supportedCore K) (test:𝓢(E,ℂ)) :
    distribution U C cone basis χ Φ compact t
      (DyadicCompletion.coreLift (core U C cone basis χ Φ compact t) f) test=
      ConeFourierBlocks.integralPairing f.val test :=
  CompletedCorePairing.core (core U C cone basis χ Φ compact t) (SchwartzAmbientBlocks.pairing K)
    (pairBound U C cone basis χ Φ compact t) f test

theorem distribution_injective : Function.Injective (distribution U C cone basis χ Φ compact t) :=
  CompletedCorePairing.realization_injective _ _ (pairBound U C cone basis χ Φ compact t)
    (SchwartzAmbientBlocks.compact_completed_pairing_injective volume (slopeBound U C cone basis)
      (family U C cone basis) K (ConeDyadicSymbols.symbols χ Φ) t
      (bounded U C cone basis χ Φ compact t) (pairBound U C cone basis χ Φ compact t) compact)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafCanonicalDistribution
