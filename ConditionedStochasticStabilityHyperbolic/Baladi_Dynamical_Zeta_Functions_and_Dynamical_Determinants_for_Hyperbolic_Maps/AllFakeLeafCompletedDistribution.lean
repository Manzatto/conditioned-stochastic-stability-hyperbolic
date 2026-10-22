module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafDyadicDistribution
public import LeanShared.Analysis.LaplacianSupportedTestJet
public import LeanShared.Analysis.SchwartzCoreDistribution

/-! The actual weighted dyadic completion has a constructed bilinear
Schwartz pairing and a proved finite distribution-order bound on compact
supports. The core pairing is the literal ambient integral. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafDyadicDistribution
open LeanShared
set_option maxHeartbeats 1600000
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : AllFakeLeafModel.ConeData U C)
  (b : OrthonormalBasis ι ℝ U)
  {Cplus Cminus : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
  (Φ : ConeDyadicSymbols.AngularCutoff Cplus Cminus) (K : Set E) (t : Bool→ℝ)
  (bounded : Bounded U C cone b χ Φ K t)

def pairing : Space U C cone b χ Φ K t bounded →ₗ[ℂ] (𝓢(E,ℂ) →ₗ[ℂ] ℂ) :=
  SchwartzCoreDistribution.pairing K (raw U C cone b χ Φ K t bounded)
    (constant U C cone b χ Φ t) (growth t+1) (AllFakeLeafDistribution.order U)
    (core_bound U C cone b χ Φ K t bounded)

theorem pairing_core (f : SchwartzJetSpace.supportedCore K) (test : 𝓢(E,ℂ)) :
    pairing U C cone b χ Φ K t bounded
      (DyadicCompletion.coreLift (raw U C cone b χ Φ K t bounded) f) test =
        ConeFourierBlocks.integralPairing f.val test :=
  SchwartzCoreDistribution.core K (raw U C cone b χ Φ K t bounded)
    (constant U C cone b χ Φ t) (growth t+1) (AllFakeLeafDistribution.order U)
    (core_bound U C cone b χ Φ K t bounded) f test

theorem finite_order_bound {κ : Type*} [Fintype κ]
    (basis : OrthonormalBasis κ ℝ E) (L : Set E) (closed : IsClosed L)
    (R : ℝ) (nonnegative : 0 ≤ R) (radius : ∀ x∈L, ‖x‖ ≤ R)
    (z : Space U C cone b χ Φ K t bounded) (test : 𝓢(E,ℂ))
    (supported : ∀ x∉L, test x=0) :
    ‖pairing U C cone b χ Φ K t bounded z test‖ ≤
      (constant U C cone b χ Φ t*((1+R)^(AllFakeLeafDistribution.order U)*
        (Fintype.card (LaplacianFiniteJet.Index κ 0)+
          Fintype.card (LaplacianFiniteJet.Index κ (growth t+1)))))*‖z‖*
            ‖SchwartzJetSpace.jetMap L (LaplacianFiniteJet.testWords basis (growth t+1)) test‖ :=
  SchwartzCoreDistribution.finite_order_bound K (raw U C cone b χ Φ K t bounded)
    (constant U C cone b χ Φ t) (growth t+1) (AllFakeLeafDistribution.order U)
    (core_bound U C cone b χ Φ K t bounded) basis L closed R nonnegative radius
    (constant_nonnegative U C cone b χ Φ t) z test supported
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafDyadicDistribution
