module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafSchwartzPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafFamilyBounds
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafProvedGeometry
public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Analysis.DyadicCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

/-! Actual Schwartz pairings extend to the completion of the literal full
leaf norm. Geometry, continuity and the core pairing are constructed. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafDistribution
open LeanShared AllFakeLeafModel
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U)

theorem geometry : ClassicalGeometry U volume b := ClassicalGeometry.proved U volume b

def raw := SchwartzAmbientRealization.linearMap volume
  (GraphJacobian.densityBound_nonneg (ι := ι) (slope U C cone))
  (leaves U C cone volume b (geometry U b))

abbrev Space := DyadicCompletion.closedCore (raw U C cone b)

def order : ℕ := Module.finrank ℝ Uᗮ+1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem order_gt : (Module.finrank ℝ Uᗮ:ℝ)<(order U:ℝ) :=
  Nat.cast_lt.mpr (Nat.lt_succ_self _)

def constant : ℝ := (exists_schwartz_pairing_bound U C cone b (order U) (order_gt U)).choose

theorem constant_nonnegative : 0 ≤ constant U C cone b :=
  (exists_schwartz_pairing_bound U C cone b (order U) (order_gt U)).choose_spec.1

theorem core_bound (f test : 𝓢(E,ℂ)) :
    ‖ConeFourierBlocks.integralPairing f test‖ ≤
      constant U C cone b*‖raw U C cone b f‖*ObliqueSchwartzDecay.seminorm (order U) test := by
  apply (exists_schwartz_pairing_bound U C cone b (order U) (order_gt U)).choose_spec.2 f test
  intro Γ
  exact represented_integral_le U C cone volume b (geometry U b) (raw U C cone b f) f
    (SchwartzAmbientRealization.linearMap_ae volume
      (GraphJacobian.densityBound_nonneg (ι := ι) (slope U C cone))
      (leaves U C cone volume b (geometry U b)) f) Γ

def atTest (test : 𝓢(E,ℂ)) : Space U C cone b →L[ℂ] ℂ :=
  (ConeFourierBlocks.integralPairing.flip test).extendOfNorm
    (DyadicCompletion.coreLift (raw U C cone b))

theorem atTest_core (f test : 𝓢(E,ℂ)) :
    atTest U C cone b test (DyadicCompletion.coreLift (raw U C cone b) f) =
      ConeFourierBlocks.integralPairing f test := by
  apply LinearMap.extendOfNorm_eq (DyadicCompletion.coreLift_dense _)
  refine ⟨constant U C cone b*ObliqueSchwartzDecay.seminorm (order U) test,fun g => ?_⟩
  change ‖ConeFourierBlocks.integralPairing g test‖ ≤
    (constant U C cone b*ObliqueSchwartzDecay.seminorm (order U) test)*‖raw U C cone b g‖
  exact (core_bound U C cone b g test).trans_eq (mul_right_comm _ _ _)

theorem atTest_bound (test : 𝓢(E,ℂ)) (z : Space U C cone b) :
    ‖atTest U C cone b test z‖ ≤
      (constant U C cone b*ObliqueSchwartzDecay.seminorm (order U) test)*‖z‖ := by
  apply LinearMap.norm_extendOfNorm_apply_le (DyadicCompletion.coreLift_dense _)
  intro f
  change ‖ConeFourierBlocks.integralPairing f test‖ ≤
    (constant U C cone b*ObliqueSchwartzDecay.seminorm (order U) test)*‖raw U C cone b f‖
  exact (core_bound U C cone b f test).trans_eq (mul_right_comm _ _ _)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafDistribution
