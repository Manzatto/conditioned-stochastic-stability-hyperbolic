module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafDyadicPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafDistribution
public import LeanShared.Analysis.SchwartzBlockPolynomialGrowth
import Mathlib.Tactic.FinCases

/-! The literal weighted full-fake-leaf dyadic completion has its actual
ambient distribution pairing. Frequency growth and finite distribution order
are derived, rather than supplied as a source. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafDyadicDistribution
open LeanShared AllFakeLeafModel
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U)
  {Cplus Cminus : Set E} (χ : ConeDyadicSymbols.RadialCutoff)
  (Φ : ConeDyadicSymbols.AngularCutoff Cplus Cminus) (K : Set E) (t : Bool→ℝ)

def family := leaves U C cone volume b (ClassicalGeometry.proved U volume b)
omit [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
theorem slopeBound (_b : OrthonormalBasis ι ℝ U) :
    0 ≤ GraphJacobian.densityBound (ι:=ι) (slope U C cone) :=
  GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C cone)
def Bounded := SchwartzAmbientBlocks.SmoothCoreBounded volume (slopeBound U C cone b)
  (family U C cone b) K (ConeDyadicSymbols.symbols χ Φ) t
variable (bounded : Bounded U C cone b χ Φ K t)
def raw := SchwartzAmbientBlocks.coreMap volume (slopeBound U C cone b)
  (family U C cone b) K (ConeDyadicSymbols.symbols χ Φ) t bounded
abbrev Space := DyadicCompletion.closedCore (raw U C cone b χ Φ K t bounded)

def growth : ℕ := ⌈max (-t false) (-t true)⌉₊
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
theorem growth_margin (s : Bool) : -t s ≤ growth t := by
  have bound : max (-t false) (-t true) ≤ (growth t:ℝ) := Nat.le_ceil _
  cases s
  · exact (le_max_left _ _).trans bound
  · exact (le_max_right _ _).trans bound

def constant : ℝ := (exists_dyadic_pairing_bound U C cone b χ Φ (growth t)
  (AllFakeLeafDistribution.order U) (AllFakeLeafDistribution.order_gt U)).choose

theorem constant_nonnegative : 0 ≤ constant U C cone b χ Φ t :=
  (exists_dyadic_pairing_bound U C cone b χ Φ (growth t)
    (AllFakeLeafDistribution.order U) (AllFakeLeafDistribution.order_gt U)).choose_spec.1

theorem core_bound (f : SchwartzJetSpace.supportedCore K) (test : 𝓢(E,ℂ)) :
    ‖ConeFourierBlocks.integralPairing f.val test‖ ≤
      constant U C cone b χ Φ t*‖raw U C cone b χ Φ K t bounded f‖*
        (ObliqueSchwartzDecay.seminorm (AllFakeLeafDistribution.order U) test+
          ObliqueSchwartzDecay.seminorm (AllFakeLeafDistribution.order U)
            (FourierSchwartzLaplacian.power (growth t+1) test)) := by
  apply (exists_dyadic_pairing_bound U C cone b χ Φ (growth t)
    (AllFakeLeafDistribution.order U) (AllFakeLeafDistribution.order_gt U)).choose_spec.2
      f.val test ‖raw U C cone b χ Φ K t bounded f‖ (norm_nonneg _)
  intro j Γ
  let z := SchwartzAmbientBlocks.block volume (slopeBound U C cone b)
    (family U C cone b) K (ConeDyadicSymbols.symbols χ Φ) j f
  have integralBound := represented_integral_le U C cone volume b
    (ClassicalGeometry.proved U volume b) z (ConeFourierBlocks.block (ConeDyadicSymbols.symbols χ Φ j) f.val)
    (SchwartzAmbientRealization.linearMap_ae volume (slopeBound U C cone b)
      (family U C cone b) (ConeFourierBlocks.block (ConeDyadicSymbols.symbols χ Φ j) f.val)) Γ
  exact integralBound.trans (SchwartzAmbientBlocks.unweighted_bound volume (slopeBound U C cone b)
    (family U C cone b) K (ConeDyadicSymbols.symbols χ Φ) t bounded (growth t) (growth_margin t) f j)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafDyadicDistribution
