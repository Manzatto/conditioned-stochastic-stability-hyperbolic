module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafSchwartzPairing
public import LeanShared.Analysis.AnnularDualPairing
public import LeanShared.Analysis.AnnularSchwartzSeminormDecay
import Mathlib.Tactic.Ring

/-! Actual full fake-leaf bounds control annular distribution pairings with
arbitrarily large frequency gain. All dual cutoffs and elliptic multipliers
are constructed from the original radial cutoff. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared LeanShared.FourierSchwartzKernel
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem exists_annular_pairing_bound (U : Submodule ℝ E) (C : Set E)
    (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U)
    (χ : ConeDyadicSymbols.RadialCutoff) (n m : ℕ)
    (order : (Module.finrank ℝ Uᗮ:ℝ)<(m:ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (σ f test : 𝓢(E,ℂ)) (A r : ℝ),
      ∀ (_ : 0 ≤ A) (_ : 1 ≤ r),
      (∀ ξ, σ ξ ≠ 0 → 1/2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2) →
      (∀ Γ : Index U C,
        (∫ x, ‖ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f x‖
          ∂inducedVolume U volume Γ.val) ≤ A) →
      r^(2*n)*‖∫ x, ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f x*test x‖ ≤
        D*A*ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n test) := by
  obtain ⟨B,nonnegative,pairing⟩ := exists_schwartz_pairing_bound U C cone b m order
  let dual := AnnularDualCutoff.symbol (E:=E) χ
  let param := AnnularEllipticSymbol.symbol dual (AnnularDualCutoff.compact χ)
    (1/4) (by norm_num) (fun ξ small=>AnnularDualCutoff.collar χ small) n
  let moment := ∫ y:E, ‖kernel param y‖*(1+‖y‖)^m
  have momentNonnegative : 0 ≤ moment := integral_nonneg fun y=>by positivity
  refine ⟨B*2^m*moment,by positivity,fun σ f test A r hA hr annulus leaves=>?_⟩
  have estimate := pairing (ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f)
    (ConeFourierBlocks.block (dilateSymbol dual r (by linarith)) test) A leaves
  rw [AnnularDualCutoff.absorb χ σ annulus r (by linarith) f test] at estimate
  have gain := AnnularEllipticSymbol.seminorm_decay dual (AnnularDualCutoff.compact χ)
    (1/4) (by norm_num) (fun ξ small=>AnnularDualCutoff.collar χ small) n m r hr test
  change r^(2*n)*ObliqueSchwartzDecay.seminorm m
    (ConeFourierBlocks.block (dilateSymbol dual r (by linarith)) test) ≤
      (2^m*ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n test))*moment at gain
  calc
    _ ≤ r^(2*n)*(B*A*ObliqueSchwartzDecay.seminorm m
        (ConeFourierBlocks.block (dilateSymbol dual r (by linarith)) test)) :=
      mul_le_mul_of_nonneg_left estimate (by positivity)
    _ = B*A*(r^(2*n)*ObliqueSchwartzDecay.seminorm m
        (ConeFourierBlocks.block (dilateSymbol dual r (by linarith)) test)) := by ring
    _ ≤ B*A*((2^m*ObliqueSchwartzDecay.seminorm m
        (FourierSchwartzLaplacian.power n test))*moment) :=
      mul_le_mul_of_nonneg_left gain (mul_nonneg nonnegative hA)
    _ = _ := by ring
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
