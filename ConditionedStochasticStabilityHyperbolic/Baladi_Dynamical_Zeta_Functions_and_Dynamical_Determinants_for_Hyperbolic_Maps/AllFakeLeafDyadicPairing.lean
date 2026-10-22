module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafDyadicBlockPairing
public import LeanShared.Analysis.ConeFourierPairingResolution

/-! The actual full dyadic core norm controls ambient test pairings.
Polynomial block growth is allowed; frequency decay is proved and summed. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped SchwartzMap Topology
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared LeanShared.ConeDyadicSymbols
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem half_sum_bound (N : ℕ) : ∑ n ∈ Finset.range N, (1/2:ℝ)^n ≤ 2 := by
  have identity : ∑ n ∈ Finset.range N, (1/2:ℝ)^n=2-2*(1/2:ℝ)^N := by
    induction N with
    | zero => norm_num
    | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [identity]
  linarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) N]

theorem exists_dyadic_pairing_bound (U : Submodule ℝ E) (C : Set E)
    (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U)
    {Cplus Cminus : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
    (q m : ℕ) (order : (Module.finrank ℝ Uᗮ:ℝ)<(m:ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f test : 𝓢(E,ℂ)) (A : ℝ), 0 ≤ A →
      (∀ (j : ℕ × Bool) (Γ : Index U C),
        (∫ x, ‖ConeFourierBlocks.block (symbols χ Φ j) f x‖ ∂inducedVolume U volume Γ.val) ≤
          A*((2:ℝ)^j.1)^q) →
      ‖∫ x, f x*test x‖ ≤
        D*A*(ObliqueSchwartzDecay.seminorm m test+
          ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power (q+1) test)) := by
  obtain ⟨D,hD,blockBound⟩ := exists_dyadic_block_pairing_bound U C cone b χ Φ q m order
  refine ⟨4*D,by positivity,fun f test A hA leaves=>?_⟩
  let B := D*A*(ObliqueSchwartzDecay.seminorm m test+
    ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power (q+1) test))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have bounds := blockBound f test A hA leaves
  have finiteBound : ∀ N, ‖∫ x, ConeFourierPairingResolution.partialSum χ Φ N f x*test x‖ ≤ 4*B := by
    intro N
    change ‖ConeFourierBlocks.integralPairing
      (ConeFourierPairingResolution.partialSum χ Φ N f) test‖ ≤ _
    simp only [ConeFourierPairingResolution.partialSum,map_sum,LinearMap.sum_apply,
      ConeFourierBlocks.integralPairing_apply]
    calc
      _ ≤ ∑ n ∈ Finset.range (N+1), ∑ s : Bool,
          ‖∫ x, ConeFourierBlocks.block (symbols χ Φ (n,s)) f x*test x‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n _
        exact norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (N+1), ∑ _s : Bool, B*(1/2:ℝ)^n := by
        apply Finset.sum_le_sum
        intro n _
        apply Finset.sum_le_sum
        intro s _
        exact bounds (n,s)
      _ = (2*B)*∑ n ∈ Finset.range (N+1), (1/2:ℝ)^n := by
        simp only [Fintype.sum_bool,← two_mul,mul_assoc,Finset.mul_sum]
      _ ≤ (2*B)*2 := mul_le_mul_of_nonneg_left (half_sum_bound (N+1)) (by positivity)
      _ = _ := by ring
  have result := le_of_tendsto (ConeFourierPairingResolution.pairing_converges χ Φ f test).norm
    (Filter.Eventually.of_forall finiteBound)
  exact result.trans_eq (by dsimp only [B]; ring)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
