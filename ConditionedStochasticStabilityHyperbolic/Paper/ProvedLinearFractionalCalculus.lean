module

public import ConditionedStochasticStabilityHyperbolic.Paper.LinearRechartedNoise
public import LeanShared.Geometry.FractionalLinearRechartRegularity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! Construct the linear fractional calculus used in saddle stabilization. The constant is the
explicit linear model constant. -/

public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LinearRechartedManifold
variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  {T : M ≃ₜ M}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem factor_le (e : E ≃L[ℝ] F) (r : ℝ) (k : ℕ) (hk : k ≤ ⌊r⌋₊ + 1) :
    ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ^ k ≤
      linearModelConstant e r := by
  unfold linearModelConstant
  have powers : ‖e.symm.toContinuousLinearMap‖ ^ k ≤
      (max 1 ‖e.symm.toContinuousLinearMap‖) ^ (⌊r⌋₊ + 1) := by
    calc
      _ ≤ (max 1 ‖e.symm.toContinuousLinearMap‖) ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
      _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) hk
  exact mul_le_mul (le_max_right _ _) powers (pow_nonneg (norm_nonneg _) _)
    (zero_le_one.trans (le_max_left _ _))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem constant_one_le (e : E ≃L[ℝ] F) (r : ℝ) : 1 ≤ linearModelConstant e r := by
  unfold linearModelConstant
  exact one_le_mul_of_one_le_of_one_le (le_max_left _ _)
    (one_le_pow₀ (le_max_left _ _))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem holder_factor_le (e : E ≃L[ℝ] F) (r : ℝ) (nonnegative : 0 ≤ r) :
    (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ^ ⌊r⌋₊) *
        ‖e.symm.toContinuousLinearMap‖ ^ (r - (⌊r⌋₊ : ℝ)) ≤ linearModelConstant e r := by
  let B := max 1 ‖e.symm.toContinuousLinearMap‖
  have hB : 1 ≤ B := le_max_left _ _
  have powBound : ‖e.symm.toContinuousLinearMap‖ ^ ⌊r⌋₊ ≤ B ^ ⌊r⌋₊ :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
  have fractional : ‖e.symm.toContinuousLinearMap‖ ^ (r - (⌊r⌋₊ : ℝ)) ≤ B :=
    (Real.rpow_le_rpow (norm_nonneg _) (le_max_right _ _)
      (sub_nonneg.mpr (Nat.floor_le nonnegative))).trans
      (Real.rpow_le_self_of_one_le hB (Nat.self_sub_floor_lt_one r).le)
  calc
    _ ≤ (max 1 ‖e.toContinuousLinearMap‖ * B ^ ⌊r⌋₊) * B :=
      mul_le_mul (mul_le_mul (le_max_right _ _) powBound
        (pow_nonneg (norm_nonneg _) _) (zero_le_one.trans (le_max_left _ _))) fractional
        (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
    _ = linearModelConstant e r := by simp only [linearModelConstant, pow_succ, B]; ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Every linear coordinate-model equivalence has the exact fractional
calculus contract used by the original-noise constructor. -/
theorem proved_linearFractionalCalculus (e : E ≃L[ℝ] F) (r : ℝ) :
    LinearFractionalCalculus (T := T) e r where
  regular f hf := hf.linearRechart e
  whitney f A δ _hT hf source := by
    let := charts (M := M) e
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      have nonnegative : 0 ≤ δ := (dist_nonneg).trans (source.uniform x)
      exact (source.uniform x).trans (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (constant_one_le e r) nonnegative)
    · intro i
      simpa only [WhitneyAtlas.linearRechart, chartImage, mfld_simps] using source.target_control i
    · intro i k hk y hy
      have original : e.symm y ∈ A.coordinatePatch i := by
        simpa only [WhitneyAtlas.coordinatePatch, WhitneyAtlas.linearRechart, chartImage,
          mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph] using hy
      have bound := source.derivatives i k hk (e.symm y) original
      have nonnegative : 0 ≤ δ := (norm_nonneg _).trans bound
      change ‖iteratedFDeriv ℝ k (e ∘ A.coordinate f i ∘ e.symm) y -
        iteratedFDeriv ℝ k (e ∘ A.coordinate T i ∘ e.symm) y‖ ≤ _
      exact (LinearConjugateJets.norm_iterated_difference_le e _ _ k y).trans
        ((mul_le_mul_of_nonneg_left bound (by positivity)).trans
          (mul_le_mul_of_nonneg_right (factor_le e r k (by omega)) nonnegative))
    · intro unequal i y hy z hz
      have originalY : e.symm y ∈ A.coordinatePatch i := by
        simpa only [WhitneyAtlas.coordinatePatch, WhitneyAtlas.linearRechart, chartImage,
          mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph] using hy
      have originalZ : e.symm z ∈ A.coordinatePatch i := by
        simpa only [WhitneyAtlas.coordinatePatch, WhitneyAtlas.linearRechart, chartImage,
          mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph] using hz
      have bound := source.holder unequal i (e.symm y) originalY (e.symm z) originalZ
      have nonnegative : 0 ≤ δ := (norm_nonneg _).trans
        (source.derivatives i 0 (Nat.zero_le _) (e.symm y) originalY)
      let α := r - (⌊r⌋₊ : ℝ)
      let B := ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ ^ ⌊r⌋₊
      have hα : 0 ≤ α := sub_nonneg.mpr (Nat.floor_le hf.nonnegative)
      have hB : 0 ≤ B := by dsimp [B]; positivity
      change ‖(iteratedFDeriv ℝ ⌊r⌋₊ (e ∘ A.coordinate f i ∘ e.symm) y -
          iteratedFDeriv ℝ ⌊r⌋₊ (e ∘ A.coordinate T i ∘ e.symm) y) -
        (iteratedFDeriv ℝ ⌊r⌋₊ (e ∘ A.coordinate f i ∘ e.symm) z -
          iteratedFDeriv ℝ ⌊r⌋₊ (e ∘ A.coordinate T i ∘ e.symm) z)‖ ≤ _
      calc
        _ ≤ B * ‖(iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) (e.symm y) -
            iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) (e.symm y)) -
          (iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate f i) (e.symm z) -
            iteratedFDeriv ℝ ⌊r⌋₊ (A.coordinate T i) (e.symm z))‖ :=
          LinearConjugateJets.norm_iterated_increment_difference_le e _ _ _ y z
        _ ≤ B * (δ * ‖e.symm y - e.symm z‖ ^ α) :=
          mul_le_mul_of_nonneg_left bound hB
        _ ≤ B * (δ * (‖e.symm.toContinuousLinearMap‖ * ‖y-z‖) ^ α) := by
          gcongr
          simpa only [ContinuousLinearEquiv.coe_coe, map_sub] using
            e.symm.toContinuousLinearMap.le_opNorm (y-z)
        _ = (B * ‖e.symm.toContinuousLinearMap‖ ^ α) * (δ * ‖y-z‖ ^ α) := by
          rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
          ring
        _ ≤ linearModelConstant e r * δ * ‖y-z‖ ^ α := by
          simpa only [B, α, mul_assoc] using
            mul_le_mul_of_nonneg_right (holder_factor_le e r hf.nonnegative)
              (mul_nonneg nonnegative (Real.rpow_nonneg (norm_nonneg (y-z)) α))

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
