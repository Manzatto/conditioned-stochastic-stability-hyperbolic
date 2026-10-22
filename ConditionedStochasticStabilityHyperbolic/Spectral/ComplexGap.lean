module

public import AbsorbingMarkovChains.ExponentialSpectralGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConditionedAverages
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller

/-! # Producing the real continuous-space gap from complex spectral data

The geometric power estimate is derived using Gelfand's formula. Inputs are
real-compatible leading eigenvectors and functionals and a strict complex
spectral-radius bound on the complementary operator. No irreducibility or
aperiodicity assumption is introduced. Spectral comparison and power-compact
spectral theory must produce these inputs for the actual noisy transfer.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ComplexGap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Complex normalized powers intertwine with their real counterparts. -/
theorem normalized_power_intertwines
    (P : E →L[ℝ] E) (Q : F →L[ℂ] F) (j : E →L[ℝ] F)
    (hcomm : ∀ x, Q (j x) = j (P x)) (r : ℝ) (n : ℕ) (x : E) :
    (((r : ℂ)⁻¹ • Q) ^ n) (j x) = j (((r⁻¹ • P) ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih]
    change (r : ℂ)⁻¹ • Q (j _) = j (r⁻¹ • P _)
    rw [hcomm, map_smul]
    simp only [← Complex.ofReal_inv]
    exact algebraMap_smul ℂ (r⁻¹) (j (P (((r⁻¹ • P) ^ n) x)))

/-- A strict complementary complex radius produces all real geometric gap
data, including time zero. The left eigenrelation is a spectral input, not a
measure assumption. -/
theorem exists_realRankOneSpectralData
    (P : E →L[ℝ] E) (Q : F →L[ℂ] F) (j : E →L[ℝ] F)
    (hj : ∀ x, ‖j x‖ = ‖x‖)
    (hcomm : ∀ x, Q (j x) = j (P x))
    (r : ℝ) (hr : 0 < r) (g one : E) (μ : E →L[ℝ] ℝ) (ℓ : F →L[ℂ] ℂ)
    (hreal : ∀ x, ℓ (j x) = (μ x : ℂ))
    (hpair : μ g = 1) (hmass : 0 < μ one)
    (hright : Q (j g) = (r : ℂ) • j g)
    (hleft : ∀ y, ℓ (Q y) = (r : ℂ) * ℓ y)
    (hspec : spectralRadius ℂ
      (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r (j g) ℓ) < ENNReal.ofReal r) :
    ∃ d : RankOneSpectralData P one, d.rate = r ∧ d.mean = μ ∧ d.eigenvector = g := by
  have hpairC : ℓ (j g) = 1 := by rw [hreal, hpair]; rfl
  have hrightR : P g = r • g := by
    have he : j (P g - r • g) = 0 := by
      rw [map_sub, map_smul, ← hcomm, hright]
      rw [show (r : ℂ) • j g = r • j g from algebraMap_smul ℂ r (j g)]
      exact sub_self _
    have hz : ‖P g - r • g‖ = 0 := by rw [← hj, he, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  obtain ⟨θ, hθ, hθone, C, hC, hgap⟩ :=
    AbsorbingMarkovChains.CompactRankOneGap.normalized_power_gap
      Q hr (j g) ℓ hpairC hright hleft hspec
  have hgapR (n : ℕ) (hn : 1 ≤ n) :
      ‖(r⁻¹ • P) ^ n - μ.smulRight g‖ ≤ C * θ ^ n := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hθ.le n))
    intro x
    have he : j (((r⁻¹ • P) ^ n - μ.smulRight g) x) =
        ((((r : ℂ)⁻¹ • Q) ^ n - ℓ.smulRight (j g)) (j x)) := by
      rw [sub_apply, sub_apply, map_sub, ← normalized_power_intertwines P Q j hcomm]
      rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
        map_smul, hreal]
      rw [show (μ x : ℂ) • j g = μ x • j g from algebraMap_smul ℂ (μ x) (j g)]
    rw [← hj, he]
    exact ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hgap n hn) (norm_nonneg _))).trans_eq
      (by rw [hj])
  let B := max C ‖1 - μ.smulRight g‖
  have hB : 0 ≤ B := hC.trans (le_max_left _ _)
  have hb (n : ℕ) : ‖(r⁻¹ • P) ^ n - μ.smulRight g‖ ≤ B * θ ^ n := by
    by_cases hn : n = 0
    · subst n
      simpa only [pow_zero, mul_one] using le_max_right C ‖1 - μ.smulRight g‖
    · exact (hgapR n (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le n))
  exact ⟨⟨r, hr, μ, g, hpair, hmass, hrightR, B, hB, θ, hθ.le, hθone, hb⟩,
    rfl, rfl, rfl⟩

end ConditionedStochasticStabilityHyperbolic.ComplexGap
