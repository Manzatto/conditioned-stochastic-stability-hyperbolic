module

public import ConditionedStochasticStabilityHyperbolic.Global.PrefixCorrespondence
public import ConditionedStochasticStabilityHyperbolic.Global.WeightedAccessibility

/-!
# Ambient smoothing of a produced prefix eigenfunction

The prefix need not carry an invertible restriction of the deterministic
map. Its leading eigenfunction extends continuously by actual killed-kernel
smoothing and agrees exactly on the invariant prefix. Eigenrelations and
backward positivity are needed only at starting points in that prefix.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.AmbientPrefixEigenfunction
open AbsorbingMarkovChains ComplexStrongFeller LayerOperators LayerRankOne RestrictedLayerChain
open PrefixCorrespondence
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U)
  (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C U hU)
    (strongFeller C hSF U hU)) (1 : U →ᵇ ℝ))

def ambientVector : X →ᵇ ℝ := d.rate⁻¹ • extensionOperator C hSF U hU d.eigenvector

/-- The smoothed ambient vector restricts exactly to the prefix vector. -/
theorem ambientVector_coe (x : U) : ambientVector C hSF U hU d x.val = d.eigenvector x := by
  change d.rate⁻¹ * extensionOperator C hSF U hU d.eigenvector x.val = _
  rw [← integral_chain C hSF U hU, ← transferOperator_apply (chain C U hU) (strongFeller C hSF U hU)]
  have he := congrArg (fun f : U →ᵇ ℝ => f x) d.right_eigenvector
  change transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU) d.eigenvector x =
    d.rate * d.eigenvector x at he
  rw [he, ← mul_assoc, inv_mul_cancel₀ d.rate_pos.ne', one_mul]

/-- Actual positivity produces ambient nonnegativity without a chosen
extension of the prefix eigenfunction. -/
theorem ambientVector_nonneg (x : X) : 0 ≤ ambientVector C hSF U hU d x := by
  have hp := d.eigenvector_nonneg_of_positive (actual_transfer_positive (chain C U hU)
    (strongFeller C hSF U hU))
  change 0 ≤ d.rate⁻¹ * extensionOperator C hSF U hU d.eigenvector x
  rw [extensionOperator_apply_subtype]
  exact mul_nonneg (inv_nonneg.mpr d.rate_pos.le) (integral_nonneg hp)

/-- The original full kernel satisfies the eigenrelation at every invariant
prefix starting point, even though no full-space spectral gap is assumed. -/
theorem eigenrelation_on_prefix
    (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0) (x : U) :
    (∫ y, ambientVector C hSF U hU d y ∂C.killedTransition x.val) =
      d.rate * ambientVector C hSF U hU d x.val := by
  rw [← integral_compatible C U hU hsupport (ambientVector C hSF U hU d) x]
  have hf : (fun y : U => ambientVector C hSF U hU d y.val) = d.eigenvector := by
    funext y
    exact ambientVector_coe C hSF U hU d y
  rw [hf, ← transferOperator_apply (chain C U hU) (strongFeller C hSF U hU)]
  have he := congrArg (fun f : U →ᵇ ℝ => f x) d.right_eigenvector
  rw [ambientVector_coe C hSF U hU d x]
  exact he

section Noise
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
  (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
  (V : Set X) (hV : MeasurableSet V) (O : Set X) (hO : IsOpen O) (hOV : O ⊆ V) (φ : X → ℝ) (hφ : Measurable φ)
  (W : ℝ) (hW : 0 < W) (hbound : ∀ x, Real.exp (φ x) ≤ W)

include hFc hO hOV in
/-- Backward positivity comes from the actual exponential noise model and
prefix eigenrelation. It assumes no global leading spectral data. -/
theorem positive_before_control_on_prefix
    (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
    (hmodel : C.killedTransition = (NoiseKernel.chain ρ F hF V hV
      (fun z => Real.exp (φ z)) (Real.measurable_exp.comp hφ) W hW hbound).killedTransition)
    (x : X) (hx : x ∈ U) (ω : Ω) (hωV : F (x, ω) ∈ O)
    (hωpos : 0 < ambientVector C hSF U hU d (F (x, ω))) :
    0 < ambientVector C hSF U hU d x := by
  let g := ambientVector C hSF U hU d
  have hgi : Integrable g (LeanShared.RandomMapKernel.killed ρ F hF V hV x) := by
    change Integrable g ((LeanShared.RandomMapKernel.transition ρ F hF x).restrict V)
    exact Integrable.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (ae_of_all _ g.norm_coe_le_norm)
  have hgiO : Integrable g (LeanShared.RandomMapKernel.killed ρ F hF O hO.measurableSet x) := by
    change Integrable g ((LeanShared.RandomMapKernel.transition ρ F hF x).restrict O)
    exact Integrable.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (ae_of_all _ g.norm_coe_le_norm)
  have hpO := LeanShared.NoiseAccessibility.integral_killed_pos ρ F hF hFc O hO g g.continuous
    (ambientVector_nonneg C hSF U hU d) x hgiO ω hωV hωpos
  have hle : (LeanShared.RandomMapKernel.killed ρ F hF O hO.measurableSet x) ≤
      (LeanShared.RandomMapKernel.killed ρ F hF V hV x) := by
    exact Measure.restrict_mono_set _ hOV
  have hp := hpO.trans_le (integral_mono_measure hle
    (ae_of_all _ (ambientVector_nonneg C hSF U hU d)) hgi)
  have hi : 0 < ∫ y, g y ∂C.killedTransition x := by
    rw [hmodel, NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
    change 0 < ∫ y, g y ∂(ENNReal.ofReal (Real.exp (φ x) / W) •
      LeanShared.RandomMapKernel.killed ρ F hF V hV x)
    rw [integral_smul_measure, ENNReal.toReal_ofReal (div_pos (Real.exp_pos _) hW).le, smul_eq_mul]
    exact mul_pos (div_pos (Real.exp_pos _) hW) hp
  rw [eigenrelation_on_prefix C hSF U hU d hsupport ⟨x, hx⟩] at hi
  exact pos_of_mul_pos_right hi d.rate_pos.le

end Noise
end ConditionedStochasticStabilityHyperbolic.Global.AmbientPrefixEigenfunction
