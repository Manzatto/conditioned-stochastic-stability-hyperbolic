module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! The norm of the actual ambient L¹ leaf family bounds every literal
induced-volume leaf integral of its represented function. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem represented_integral_le (U : Submodule ℝ E) (C : Set E) (cone : ConeData U C)
    (μ : Measure U) (b : OrthonormalBasis ι ℝ U) (geometry : ClassicalGeometry U μ b)
    (z : GraphLeafNorm.AmbientFamilySpace μ (leaves U C cone μ b geometry))
    (f : E → ℂ)
    (represents : ∀ Γ, z Γ =ᵐ[(leaves U C cone μ b geometry Γ).measure μ] f)
    (Γ : Index U C) : (∫ x, ‖f x‖ ∂inducedVolume U μ Γ.val) ≤ ‖z‖ := by
  rw [← leaves_measure U C cone μ b geometry Γ]
  calc
    _ = ∫ x, ‖(z Γ) x‖ ∂(leaves U C cone μ b geometry Γ).measure μ :=
      integral_congr_ae ((represents Γ).symm.fun_comp norm)
    _ = ‖z Γ‖ := (L1.norm_eq_integral_norm _).symm
    _ ≤ ‖z‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero z Γ
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
