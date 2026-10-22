module
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafConeComparison
public import LeanShared.Analysis.AmbientLeafIntegralFromNorm
public import LeanShared.Analysis.SchwartzAmbientRealization

/-! The actual between-cone convolution estimate holds in the constructed
ambient leaf norms, with one kernel mass constant. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (U : Submodule ℝ E) {C D : Set E} (coneC : ConeData U C) (coneD : ConeData U D)
  (μ : Measure U) [μ.IsAddHaarMeasure]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (basis : OrthonormalBasis ι ℝ U)
  (geometryC : ClassicalGeometry U μ basis) (geometryD : ClassicalGeometry U μ basis)

@[expose] def ambientRealize (f : 𝓢(E,ℂ)) :=
  SchwartzAmbientRealization.linearMap μ
    (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C coneC))
    (leaves U C coneC μ basis geometryC) f

include coneD geometryD in
theorem convolution_norm_between_cones (inside : C⊆D) (σ f : 𝓢(E,ℂ))
    (A:ℝ) (nonnegative : 0≤A)
    (mass : (∫⁻ z,‖FourierSchwartzKernel.kernel σ z‖ₑ)≤ENNReal.ofReal A) :
    ‖ambientRealize U coneC μ basis geometryC (ConeFourierBlocks.block σ f)‖≤
      A*‖ambientRealize U coneD μ basis geometryD f‖ := by
  let source := ambientRealize U coneD μ basis geometryD f
  have sourceBound (Δ : Index U D) : (∫⁻ x,‖f x‖ₑ
      ∂EmbeddedSubmanifoldVolume.volume U μ Δ.val)≤ENNReal.ofReal ‖source‖ := by
    have actual := GraphLeafNorm.ambient_lintegral_le_norm μ
      (leaves U D coneD μ basis geometryD) source f
      (SchwartzAmbientRealization.linearMap_ae μ
        (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U D coneD))
        (leaves U D coneD μ basis geometryD) f) Δ
    rw [leaves_measure U D coneD μ basis geometryD Δ] at actual
    simpa only [inducedVolume] using actual
  apply GraphLeafNorm.ambient_norm_le_of_lintegral μ
    (leaves U C coneC μ basis geometryC)
    (ambientRealize U coneC μ basis geometryC (ConeFourierBlocks.block σ f))
    (ConeFourierBlocks.block σ f) (A*‖source‖) (mul_nonneg nonnegative (norm_nonneg _))
  · exact SchwartzAmbientRealization.linearMap_ae μ
      (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C coneC))
      (leaves U C coneC μ basis geometryC) _
  · intro Γ
    rw [leaves_measure U C coneC μ basis geometryC Γ,ENNReal.ofReal_mul nonnegative]
    simp only [inducedVolume]
    exact (convolution_cone_bound U coneC inside μ σ f _ sourceBound Γ).trans
      (mul_le_mul_of_nonneg_right mass bot_le)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
