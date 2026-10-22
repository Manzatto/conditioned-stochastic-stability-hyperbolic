module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafConvolutionNorm
public import LeanShared.Analysis.ConeNeighborNormComparison
public import LeanShared.Analysis.ConeKernelUniformMass
public import LeanShared.Analysis.SchwartzAmbientBlocks

/-! The smooth-core norm comparison for ordered cone systems is proved for
all of the manuscript's fake leaves and the literal physical block norm.
No comparison inequality or completed comparison map is supplied. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared ConeDyadicSymbols ConeSymbolOverlap BTLinkedDyadicWeights
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (U : Submodule ℝ E) {C D Cm Dm : Set E}
  (coneC : ConeData U C) (coneD : ConeData U D)
  (μ : Measure U) [μ.IsAddHaarMeasure]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (basis : OrthonormalBasis ι ℝ U)
  (geometryC : ClassicalGeometry U μ basis) (geometryD : ClassicalGeometry U μ basis)
  (K : Set E) (χ ψ : RadialCutoff) (Φ : AngularCutoff C Cm) (Ψ : AngularCutoff D Dm)
  (t s:ℝ)

@[expose] def physicalConeCore
    (bounded : SchwartzAmbientBlocks.SmoothCoreBounded μ
      (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C coneC))
      (leaves U C coneC μ basis geometryC) K (symbols χ Φ) (exponent t s)) :=
  SchwartzAmbientBlocks.coreMap μ
    (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C coneC))
    (leaves U C coneC μ basis geometryC) K (symbols χ Φ) (exponent t s) bounded

theorem exists_ordered_core_comparison (inside : C⊆D)
    (ordered : ∀ ξ:E,‖ξ‖=1→ξ∉D→ξ∈Cm) (order : s≤t)
    (boundedC : SchwartzAmbientBlocks.SmoothCoreBounded μ
      (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C coneC))
      (leaves U C coneC μ basis geometryC) K (symbols χ Φ) (exponent t s))
    (boundedD : SchwartzAmbientBlocks.SmoothCoreBounded μ
      (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U D coneD))
      (leaves U D coneD μ basis geometryD) K (symbols ψ Ψ) (exponent t s)) :
    ∃ constant:ℝ,0≤constant ∧ ∀ f:SchwartzJetSpace.supportedCore K,
      ‖physicalConeCore U coneC μ basis geometryC K χ Φ t s boundedC f‖≤
        constant*‖physicalConeCore U coneD μ basis geometryD K ψ Ψ t s boundedD f‖ := by
  obtain ⟨A,nonnegativeA,mass⟩ := exists_uniform_kernel_mass χ Φ
  let R := (2:ℝ)^(3*(|s|+|t|))
  have nonnegativeR : 0≤R := (Real.rpow_pos_of_pos (by norm_num) _).le
  refine ⟨6*A*R,by positivity,?_⟩
  intro f
  let N := ‖physicalConeCore U coneD μ basis geometryD K ψ Ψ t s boundedD f‖
  have nonnegativeN : 0≤N := norm_nonneg _
  have sourceBound (j:ℕ×Bool) :
      ‖ambientRealize U coneD μ basis geometryD
        (anisotropicWeight t s j • ConeFourierBlocks.block (symbols ψ Ψ j) f.val)‖≤N := by
    change ‖SchwartzAmbientRealization.linearMap μ
      (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U D coneD))
      (leaves U D coneD μ basis geometryD) _‖≤N
    rw [map_smul]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero
      (physicalConeCore U coneD μ basis geometryD K ψ Ψ t s boundedD f) j
  apply lp.norm_le_of_forall_le (mul_nonneg (by positivity : 0≤6*A*R) nonnegativeN)
  intro j
  have row := normalized_row_norm_le χ ψ Φ Ψ ordered t s order
    (SchwartzAmbientRealization.linearMap μ
      (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C coneC))
      (leaves U C coneC μ basis geometryC)) A N nonnegativeA nonnegativeN j.1 j.2 f.val
    (fun k _=>(convolution_norm_between_cones U coneC coneD μ basis geometryC geometryD inside
      (symbols χ Φ j) (anisotropicWeight t s k • ConeFourierBlocks.block (symbols ψ Ψ k) f.val)
      A nonnegativeA (mass j)).trans (mul_le_mul_of_nonneg_left (sourceBound k) nonnegativeA))
  have coordinate : physicalConeCore U coneC μ basis geometryC K χ Φ t s boundedC f j=
      anisotropicWeight t s j • SchwartzAmbientRealization.linearMap μ
        (GraphJacobian.densityBound_nonneg (ι:=ι) (slope U C coneC))
        (leaves U C coneC μ basis geometryC) (ConeFourierBlocks.block (symbols χ Φ j) f.val) := rfl
  rw [coordinate]
  simpa only [map_smul,Prod.mk.eta,R] using row
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
