module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelBumpIntegral
public import LeanShared.Geometry.TranslatedHolderTests
meta import Lean.LibrarySuggestions.Basic

/-! One chart of the regularized trace family. The tests are the chart-local Hölder tests
`wt · ρ(· - y)`, the bumps are `cut · ρ'(· - y)`. On a core function `v`, the coefficient
`y ↦ ψ_y(v)` is the convolution of `G(v) = wt · loc_j v` with `ρ`, and the bump integral is
the zero extension of `cut · (κ ⋆ G(v))`, `κ(y) = ∫ ρ(s) ρ'(y + s) ds`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelChartSmoothing"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace PhysicalModelFullTestPairing PhysicalModelLocalHolderTest

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (j : m.localization.indices) (cut : 𝓢(E, ℂ))
  (cutCompact : HasCompactSupport (cut : E → ℂ))
  (cutSupport : tsupport (cut : E → ℂ) ⊆
    ConstructedManifoldLocalization.support m.atlas m.localization j)
  (wt : 𝓢(E, ℂ)) (wtOne : ∀ z ∈ tsupport (wt : E → ℂ), cut z = 1)

include wtOne in
theorem wt_inside : tsupport (wt : E → ℂ) ⊆ tsupport (cut : E → ℂ) := fun z hz =>
  subset_tsupport _ (show cut z ≠ 0 by rw [wtOne z hz]; exact one_ne_zero)

/-- The weighted localization `G(v) = wt · loc_j v` on the cutoff support. -/
def weighted (v : Core (E := E) V) : supportedCore (tsupport (cut : E → ℂ)) :=
  ⟨LeafCommutator.mul wt (ConstructedManifoldLocalization.localize m.atlas m.localization
      m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      j v).val, fun x hx => by
    rw [LeafCommutator.mul_apply, image_eq_zero_of_notMem_tsupport
      (fun h => hx (wt_inside cut wt wtOne h)), zero_mul]⟩

theorem weighted_apply (v : Core (E := E) V) (x : E) :
    (weighted m j cut wt wtOne v).val x = wt x * (ConstructedManifoldLocalization.localize
      m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
      (SmoothSupportedManifoldCore.smooth V) j v).val x := by
  change LeafCommutator.mul wt _ x = _
  rw [LeafCommutator.mul_apply]

theorem weighted_tsupport (v : Core (E := E) V) :
    tsupport ((weighted m j cut wt wtOne v).val : E → ℂ) ⊆ tsupport (wt : E → ℂ) := by
  have h : ((weighted m j cut wt wtOne v).val : E → ℂ) = fun x => wt x * (ConstructedManifoldLocalization.localize
      m.atlas m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
      (SmoothSupportedManifoldCore.smooth V) j v).val x := funext (weighted_apply m j cut wt wtOne v)
  rw [h]
  exact tsupport_mul_subset_left

section Coefficient
variable {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
  (ρ : 𝓢(E, ℂ)) (vf : E → BoundedHolderSpace.graph E bt)
  (hvf : ∀ y z, BoundedHolderSpace.physical E bt (vf y) z = wt z * ρ (z - y))

include hbt hbt1 localBound hvf in
/-- The coefficient of a core function is the convolution of its weighted localization. -/
theorem coefficient_apply (v : Core (E := E) V) (y : E) :
    test m j (vf y) (coreLift m.qa v) = ∫ z, (weighted m j cut wt wtOne v).val z * ρ (z - y) := by
  rw [test_core m hbt hbt1 localBound j (vf y) v, corePairing_apply]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [hvf, weighted_apply]
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem continuous_of_sub_bound {Y G Z : Type*} [PseudoMetricSpace Y] [SeminormedAddCommGroup G]
    [SeminormedAddCommGroup Z] (T : G → Z) (hsub : ∀ v w, T (v - w) = T v - T w) (C : ℝ)
    (hC : ∀ v, ‖T v‖ ≤ C * ‖v‖) (vf : Y → G) (hv : Continuous vf) :
    Continuous (fun y => T (vf y)) :=
  continuous_of_dist_le _ vf C (fun y y' => by
    rw [dist_eq_norm, dist_eq_norm, ← hsub]; exact hC _) hv

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem lipschitz_continuous {Y G : Type*} [PseudoMetricSpace Y] [SeminormedAddCommGroup G]
    (vf : Y → G) (K : ℝ) (lip : ∀ y y', ‖vf y - vf y'‖ ≤ K * dist y y') : Continuous vf :=
  continuous_of_dist_le vf id K (fun y y' => by rw [dist_eq_norm]; exact lip y y') continuous_id

include hbt hbt1 localBound in
/-- The test family is continuous in operator norm. -/
theorem test_continuous (K : ℝ) (lip : ∀ y y', ‖vf y - vf y'‖ ≤ K * dist y y') :
    Continuous (fun y => test m j (vf y)) :=
  let h := test_norm m hbt hbt1 localBound j
  continuous_of_sub_bound (test m j) (test_sub m hbt hbt1 localBound j) h.choose h.choose_spec.2
    vf (lipschitz_continuous vf K lip)

include hbt hbt1 localBound in
theorem coefficient_continuous (K : ℝ) (lip : ∀ y y', ‖vf y - vf y'‖ ≤ K * dist y y')
    (v : Core (E := E) V) : Continuous (fun y => test m j (vf y) (coreLift m.qa v)) :=
  (test_continuous m j hbt hbt1 localBound vf K lip).clm_apply continuous_const

include hbt hbt1 localBound hvf cut wtOne in
theorem coefficient_compact (wtCompact : HasCompactSupport (wt : E → ℂ))
    (ρc : HasCompactSupport (ρ : E → ℂ)) (v : Core (E := E) V) :
    HasCompactSupport (fun y => test m j (vf y) (coreLift m.qa v)) := by
  refine HasCompactSupport.intro ((wtCompact.prod ρc).image (continuous_fst.sub continuous_snd))
    fun y hy => ?_
  rw [coefficient_apply m j cut wt wtOne hbt hbt1 localBound ρ vf hvf v y]
  refine integral_eq_zero_of_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport (wt : E → ℂ)
  · have out : z - y ∉ tsupport (ρ : E → ℂ) := fun h => hy ⟨(z, z - y), ⟨hz, h⟩, sub_sub_cancel z y⟩
    simp [image_eq_zero_of_notMem_tsupport out]
  · have zero : (weighted m j cut wt wtOne v).val z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (weighted_tsupport m j cut wt wtOne v h))
    simp [zero]

include hbt hbt1 localBound hvf in
/-- The smoothed bump coefficient is a cutoff convolution of the weighted localization. -/
theorem smoothed_apply (ρ' : 𝓢(E, ℂ)) (ρc : HasCompactSupport (ρ : E → ℂ))
    (ρ'c : HasCompactSupport (ρ' : E → ℂ)) (v : Core (E := E) V)
    (cont : Continuous (fun y => test m j (vf y) (coreLift m.qa v))) (x : E) :
    (SchwartzAmbientBlocks.cutoffConvolution cut ρ' cutCompact ρ'c
        (fun y => test m j (vf y) (coreLift m.qa v)) cont).val x =
      cut x * ∫ y, (∫ s, ρ s * ρ' (y + s)) * (weighted m j cut wt wtOne v).val (x - y) := by
  rw [SchwartzAmbientBlocks.cutoffConvolution_apply]
  congr 1
  simp_rw [coefficient_apply m j cut wt wtOne hbt hbt1 localBound ρ vf hvf v]
  have Gcs : HasCompactSupport ((weighted m j cut wt wtOne v).val : E → ℂ) :=
    (cutCompact).mono' ((subset_tsupport _).trans (closure_minimal (fun z hz => by
      by_contra out; exact hz ((weighted m j cut wt wtOne v).property z out)) (isClosed_tsupport _)))
  exact SchwartzAmbientBlocks.double_convolution _ ρ ρ' (weighted m j cut wt wtOne v).val.continuous
    Gcs ρ.continuous ρc ρ'.continuous ρ'c x

end Coefficient

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
