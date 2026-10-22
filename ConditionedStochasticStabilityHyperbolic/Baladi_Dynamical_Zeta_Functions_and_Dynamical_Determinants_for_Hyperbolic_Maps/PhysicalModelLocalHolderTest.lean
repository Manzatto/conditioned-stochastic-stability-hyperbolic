module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestPairing
public import LeanShared.Analysis.CompletedCorePairingBounds
public import LeanShared.Analysis.CompletedCorePairingLinear
public import LeanShared.Geometry.ChartFunctionPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModelCore
public import LeanShared.Geometry.BoundedHolderMultiplication
public import LeanShared.Geometry.CompactSmoothHolderGraph
meta import Lean.LibrarySuggestions.Basic

/-! Chart-local Hölder test functionals on the strong space. The Euclidean pairing of the
chart-`j` localization of a core function with a Hölder test `v` extends to a bounded
functional `ψ_v` on the completed strong space, linear and Lipschitz in `v`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelLocalHolderTest"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelLocalHolderTest
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelFullTestPairing

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
  {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)

include hbt hbt1 in
/-- The local pairing with any Hölder test, after a cutoff equal to one on the support. -/
theorem local_holder_bound (localBound : LocalPairing m bt) (j : m.localization.indices) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support m.atlas m.localization j))
      (v : BoundedHolderSpace.graph E bt),
      ‖∫ z, g.val z * BoundedHolderSpace.physical E bt v z‖ ≤ C * ‖v‖ * ‖m.localBlocks j g‖ := by
  obtain ⟨χ, χc, -, χone⟩ := CompactSchwartzCutoff.exists_cutoff
    (ConstructedManifoldLocalization.support_compact m.atlas m.localization j) isOpen_univ
    (subset_univ _)
  obtain ⟨a, ha⟩ := CompactSmoothHolderGraph.exists_graph (χ.smooth ⊤) χc hbt hbt1
  obtain ⟨Cl, Cl0, pairing⟩ := localBound j (tsupport χ) χc
  refine ⟨Cl * (2 * ‖a‖), by positivity, fun g v => ?_⟩
  set av := BoundedHolderSpace.product bt a v
  have physicalA : (BoundedHolderSpace.physical E bt a : E → ℂ) = χ := funext ha
  have supp : tsupport (BoundedHolderSpace.physical E bt av) ⊆ tsupport χ := by
    have h : (BoundedHolderSpace.physical E bt av : E → ℂ) =
        fun z => χ z * BoundedHolderSpace.physical E bt v z := by
      funext z
      rw [BoundedHolderSpace.physical_product, BoundedContinuousFunction.mul_apply, ha]
    rw [h]
    exact tsupport_mul_subset_left
  have same : (∫ z, g.val z * BoundedHolderSpace.physical E bt v z) =
      ∫ z, g.val z * BoundedHolderSpace.physical E bt av z := by
    congr 1
    funext z
    rw [BoundedHolderSpace.physical_product, BoundedContinuousFunction.mul_apply, ha]
    by_cases hz : z ∈ ConstructedManifoldLocalization.support m.atlas m.localization j
    · rw [χone z hz, one_mul]
    · rw [g.property z hz, zero_mul, zero_mul]
  rw [same]
  calc ‖∫ z, g.val z * BoundedHolderSpace.physical E bt av z‖
      ≤ Cl * ‖av‖ * ‖m.localBlocks j g‖ := pairing g av supp
    _ ≤ Cl * ((2 * ‖a‖) * ‖v‖) * ‖m.localBlocks j g‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (BoundedHolderSpace.product_norm_le bt a v) Cl0) (norm_nonneg _)
    _ = Cl * (2 * ‖a‖) * ‖v‖ * ‖m.localBlocks j g‖ := by ring

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem pairing_integrable {D : Set E} (g : SchwartzJetSpace.supportedCore D)
    (v : BoundedHolderSpace.graph E bt) :
    Integrable (fun z => g.val z * BoundedHolderSpace.physical E bt v z) :=
  g.val.integrable.mul_bdd (c := ‖BoundedHolderSpace.physical E bt v‖)
    (BoundedHolderSpace.physical E bt v).continuous.aestronglyMeasurable
    (ae_of_all _ fun z => (BoundedHolderSpace.physical E bt v).norm_coe_le_norm z)

/-- The chart-`j` Euclidean pairing of localized core functions with Hölder tests. -/
def corePairing (j : m.localization.indices) :
    Core (E := E) V →ₗ[ℂ] (BoundedHolderSpace.graph E bt →ₗ[ℂ] ℂ) :=
  LinearMap.mk₂ ℂ (fun c v => ∫ z, (ConstructedManifoldLocalization.localize m.atlas m.localization
      m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      j c).val z * BoundedHolderSpace.physical E bt v z)
    (fun c d v => by
      rw [map_add, ← integral_add (pairing_integrable _ v) (pairing_integrable _ v)]
      congr 1
      funext z
      rw [Submodule.coe_add, add_apply, add_mul])
    (fun a c v => by
      rw [map_smul, smul_eq_mul, ← integral_const_mul]
      congr 1
      funext z
      rw [Submodule.coe_smul, smul_apply, smul_eq_mul, mul_assoc])
    (fun c v w => by
      rw [← integral_add (pairing_integrable _ v) (pairing_integrable _ w)]
      congr 1
      funext z
      rw [map_add, BoundedContinuousFunction.add_apply, mul_add])
    (fun a c v => by
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext z
      rw [map_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]
      ring)

theorem corePairing_apply (j : m.localization.indices) (c : Core (E := E) V)
    (v : BoundedHolderSpace.graph E bt) :
    corePairing m j c v = ∫ z, (ConstructedManifoldLocalization.localize m.atlas m.localization
      m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      j c).val z * BoundedHolderSpace.physical E bt v z := rfl

include hbt hbt1 in
theorem corePairing_estimate (localBound : LocalPairing m bt) (j : m.localization.indices) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : BoundedHolderSpace.graph E bt) (c : Core (E := E) V),
      ‖corePairing m j c v‖ ≤ (C * ‖v‖) * ‖m.qa c‖ := by
  obtain ⟨C, C0, bound⟩ := local_holder_bound m hbt hbt1 localBound j
  refine ⟨C, C0, fun v c => ?_⟩
  rw [corePairing_apply]
  refine (bound _ v).trans ?_
  exact mul_le_mul_of_nonneg_left (local_le_core m c j) (by positivity)

include hbt hbt1 in
theorem corePairing_bounded (localBound : LocalPairing m bt) (j : m.localization.indices) :
    ∀ v : BoundedHolderSpace.graph E bt, ∃ C : ℝ, ∀ c : Core (E := E) V,
      ‖corePairing m j c v‖ ≤ C * ‖m.qa c‖ := fun v =>
  ⟨_, (corePairing_estimate m hbt hbt1 localBound j).choose_spec.2 v⟩

/-- The completed chart-local Hölder test functional. -/
def test (j : m.localization.indices) (v : BoundedHolderSpace.graph E bt) :
    m.StrongSpace →L[ℂ] ℂ :=
  CompletedCorePairing.atTest m.qa (corePairing m j) v

include hbt hbt1 in
theorem test_core (localBound : LocalPairing m bt) (j : m.localization.indices)
    (v : BoundedHolderSpace.graph E bt) (c : Core (E := E) V) :
    test m j v (coreLift m.qa c) = corePairing m j c v :=
  CompletedCorePairing.core m.qa (corePairing m j) (corePairing_bounded m hbt hbt1 localBound j) c v

include hbt hbt1 in
theorem test_sub (localBound : LocalPairing m bt) (j : m.localization.indices)
    (v w : BoundedHolderSpace.graph E bt) :
    test m j (v - w) = test m j v - test m j w :=
  CompletedCorePairing.atTest_sub m.qa (corePairing m j)
    (corePairing_bounded m hbt hbt1 localBound j) v w

include hbt hbt1 in
theorem test_norm (localBound : LocalPairing m bt) (j : m.localization.indices) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : BoundedHolderSpace.graph E bt, ‖test m j v‖ ≤ C * ‖v‖ :=
  let h := corePairing_estimate m hbt hbt1 localBound j
  ⟨h.choose, h.choose_spec.1, fun v => CompletedCorePairing.atTest_norm_le m.qa (corePairing m j) v
    (h.choose * ‖v‖) (mul_nonneg h.choose_spec.1 (norm_nonneg v)) (h.choose_spec.2 v)⟩

/-- The chart-`j` pairing functional on bounded continuous functions. -/
def chartPairing (j : m.localization.indices) (v : BoundedHolderSpace.graph E bt) :
    (M →ᵇ ℂ) →L[ℂ] ℂ :=
  ChartFunctionPairing.pairing (m.atlas j) (m.localization.cutoff j) (m.localization.support j)
    (m.localization.compact j) (m.localization.smooth j).continuous volume
    (BoundedHolderSpace.physical E bt v)

include hbt hbt1 in
/-- On realized regular inputs the test functional is the literal chart pairing. -/
theorem test_realize (localBound : LocalPairing m bt) (j : m.localization.indices)
    (v : BoundedHolderSpace.graph E bt) (physReg : Reg →L[ℂ] (M →ᵇ ℂ))
    (hphys : ∀ r x, physReg r x = m.view r x) (r : Reg) :
    test m j v (m.realize r) = chartPairing m j v (physReg r) :=
  CompletedCorePairing.atTest_eq_of_dense m.qa (corePairing m j)
    (corePairing_bounded m hbt hbt1 localBound j) m.realize m.regularCore m.regularCore_dense
    m.realize_core v ((chartPairing m j v).comp physReg) (fun c => by
      show chartPairing m j v (physReg (m.regularCore c)) = _
      rw [chartPairing, ChartFunctionPairing.pairing_apply, corePairing_apply]
      congr 1
      funext z
      have hv : (⇑(physReg (m.regularCore c)) : M → ℂ) = SmoothSupportedManifoldCore.functions V c := by
        funext x; rw [hphys, m.view_core]
      rw [hv]
      rfl) r

include hbt hbt1 in
/-- The local Schwartz pairing bound, through a cutoff equal to one on the chart support. -/
theorem schwartz_bound (localBound : LocalPairing m bt) (j : m.localization.indices)
    (φ : 𝓢(E, ℂ)) :
    ∃ C : ℝ, ∀ g, ‖SchwartzAmbientBlocks.pairing
      (ConstructedManifoldLocalization.support m.atlas m.localization j) g φ‖ ≤
        C * ‖m.localBlocks j g‖ := by
  obtain ⟨χ, χc, -, χone⟩ := CompactSchwartzCutoff.exists_cutoff
    (ConstructedManifoldLocalization.support_compact m.atlas m.localization j) isOpen_univ
    (subset_univ _)
  have smooth : ContDiff ℝ ∞ (fun x => χ x * φ x) := (χ.smooth ⊤).mul (φ.smooth ⊤)
  have compact : HasCompactSupport (fun x => χ x * φ x) := χc.mul_right
  obtain ⟨v, hv⟩ := CompactSmoothHolderGraph.exists_graph smooth compact hbt hbt1
  obtain ⟨C, C0, bound⟩ := local_holder_bound m hbt hbt1 localBound j
  refine ⟨C * ‖v‖, fun g => ?_⟩
  have eq : SchwartzAmbientBlocks.pairing
      (ConstructedManifoldLocalization.support m.atlas m.localization j) g φ =
        ∫ x, g.val x * BoundedHolderSpace.physical E bt v x := by
    change ∫ x, g.val x * φ x = _
    congr 1
    funext x
    rw [hv x]
    by_cases hx : x ∈ ConstructedManifoldLocalization.support m.atlas m.localization j
    · rw [χone x hx, one_mul]
    · rw [g.property x hx, zero_mul, zero_mul]
  rw [eq]
  exact bound g v

end ConditionedStochasticStabilityHyperbolic.PhysicalModelLocalHolderTest
