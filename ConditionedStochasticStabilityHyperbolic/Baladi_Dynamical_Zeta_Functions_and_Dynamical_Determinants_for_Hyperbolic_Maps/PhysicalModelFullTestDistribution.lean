module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldLocalCompletion
public import LeanShared.Geometry.NativeFullHolderTests
public import LeanShared.Geometry.CompactSmoothHolderGraph
public import LeanShared.Geometry.ReferenceInverseDensityPairing
public import LeanShared.Analysis.CompactCompletedDistributionFaithful
public import LeanShared.Analysis.CompactSchwartzCutoff
meta import Lean.LibrarySuggestions.Basic

/-! The strong space of a physical model as distributions on the full native Hölder tests. The
literal reference-measure integral of a smooth core function against a full test of order `bt`
is bounded by the strong core norm (`global_pairing`), so it extends continuously to the strong
space. The extension is injective: the local low-order pairing gives every local completed
Schwartz pairing, which is faithful, and the reciprocal-density isolation tests recover each
local pairing from the global one. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelFullTestDistribution"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold Bundle
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelFullTestDistribution
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelFullTestPairing

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (d : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
  {bt : ℝ} (hbt1 : bt ≤ 1)

theorem view_continuous (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) :
    Continuous (NativeFullHolderTests.view bt hbt1 t) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact (SmoothHolderTestSpaces.physical bt
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) bt hbt1) univ t).continuous

theorem view_norm_le (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) (x : M) :
    ‖NativeFullHolderTests.view bt hbt1 t x‖ ≤ ‖t‖ := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact ((SmoothHolderTestSpaces.physical bt
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) bt hbt1) univ t).norm_coe_le_norm
      x).trans (SmoothHolderTestSpaces.physical_norm_le bt
        (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) bt hbt1) univ t)

theorem view_holder (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∀ x y, ‖NativeFullHolderTests.view bt hbt1 t x - NativeFullHolderTests.view bt hbt1 t y‖ ≤
      ‖t‖ * dist x y ^ bt := by
  intro _ x y
  exact BoundedHolderSpace.increment_bound M bt t.val x y

theorem integrable (f : Core (E := E) V) (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) :
    Integrable (fun x => SmoothSupportedManifoldCore.functions V f x *
      NativeFullHolderTests.view bt hbt1 t x) (d.measure volume) :=
  LocalizedReferencePairing.continuous_integrable
    ((SmoothSupportedManifoldCore.smooth V f).continuous.mul (view_continuous hbt1 t))

/-- The literal reference integral of a smooth core function against full tests. -/
def testFunctional (f : Core (E := E) V) :
    NativeFullHolderTests.Full (E := E) (M := M) bt hbt1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun t => ∫ x, SmoothSupportedManifoldCore.functions V f x *
        NativeFullHolderTests.view bt hbt1 t x ∂d.measure volume
      map_add' := fun s t => by
        rw [← integral_add (integrable d hbt1 f s) (integrable d hbt1 f t)]
        congr 1
        funext x
        rw [map_add, Pi.add_apply, mul_add]
      map_smul' := fun c t => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext x
        rw [map_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    (∫ x, ‖SmoothSupportedManifoldCore.functions V f x‖ ∂d.measure volume)
    (fun t => by
      change ‖∫ x, SmoothSupportedManifoldCore.functions V f x *
        NativeFullHolderTests.view bt hbt1 t x ∂d.measure volume‖ ≤ _
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_mul_const]
      apply integral_mono (integrable d hbt1 f t).norm
      · exact (LocalizedReferencePairing.continuous_integrable
          (SmoothSupportedManifoldCore.smooth V f).continuous).norm.mul_const _
      · intro x
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (view_norm_le hbt1 t x) (norm_nonneg _))

theorem testFunctional_apply (f : Core (E := E) V)
    (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) :
    testFunctional d hbt1 f t = ∫ x, SmoothSupportedManifoldCore.functions V f x *
      NativeFullHolderTests.view bt hbt1 t x ∂d.measure volume := rfl

/-- The core-to-functional map. -/
def coreTests : Core (E := E) V →ₗ[ℂ]
    (NativeFullHolderTests.Full (E := E) (M := M) bt hbt1 →L[ℂ] ℂ) where
  toFun f := testFunctional d hbt1 f
  map_add' f g := by
    ext t
    change testFunctional d hbt1 (f + g) t = testFunctional d hbt1 f t + testFunctional d hbt1 g t
    rw [testFunctional_apply, testFunctional_apply, testFunctional_apply, ← integral_add (integrable d hbt1 f t) (integrable d hbt1 g t)]
    congr 1
    funext x
    rw [map_add, Pi.add_apply, add_mul]
  map_smul' c f := by
    ext t
    change testFunctional d hbt1 (c • f) t = c • testFunctional d hbt1 f t
    rw [testFunctional_apply, testFunctional_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    ring

set_option maxHeartbeats 1600000 in
theorem coreTests_bound {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Core (E := E) V, ‖coreTests (V := V) d hbt1 f‖ ≤ C * ‖coreLift m.qa f‖ := by
  obtain ⟨C, hC, bound⟩ := global_pairing m d hbt hbt1 localBound
  refine ⟨C, hC, fun f => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro t
  have h := bound f (NativeFullHolderTests.view bt hbt1 t) ‖t‖ (norm_nonneg _)
    (view_continuous hbt1 t) (view_norm_le hbt1 t) (view_holder hbt1 t)
  change ‖testFunctional d hbt1 f t‖ ≤ _
  rw [testFunctional_apply]
  calc _ ≤ C * ‖t‖ * ‖coreLift m.qa f‖ := h
    _ = C * ‖coreLift m.qa f‖ * ‖t‖ := by ring

/-- The algebraic core pairing with full tests. -/
def corePairing : Core (E := E) V →ₗ[ℂ]
    (NativeFullHolderTests.Full (E := E) (M := M) bt hbt1 →ₗ[ℂ] ℂ) where
  toFun f := (coreTests d hbt1 f : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1 →ₗ[ℂ] ℂ)
  map_add' f g := by
    ext t
    change coreTests d hbt1 (f + g) t = coreTests d hbt1 f t + coreTests d hbt1 g t
    rw [map_add]
    rfl
  map_smul' c f := by
    ext t
    change coreTests d hbt1 (c • f) t = c • coreTests d hbt1 f t
    rw [map_smul]
    rfl

theorem corePairing_bounded {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
    (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) :
    ∃ C : ℝ, ∀ f : Core (E := E) V, ‖corePairing (V := V) d hbt1 f t‖ ≤ C * ‖m.qa f‖ := by
  obtain ⟨C, _, bound⟩ := coreTests_bound m d hbt hbt1 localBound
  refine ⟨C * ‖t‖, fun f => ?_⟩
  calc ‖corePairing d hbt1 f t‖ = ‖coreTests d hbt1 f t‖ := rfl
    _ ≤ ‖coreTests d hbt1 f‖ * ‖t‖ := (coreTests d hbt1 f).le_opNorm t
    _ ≤ C * ‖coreLift m.qa f‖ * ‖t‖ := mul_le_mul_of_nonneg_right (bound f) (norm_nonneg _)
    _ = C * ‖t‖ * ‖m.qa f‖ := by
      rw [show ‖coreLift m.qa f‖ = ‖m.qa f‖ from rfl]
      ring

set_option maxHeartbeats 1600000 in
theorem completed_bound {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt) :
    ∃ C : ℝ, ∀ (z : m.StrongSpace) (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1),
      ‖CompletedCorePairing.pairing m.qa (corePairing d hbt1)
        (corePairing_bounded m d hbt hbt1 localBound) z t‖ ≤ C * ‖z‖ * ‖t‖ := by
  obtain ⟨C, _, bound⟩ := coreTests_bound m d hbt hbt1 localBound
  refine ⟨C, fun z t => ?_⟩
  rw [CompletedCorePairing.pairing_apply]
  have estimate : ∀ f : Core (E := E) V, ‖corePairing d hbt1 f t‖ ≤ (C * ‖t‖) * ‖m.qa f‖ := by
    intro f
    calc ‖corePairing d hbt1 f t‖ = ‖coreTests d hbt1 f t‖ := rfl
      _ ≤ ‖coreTests d hbt1 f‖ * ‖t‖ := (coreTests d hbt1 f).le_opNorm t
      _ ≤ C * ‖coreLift m.qa f‖ * ‖t‖ := mul_le_mul_of_nonneg_right (bound f) (norm_nonneg _)
      _ = C * ‖t‖ * ‖m.qa f‖ := by
        rw [show ‖coreLift m.qa f‖ = ‖m.qa f‖ from rfl]
        ring
  calc ‖CompletedCorePairing.atTest m.qa (corePairing d hbt1) t z‖ ≤ (C * ‖t‖) * ‖z‖ :=
        CompletedCorePairing.bound m.qa (corePairing d hbt1) t (C * ‖t‖) estimate z
    _ = C * ‖z‖ * ‖t‖ := by ring

/-- The full-test distribution of the strong space. -/
def aFull {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt) :
    m.StrongSpace →L[ℂ] (NativeFullHolderTests.Full (E := E) (M := M) bt hbt1 →L[ℂ] ℂ) :=
  (CompletedCorePairing.pairing m.qa (corePairing d hbt1)
    (corePairing_bounded m d hbt hbt1 localBound)).mkContinuous₂
    (Classical.choose (completed_bound m d hbt hbt1 localBound))
    (Classical.choose_spec (completed_bound m d hbt hbt1 localBound))

theorem aFull_apply {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
    (z : m.StrongSpace) (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) :
    aFull m d hbt hbt1 localBound z t =
      CompletedCorePairing.atTest m.qa (corePairing d hbt1) t z := rfl

theorem aFull_core {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
    (f : Core (E := E) V) (t : NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) :
    aFull m d hbt hbt1 localBound (coreLift m.qa f) t = ∫ x, SmoothSupportedManifoldCore.functions V f x *
      NativeFullHolderTests.view bt hbt1 t x ∂d.measure volume := by
  rw [aFull_apply, CompletedCorePairing.core m.qa (corePairing d hbt1)
    (corePairing_bounded m d hbt hbt1 localBound) f t]
  rfl

/-- The local low-order pairing gives the completed local Schwartz pairing bound: a
cutoff equal to one on the local support turns a Schwartz test into a compactly
supported Hölder test. -/
theorem local_schwartz_bound {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
    (i : m.localization.indices) (φ : 𝓢(E, ℂ)) :
    ∃ C : ℝ, ∀ g, ‖SchwartzAmbientBlocks.pairing
      (ConstructedManifoldLocalization.support m.atlas m.localization i) g φ‖ ≤
        C * ‖m.localBlocks i g‖ := by
  obtain ⟨χ, χc, -, χone⟩ := CompactSchwartzCutoff.exists_cutoff
    (ConstructedManifoldLocalization.support_compact m.atlas m.localization i) isOpen_univ
    (subset_univ _)
  have smooth : ContDiff ℝ ∞ (fun x => χ x * φ x) := (χ.smooth ⊤).mul (φ.smooth ⊤)
  have compact : HasCompactSupport (fun x => χ x * φ x) := χc.mul_right
  obtain ⟨v, hv⟩ := CompactSmoothHolderGraph.exists_graph smooth compact hbt hbt1
  obtain ⟨Cl, _, pairing⟩ := localBound i (tsupport χ) χc
  refine ⟨Cl * ‖v‖, fun g => ?_⟩
  have supp : tsupport (BoundedHolderSpace.physical E bt v) ⊆ tsupport χ := by
    have h : (BoundedHolderSpace.physical E bt v : E → ℂ) = fun x => χ x * φ x := funext hv
    rw [h]
    exact tsupport_mul_subset_left
  have eq : SchwartzAmbientBlocks.pairing
      (ConstructedManifoldLocalization.support m.atlas m.localization i) g φ =
        ∫ x, g.val x * BoundedHolderSpace.physical E bt v x := by
    change ∫ x, g.val x * φ x = _
    congr 1
    funext x
    rw [hv x]
    by_cases hx : x ∈ ConstructedManifoldLocalization.support m.atlas m.localization i
    · rw [χone x hx, one_mul]
    · rw [g.property x hx, zero_mul, zero_mul]
  rw [eq]
  exact pairing g v supp

/-- The reciprocal-density isolation test of chart `i` and Schwartz test `φ`. -/
def isolationCore (i : m.localization.indices) (φ : 𝓢(E, ℂ)) :
    SmoothSupportedManifoldCore.core (E := E) (univ : Set M) :=
  ⟨d.isolationTest (m.atlas i) (m.atlas_mem i) (m.localization.cutoff i)
      (m.localization.smooth i) (m.localization.compact i) (m.localization.support i) φ,
    d.isolationTest_smooth _ _ _ _ _ _ _, subset_univ _⟩

set_option maxHeartbeats 1600000 in
theorem isolation_evaluation {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
    (i : m.localization.indices) (φ : 𝓢(E, ℂ)) (z : m.StrongSpace) :
    CompletedCorePairing.atTest m.qa (corePairing d hbt1)
      (NativeFullHolderTests.core bt hbt1 (isolationCore m d i φ)) z =
    CompletedCorePairing.atTest (m.localBlocks i) (SchwartzAmbientBlocks.pairing
      (ConstructedManifoldLocalization.support m.atlas m.localization i)) φ (m.localCompletion i z) := by
  refine (coreLift_dense m.qa).induction_on z
    (isClosed_eq (CompletedCorePairing.atTest _ _ _).continuous
      ((CompletedCorePairing.atTest _ _ φ).continuous.comp (m.localCompletion i).continuous)) ?_
  intro c
  rw [CompletedCorePairing.core m.qa (corePairing d hbt1) (corePairing_bounded m d hbt hbt1 localBound) c,
    m.localCompletion_core i c, CompletedCorePairing.core (m.localBlocks i)
      (SchwartzAmbientBlocks.pairing _) (local_schwartz_bound m hbt hbt1 localBound i) _ φ]
  exact FiniteSmoothReferenceCharts.Data.isolation_pairing d volume (m.atlas i) (m.atlas_mem i)
    (m.localization.cutoff i) (m.localization.smooth i) (m.localization.compact i)
    (m.localization.support i) φ (SmoothSupportedManifoldCore.functions V c)
    (SmoothSupportedManifoldCore.smooth V c).continuous

set_option maxHeartbeats 1600000 in
/-- The full-test distribution is faithful. -/
theorem aFull_injective {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt) :
    Function.Injective (aFull m d hbt hbt1 localBound) := by
  intro z w equal
  apply m.localCompletion_jointly_injective
  intro i
  apply SchwartzAmbientBlocks.compact_completed_pairing_injective μ m.slope_nonnegative (m.leaves i)
    (ConstructedManifoldLocalization.support m.atlas m.localization i)
    (ConeDyadicSymbols.symbols (m.radial i) (m.angle i)) (m.exponent i) (m.boundedBlocks i)
    (local_schwartz_bound m hbt hbt1 localBound i)
    (ConstructedManifoldLocalization.support_compact m.atlas m.localization i)
  apply LinearMap.ext
  intro φ
  have left := isolation_evaluation m d hbt hbt1 localBound i φ z
  have right := isolation_evaluation m d hbt hbt1 localBound i φ w
  have middle := congrArg (fun L => L (NativeFullHolderTests.core bt hbt1 (isolationCore m d i φ))) equal
  exact left.symm.trans (middle.trans right)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelFullTestDistribution
