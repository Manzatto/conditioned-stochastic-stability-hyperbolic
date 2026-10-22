module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelSingleChart
public import LeanShared.Analysis.BlockNormCalculus
public import LeanShared.Geometry.SupportedChartExtension
public import LeanShared.Geometry.SupportedChartExtensionCore
public import LeanShared.Analysis.LocalBochnerIdentification
meta import Lean.LibrarySuggestions.Basic

/-! Bump vectors of the regularized trace. In a fixed chart `j`, the zero extensions of
`A · ρ(· - y)` are smooth supported core functions; one generator step maps them to strong
vectors depending continuously on `y`, by the single-chart pair estimate and the block
norm calculus of the chart (translation-closed leaves, bounded blocks on every compact set,
smooth multipliers). -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelBumpVectors"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace

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

/-- The block norm calculus of the local chart norms. -/
structure LocalCalculus : Prop where
  sfinite : ∀ j c, SFinite ((m.leaves j c).measure μ)
  translate : ∀ j c (z : E), ∃ c', ((m.leaves j c).measure μ).map (fun x => x + z) =
    (m.leaves j c').measure μ
  bounded : ∀ j (K : Set E), IsCompact K → SchwartzAmbientBlocks.SmoothCoreBounded μ
    m.slope_nonnegative (m.leaves j) K (ConeDyadicSymbols.symbols (m.radial j) (m.angle j))
    (m.exponent j)
  multiplier : ∀ j (a : 𝓢(E, ℂ)) (K : Set E) (hK : IsCompact K), ∃ C : ℝ,
    ∀ f g : supportedCore K, g.val = LeafCommutator.mul a f.val →
      ‖SchwartzAmbientBlocks.coreMap μ m.slope_nonnegative (m.leaves j) K
        (ConeDyadicSymbols.symbols (m.radial j) (m.angle j)) (m.exponent j) (bounded j K hK) g‖ ≤
      C * ‖SchwartzAmbientBlocks.coreMap μ m.slope_nonnegative (m.leaves j) K
        (ConeDyadicSymbols.symbols (m.radial j) (m.angle j)) (m.exponent j) (bounded j K hK) f‖

variable (j : m.localization.indices) (cut : 𝓢(E, ℂ))
  (cutCompact : HasCompactSupport (cut : E → ℂ))
  (cutSupport : tsupport (cut : E → ℂ) ⊆
    ConstructedManifoldLocalization.support m.atlas m.localization j)
  (cutRegion : (m.atlas j).symm '' tsupport (cut : E → ℂ) ⊆ V)
  (ρ : 𝓢(E, ℂ))

/-- The local bump `cut · ρ(· - y)` in chart `j`. -/
def bumpLocal (y : E) : supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization j) :=
  ⟨LeafCommutator.mul cut (SchwartzMap.compSubConstCLM ℝ y ρ), fun x hx => by
    rw [LeafCommutator.mul_apply, image_eq_zero_of_notMem_tsupport (fun h => hx (cutSupport h)),
      zero_mul]⟩

theorem bumpLocal_apply (y x : E) :
    (bumpLocal m j cut cutSupport ρ y).val x = cut x * ρ (x - y) := by
  change LeafCommutator.mul cut (SchwartzMap.compSubConstCLM ℝ y ρ) x = _
  rw [LeafCommutator.mul_apply, SchwartzMap.compSubConstCLM_apply]

include cutCompact in
theorem bumpLocal_tsupport (y : E) :
    tsupport ((bumpLocal m j cut cutSupport ρ y).val : E → ℂ) ⊆ tsupport (cut : E → ℂ) := by
  have h : ((bumpLocal m j cut cutSupport ρ y).val : E → ℂ) = fun x => cut x * ρ (x - y) :=
    funext (bumpLocal_apply m j cut cutSupport ρ y)
  rw [h]
  exact tsupport_mul_subset_left

include cutCompact cutRegion in
/-- The zero extension of the local bump, as a smooth supported core function. -/
def bumpCore (y : E) : Core (E := E) V :=
  ⟨SupportedChartExtension.function (m.atlas j) (bumpLocal m j cut cutSupport ρ y).val,
    SupportedChartExtension.smooth (m.atlas j) (m.atlas_mem j)
      ((bumpLocal m j cut cutSupport ρ y).val.smooth ⊤)
      (cutCompact.mono' ((subset_tsupport _).trans (bumpLocal_tsupport m j cut cutCompact cutSupport ρ y)))
      ((bumpLocal_tsupport m j cut cutCompact cutSupport ρ y).trans (cutSupport.trans
        (ChartLocalization.localSupport_subset_target _ _ (m.localization.support j)))),
    (SupportedChartExtension.support_subset (m.atlas j)
      (cutCompact.mono' ((subset_tsupport _).trans (bumpLocal_tsupport m j cut cutCompact cutSupport ρ y)))
      ((bumpLocal_tsupport m j cut cutCompact cutSupport ρ y).trans (cutSupport.trans
        (ChartLocalization.localSupport_subset_target _ _ (m.localization.support j))))).trans
      ((image_mono (bumpLocal_tsupport m j cut cutCompact cutSupport ρ y)).trans cutRegion)⟩

theorem bumpCore_apply (y : E) (x : M) :
    SmoothSupportedManifoldCore.functions V (bumpCore m j cut cutCompact cutSupport cutRegion ρ y) x =
      if x ∈ (m.atlas j).source then (bumpLocal m j cut cutSupport ρ y).val (m.atlas j x) else 0 :=
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem continuous_of_dist_le {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] (f : α → β) (g : α → γ) (K : ℝ)
    (h : ∀ x y, dist (f x) (f y) ≤ K * dist (g x) (g y)) (hg : Continuous g) : Continuous f := by
  rw [Metric.continuous_iff] at hg ⊢
  intro x ε hε
  obtain ⟨δ, hδ, close⟩ := hg x (ε / (|K| + 1)) (by positivity)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have near := close y hy
  calc dist (f y) (f x) ≤ K * dist (g y) (g x) := h y x
    _ ≤ |K| * dist (g y) (g x) := mul_le_mul_of_nonneg_right (le_abs_self K) dist_nonneg
    _ ≤ |K| * (ε / (|K| + 1)) := mul_le_mul_of_nonneg_left near.le (abs_nonneg K)
    _ < ε := by
        have pos : 0 < |K| + 1 := by positivity
        rw [mul_div_assoc', div_lt_iff₀ pos]
        nlinarith [abs_nonneg K]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- A linear map controlled through a subtractive relation by a continuous local family is
continuous along the family. -/
theorem continuous_of_single {Y C X L B : Type*} [PseudoMetricSpace Y]
    [AddCommGroup C] [Module ℂ C] [SeminormedAddCommGroup X] [NormedSpace ℂ X]
    [AddCommGroup L] [Module ℂ L] [SeminormedAddCommGroup B] [NormedSpace ℂ B]
    (G : C →ₗ[ℂ] X) (lb : L →ₗ[ℂ] B) (rel : C → L → Prop)
    (relSub : ∀ c c' f f', rel c f → rel c' f' → rel (c - c') (f - f')) (K : ℝ)
    (single : ∀ c f, rel c f → ‖G c‖ ≤ K * ‖lb f‖) (c : Y → C) (f : Y → L)
    (hrel : ∀ y, rel (c y) (f y)) (hcont : Continuous (fun y => lb (f y))) :
    Continuous (fun y => G (c y)) :=
  continuous_of_dist_le _ _ K (fun y y' => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub]
    exact single _ _ (relSub _ _ _ _ (hrel y) (hrel y'))) hcont

/-- The single-chart relation between core functions and local functions. -/
def SingleChart (c : Core (E := E) V)
    (f : supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization j)) : Prop :=
  ∀ x, SmoothSupportedManifoldCore.functions V c x =
    if x ∈ (m.atlas j).source then f.val (m.atlas j x) else 0

theorem singleChart_sub (c c' : Core (E := E) V)
    (f f' : supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization j))
    (h : SingleChart m j c f) (h' : SingleChart m j c' f') : SingleChart m j (c - c') (f - f') := by
  intro x
  rw [map_sub, Pi.sub_apply, h, h']
  split_ifs <;> simp

/-- One generator step of the bumps depends continuously on the translation. -/
theorem generator_continuous (lc : LocalCalculus m) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (hρ : HasCompactSupport (ρ : E → ℂ)) :
    Continuous (fun y => m.generator a
      (coreLift m.qa (bumpCore m j cut cutCompact cutSupport cutRegion ρ y))) :=
  have : ∀ c, SFinite ((m.leaves j c).measure μ) := lc.sfinite j
  continuous_of_single ((m.generator a).toLinearMap.comp (coreLift m.qa)) (m.localBlocks j)
    (SingleChart m j) (singleChart_sub m j) (strong + ∑ i, remainder i j)
    (fun c f h => PhysicalModelSingleChart.single_chart m bound a strong remainder hs hR estimate
      j f c h)
    (bumpCore m j cut cutCompact cutSupport cutRegion ρ) (bumpLocal m j cut cutSupport ρ)
    (fun _ _ => rfl)
    (BlockNormCalculus.cutoff_translate_continuous μ m.slope_nonnegative (m.leaves j)
      (ConeDyadicSymbols.symbols (m.radial j) (m.angle j)) (m.exponent j) (lc.translate j)
      (lc.bounded j) cut (fun K hK => lc.multiplier j cut K hK) b ρ hρ (m.boundedBlocks j)
      (bumpLocal m j cut cutSupport ρ) (bumpLocal_apply m j cut cutSupport ρ))

include cutSupport in
theorem cut_inside : tsupport (cut : E → ℂ) ⊆ (m.atlas j).target :=
  cutSupport.trans (ChartLocalization.localSupport_subset_target _ _ (m.localization.support j))

/-- Zero extension from the cutoff support into the core. -/
def extension : supportedCore (tsupport (cut : E → ℂ)) →ₗ[ℂ] Core (E := E) V :=
  SupportedChartExtension.coreMap (m.atlas j) (m.atlas_mem j) cutCompact
    (cut_inside m j cut cutSupport) cutRegion

/-- Inclusion of the cutoff support core into the chart support core. -/
def inclusion (f : supportedCore (tsupport (cut : E → ℂ))) :
    supportedCore (ConstructedManifoldLocalization.support m.atlas m.localization j) :=
  ⟨f.val, fun x hx => f.property x (fun h => hx (cutSupport h))⟩

/-- The local block map on the cutoff support. -/
abbrev cutBlocks (lc : LocalCalculus m) :=
  SchwartzAmbientBlocks.coreMap μ m.slope_nonnegative (m.leaves j) (tsupport (cut : E → ℂ))
    (ConeDyadicSymbols.symbols (m.radial j) (m.angle j)) (m.exponent j)
    (lc.bounded j _ cutCompact)

theorem cutBlocks_norm (lc : LocalCalculus m) (f : supportedCore (tsupport (cut : E → ℂ))) :
    ‖m.localBlocks j (inclusion m j cut cutSupport f)‖ = ‖cutBlocks m j cut cutCompact lc f‖ :=
  BlockNormCalculus.norm_congr μ m.slope_nonnegative (m.leaves j)
    (ConeDyadicSymbols.symbols (m.radial j) (m.angle j)) (m.exponent j) (m.boundedBlocks j)
    (lc.bounded j _ cutCompact) _ _ rfl

theorem chart_bound (lc : LocalCalculus m) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    (f : supportedCore (tsupport (cut : E → ℂ))) :
    ‖m.generator a (coreLift m.qa (extension m j cut cutCompact cutSupport cutRegion f))‖ ≤
      (strong + ∑ i, remainder i j) *
        ‖coreLift (cutBlocks m j cut cutCompact lc) f‖ :=
  (PhysicalModelSingleChart.single_chart m bound a strong remainder hs hR estimate j
    (inclusion m j cut cutSupport f) (extension m j cut cutCompact cutSupport cutRegion f)
    (fun _ => rfl)).trans_eq (congrArg _ (cutBlocks_norm m j cut cutCompact cutSupport lc f))

/-- The bounded chart lift from the local completion of the cutoff support. -/
def chartLift (lc : LocalCalculus m) (a : Ω) :
    closedCore (cutBlocks m j cut cutCompact lc) →L[ℂ] m.StrongSpace :=
  ((m.generator a).toLinearMap.comp ((coreLift m.qa).comp
    (extension m j cut cutCompact cutSupport cutRegion))).extendOfNorm
    (coreLift (cutBlocks m j cut cutCompact lc))

theorem chartLift_core (lc : LocalCalculus m) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    (f : supportedCore (tsupport (cut : E → ℂ))) :
    chartLift m j cut cutCompact cutSupport cutRegion lc a
      (coreLift (cutBlocks m j cut cutCompact lc) f) =
      m.generator a (coreLift m.qa (extension m j cut cutCompact cutSupport cutRegion f)) :=
  LinearMap.extendOfNorm_eq (coreLift_dense _)
    ⟨_, chart_bound m j cut cutCompact cutSupport cutRegion lc bound a strong remainder hs hR
      estimate⟩ f

theorem chartLift_norm (lc : LocalCalculus m) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    (z : closedCore (cutBlocks m j cut cutCompact lc)) :
    ‖chartLift m j cut cutCompact cutSupport cutRegion lc a z‖ ≤
      (strong + ∑ i, remainder i j) * ‖z‖ :=
  LinearMap.norm_extendOfNorm_apply_le (coreLift_dense _) _
    (chart_bound m j cut cutCompact cutSupport cutRegion lc bound a strong remainder hs hR
      estimate) z

include cutCompact cutRegion in
/-- Bumps vanish for translations far from the cutoff. -/
theorem bumpCore_zero (y : E)
    (far : y ∉ (fun p : E × E => p.1 - p.2) '' (tsupport (cut : E → ℂ) ×ˢ tsupport (ρ : E → ℂ))) :
    bumpCore m j cut cutCompact cutSupport cutRegion ρ y = 0 := by
  apply Subtype.ext
  funext x
  change (if x ∈ (m.atlas j).source then (bumpLocal m j cut cutSupport ρ y).val (m.atlas j x) else 0) = 0
  split_ifs
  · rw [bumpLocal_apply]
    by_cases hz : m.atlas j x ∈ tsupport (cut : E → ℂ)
    · have out : m.atlas j x - y ∉ tsupport (ρ : E → ℂ) := fun h =>
        far ⟨(m.atlas j x, m.atlas j x - y), ⟨hz, h⟩, sub_sub_cancel _ _⟩
      rw [image_eq_zero_of_notMem_tsupport out, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  · rfl

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
