module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceCharts
public import LeanShared.Analysis.ChartTraceFamily
public import LeanShared.Analysis.DenseUniformConvergence
meta import Lean.LibrarySuggestions.Basic

/-! The regularized trace family of the strong space. Chart `k` contributes the tests
`ψ_{k,y} = test(wt_k · ρ(· - y))` and the vectors `P(L(bump_{k,y}))`, where `P` is a fixed
bounded operator. On core functions the smoothing is `P L` of the chart sum of
`cut_k · (κ ⋆ G_k(v))`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTraceFamily"

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
  (tc : TraceCharts m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
  (ρ : 𝓢(E, ℂ)) (ρc : HasCompactSupport (ρ : E → ℂ))

/-- The chart indices as `Fin`. -/
abbrev chartEquiv : Fin (Fintype.card m.localization.indices) ≃ m.localization.indices :=
  (Fintype.equivFin _).symm

include hbt hbt1 ρc in
theorem testFamily_spec (j : m.localization.indices) :
    ∃ v : E → BoundedHolderSpace.graph E bt,
      (∀ y z, BoundedHolderSpace.physical E bt (v y) z = tc.wt j z * ρ (z - y)) ∧
      ∃ K : ℝ, ∀ y y', ‖v y - v y'‖ ≤ K * dist y y' :=
  TranslatedHolderTests.translated_family ((tc.wt j).smooth ⊤) (tc.wtCompact j) (ρ.smooth ⊤) ρc
    hbt hbt1

/-- The Hölder test family of chart `j`. -/
def testFamily (j : m.localization.indices) : E → BoundedHolderSpace.graph E bt :=
  (testFamily_spec m tc hbt hbt1 ρ ρc j).choose

theorem testFamily_apply (j : m.localization.indices) (y z : E) :
    BoundedHolderSpace.physical E bt (testFamily m tc hbt hbt1 ρ ρc j y) z = tc.wt j z * ρ (z - y) :=
  (testFamily_spec m tc hbt hbt1 ρ ρc j).choose_spec.1 y z

theorem testFamily_lipschitz (j : m.localization.indices) :
    ∃ K : ℝ, ∀ y y', ‖testFamily m tc hbt hbt1 ρ ρc j y - testFamily m tc hbt hbt1 ρ ρc j y'‖ ≤
      K * dist y y' :=
  (testFamily_spec m tc hbt hbt1 ρ ρc j).choose_spec.2

section Vectors
variable (lc : LocalCalculus m) (localBound : LocalPairing m bt) {L : ℝ} (bound : AnalyticBound m L)
  (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
  (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
  (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
  (P : m.StrongSpace →L[ℂ] m.StrongSpace) (ρ' : 𝓢(E, ℂ)) (ρ'c : HasCompactSupport (ρ' : E → ℂ))

/-- The vectors of chart `j`. -/
def vectorFamily (j : m.localization.indices) (y : E) : m.StrongSpace :=
  P (m.generator a (coreLift m.qa (bumpCore m j (tc.cut j) (tc.cutCompact j) (tc.cutSupport j)
    (tc.cutRegion j) ρ' y)))

include lc bound hs hR estimate b ρ'c in
theorem vector_continuous (j : m.localization.indices) :
    Continuous (vectorFamily m tc a P ρ' j) :=
  P.continuous.comp (generator_continuous m j (tc.cut j) (tc.cutCompact j) (tc.cutSupport j)
    (tc.cutRegion j) ρ' lc bound a strong remainder hs hR estimate b ρ'c)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem clm_lin_zero {C X : Type*} [AddCommGroup C] [Module ℂ C] [NormedAddCommGroup X]
    [NormedSpace ℂ X] (P : X →L[ℂ] X) (G : C →ₗ[ℂ] X) (c : C) (h : c = 0) : P (G c) = 0 := by
  rw [h, map_zero, map_zero]

include ρ'c in
theorem vector_compact (j : m.localization.indices) :
    HasCompactSupport (vectorFamily m tc a P ρ' j) :=
  HasCompactSupport.intro ((tc.cutCompact j).prod ρ'c |>.image (continuous_fst.sub continuous_snd))
    fun y hy => clm_lin_zero P ((m.generator a).toLinearMap.comp (coreLift m.qa)) _
      (bumpCore_zero m j (tc.cut j) (tc.cutCompact j) (tc.cutSupport j) (tc.cutRegion j) ρ' y hy)

include localBound in
theorem test_family_continuous (k : Fin (Fintype.card m.localization.indices)) :
    Continuous (fun y => test m (chartEquiv m k) (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k) y)) :=
  test_continuous m (chartEquiv m k) hbt hbt1 localBound _
    (testFamily_lipschitz m tc hbt hbt1 ρ ρc (chartEquiv m k)).choose
    (testFamily_lipschitz m tc hbt hbt1 ρ ρc (chartEquiv m k)).choose_spec

/-- The regularized trace family. -/
def family : RegularizedTraceFunctional.Family m.StrongSpace
    (Fin (Fintype.card m.localization.indices) × E) :=
  ChartTraceFamily.family volume
    (fun k y => test m (chartEquiv m k) (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k) y))
    (fun k y => vectorFamily m tc a P ρ' (chartEquiv m k) y)
    (test_family_continuous m tc hbt hbt1 ρ ρc localBound)
    (fun _ => vector_continuous m tc lc bound a strong remainder hs hR estimate b P ρ' ρ'c _)
    (fun k => ((test_family_continuous m tc hbt hbt1 ρ ρc localBound k).norm.mul
      (vector_continuous m tc lc bound a strong remainder hs hR estimate b P ρ' ρ'c _).norm
      ).integrable_of_hasCompactSupport (vector_compact m tc a P ρ' ρ'c _).norm.mul_left)

/-- The coefficient of a core function in chart `k`. -/
abbrev coefficient (k : Fin (Fintype.card m.localization.indices)) (v : Core (E := E) V) (y : E) : ℂ :=
  test m (chartEquiv m k) (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k) y) (coreLift m.qa v)

include localBound in
theorem coefficient_cont (k : Fin (Fintype.card m.localization.indices)) (v : Core (E := E) V) :
    Continuous (coefficient m tc hbt hbt1 ρ ρc k v) :=
  (test_family_continuous m tc hbt hbt1 ρ ρc localBound k).clm_apply continuous_const

include localBound in
theorem coefficient_compact' (k : Fin (Fintype.card m.localization.indices)) (v : Core (E := E) V) :
    HasCompactSupport (coefficient m tc hbt hbt1 ρ ρc k v) :=
  coefficient_compact m (chartEquiv m k) (tc.cut (chartEquiv m k)) (tc.wt (chartEquiv m k))
    (tc.wtOne (chartEquiv m k)) hbt hbt1 localBound ρ (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k))
    (testFamily_apply m tc hbt hbt1 ρ ρc (chartEquiv m k)) (tc.wtCompact (chartEquiv m k)) ρc v

/-- The smoothed chart piece `cut · (κ ⋆ G(v))`. -/
abbrev smoothed (k : Fin (Fintype.card m.localization.indices)) (v : Core (E := E) V) :
    supportedCore (tsupport (tc.cut (chartEquiv m k) : E → ℂ)) :=
  SchwartzAmbientBlocks.cutoffConvolution (tc.cut (chartEquiv m k)) ρ'
    (tc.cutCompact (chartEquiv m k)) ρ'c (coefficient m tc hbt hbt1 ρ ρc k v)
    (coefficient_cont m tc hbt hbt1 ρ ρc localBound k v)

include lc bound hs hR estimate b in
/-- The smoothing of chart `k` on a core function. -/
theorem chart_smoothing (k : Fin (Fintype.card m.localization.indices)) (v : Core (E := E) V) :
    ∫ y, coefficient m tc hbt hbt1 ρ ρc k v y • vectorFamily m tc a P ρ' (chartEquiv m k) y =
      P (m.generator a (coreLift m.qa (extension m (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.cutCompact (chartEquiv m k)) (tc.cutSupport (chartEquiv m k)) (tc.cutRegion (chartEquiv m k))
        (smoothed m tc hbt hbt1 ρ ρc localBound ρ' ρ'c k v)))) :=
  (CompletedCorePairing.integral_smul_comp volume P (coefficient m tc hbt hbt1 ρ ρc k v)
    (fun y => m.generator a (coreLift m.qa (bumpCore m (chartEquiv m k) (tc.cut (chartEquiv m k))
      (tc.cutCompact (chartEquiv m k)) (tc.cutSupport (chartEquiv m k))
      (tc.cutRegion (chartEquiv m k)) ρ' y)))
    (((coefficient_cont m tc hbt hbt1 ρ ρc localBound k v).smul
      (generator_continuous m (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.cutCompact (chartEquiv m k)) (tc.cutSupport (chartEquiv m k))
        (tc.cutRegion (chartEquiv m k)) ρ' lc bound a strong remainder hs hR estimate b ρ'c)
      ).integrable_of_hasCompactSupport
      (coefficient_compact' m tc hbt hbt1 ρ ρc localBound k v).smul_right)).trans
    (congrArg P (bump_integral m (chartEquiv m k) (tc.cut (chartEquiv m k))
      (tc.cutCompact (chartEquiv m k)) (tc.cutSupport (chartEquiv m k))
      (tc.cutRegion (chartEquiv m k)) ρ' lc hbt hbt1 localBound bound a strong remainder hs hR
      estimate b ρ'c _ (coefficient_cont m tc hbt hbt1 ρ ρc localBound k v)
      (coefficient_compact' m tc hbt hbt1 ρ ρc localBound k v)))

end Vectors

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
