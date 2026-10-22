module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelBumpVectors
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelLocalHolderTest
meta import Lean.LibrarySuggestions.Basic

/-! Weighted integrals of bump vectors. For a continuous compactly supported coefficient
`a`, the Bochner integral of `a(y) · L(bump_y)` is one generator step of the zero
extension of `cut · (a ⋆ ρ)`. The chart lift is continuous on the local completion and the
local Bochner identification is faithful there. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelBumpIntegral"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace PhysicalModelFullTestPairing

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
  (cutRegion : (m.atlas j).symm '' tsupport (cut : E → ℂ) ⊆ V)
  (ρ : 𝓢(E, ℂ))

/-- The bump on the cutoff support. -/
def cutLocal (y : E) : supportedCore (tsupport (cut : E → ℂ)) :=
  ⟨(bumpLocal m j cut cutSupport ρ y).val, fun x hx => by
    rw [bumpLocal_apply, image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩

theorem cutLocal_apply (y x : E) : (cutLocal m j cut cutSupport ρ y).val x = cut x * ρ (x - y) :=
  bumpLocal_apply m j cut cutSupport ρ y x

theorem cutLocal_continuous (lc : LocalCalculus m) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (ρc : HasCompactSupport (ρ : E → ℂ)) :
    Continuous (fun y => coreLift (cutBlocks m j cut cutCompact lc)
      (cutLocal m j cut cutSupport ρ y)) :=
  have : ∀ c, SFinite ((m.leaves j c).measure μ) := lc.sfinite j
  Continuous.subtype_mk (BlockNormCalculus.cutoff_translate_continuous μ m.slope_nonnegative
    (m.leaves j) (ConeDyadicSymbols.symbols (m.radial j) (m.angle j)) (m.exponent j)
    (lc.translate j) (lc.bounded j) cut (fun K hK => lc.multiplier j cut K hK) b ρ ρc
    (lc.bounded j _ cutCompact) (cutLocal m j cut cutSupport ρ)
    (cutLocal_apply m j cut cutSupport ρ)) _

include cutSupport in
theorem cut_pairBound (lc : LocalCalculus m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (localBound : LocalPairing m bt) :
    ∀ φ, ∃ C : ℝ, ∀ f, ‖SchwartzAmbientBlocks.pairing (tsupport (cut : E → ℂ)) f φ‖ ≤
      C * ‖cutBlocks m j cut cutCompact lc f‖ := fun φ =>
  let h := PhysicalModelLocalHolderTest.schwartz_bound m hbt hbt1 localBound j φ
  ⟨h.choose, fun f => (h.choose_spec (inclusion m j cut cutSupport f)).trans_eq
    (congrArg _ (cutBlocks_norm m j cut cutCompact cutSupport lc f))⟩

set_option maxHeartbeats 1600000 in
theorem cutLocal_identification (lc : LocalCalculus m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (localBound : LocalPairing m bt) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ρc : HasCompactSupport (ρ : E → ℂ))
    (coef : E → ℂ) (cont : Continuous coef) (compact : HasCompactSupport coef) :
    ∫ y, coef y • coreLift (cutBlocks m j cut cutCompact lc) (cutLocal m j cut cutSupport ρ y) =
      coreLift (cutBlocks m j cut cutCompact lc)
        (SchwartzAmbientBlocks.cutoffConvolution cut ρ cutCompact ρc coef cont) := by
  obtain ⟨Bc, hBc⟩ := LeafCommutator.exists_bound cut
  obtain ⟨Bρ, hBρ⟩ := LeafCommutator.exists_bound ρ
  exact SchwartzAmbientBlocks.integral_coreLift μ m.slope_nonnegative (m.leaves j)
    (tsupport (cut : E → ℂ)) (ConeDyadicSymbols.symbols (m.radial j) (m.angle j)) (m.exponent j)
    (lc.bounded j _ cutCompact) (cut_pairBound m j cut cutCompact cutSupport lc hbt hbt1 localBound)
    cutCompact coef cont (cont.integrable_of_hasCompactSupport compact)
    (cutLocal m j cut cutSupport ρ)
    (((cut.continuous.comp continuous_snd).mul
      (ρ.continuous.comp (continuous_snd.sub continuous_fst))).congr fun p =>
        (cutLocal_apply m j cut cutSupport ρ p.1 p.2).symm)
    (Bc * Bρ) (fun y x => by
      rw [cutLocal_apply, norm_mul]
      exact mul_le_mul (hBc x) (hBρ _) (norm_nonneg _) ((norm_nonneg _).trans (hBc x)))
    ((cont.smul (cutLocal_continuous m j cut cutCompact cutSupport ρ lc b ρc)).integrable_of_hasCompactSupport
      compact.smul_right)
    (SchwartzAmbientBlocks.cutoffConvolution cut ρ cutCompact ρc coef cont) (fun x => by
      rw [SchwartzAmbientBlocks.cutoffConvolution_apply, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [cutLocal_apply]
      ring)

/-- Weighted integrals of bump vectors. -/
theorem bump_integral (lc : LocalCalculus m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (localBound : LocalPairing m bt) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (ρc : HasCompactSupport (ρ : E → ℂ))
    (coef : E → ℂ) (cont : Continuous coef) (compact : HasCompactSupport coef) :
    ∫ y, coef y • m.generator a (coreLift m.qa (bumpCore m j cut cutCompact cutSupport cutRegion ρ y)) =
      m.generator a (coreLift m.qa (extension m j cut cutCompact cutSupport cutRegion
        (SchwartzAmbientBlocks.cutoffConvolution cut ρ cutCompact ρc coef cont))) :=
  (CompletedCorePairing.integral_lift volume (chartLift m j cut cutCompact cutSupport cutRegion lc a)
    coef (fun y => coreLift (cutBlocks m j cut cutCompact lc) (cutLocal m j cut cutSupport ρ y))
    ((cont.smul (cutLocal_continuous m j cut cutCompact cutSupport ρ lc b ρc)).integrable_of_hasCompactSupport
      compact.smul_right) _
    (fun y => chartLift_core m j cut cutCompact cutSupport cutRegion lc bound a strong remainder hs
      hR estimate (cutLocal m j cut cutSupport ρ y)) _
    (cutLocal_identification m j cut cutCompact cutSupport ρ lc hbt hbt1 localBound b ρc coef cont
      compact)).trans
    (chartLift_core m j cut cutCompact cutSupport cutRegion lc bound a strong remainder hs hR
      estimate _)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
