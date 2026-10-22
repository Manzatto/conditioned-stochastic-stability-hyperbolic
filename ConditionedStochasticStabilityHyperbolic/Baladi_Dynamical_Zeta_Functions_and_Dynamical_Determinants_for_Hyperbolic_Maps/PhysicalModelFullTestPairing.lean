module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import LeanShared.Geometry.LocalizedReferencePairing
public import LeanShared.Geometry.BoundedHolderOfBoundNorm
public import LeanShared.Analysis.CompactSchwartzCutoff
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
meta import Lean.LibrarySuggestions.Basic

/-! Global low-order pairing: if every local block norm of a physical model controls the Euclidean
pairing with compactly supported Hölder tests of order `bt`, then the reference-measure pairing
of a smooth core function with a native Hölder function of order `bt` is bounded by the native
Hölder constant times the model's strong core norm. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelFullTestPairing"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold Bundle
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelFullTestPairing
open LeanShared DyadicCompletion PhysicalManifoldModel

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
  (bt : ℝ)

/-- The local low-order pairing property of a physical model. -/
def LocalPairing : Prop :=
  ∀ i (K : Set E), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (g : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support m.atlas m.localization i))
      (v : BoundedHolderSpace.graph E bt),
      tsupport (BoundedHolderSpace.physical E bt v) ⊆ K →
      ‖∫ x, g.val x * BoundedHolderSpace.physical E bt v x‖ ≤ C * ‖v‖ * ‖m.localBlocks i g‖

theorem local_le_core (f : Core (E := E) V) (i : m.localization.indices) :
    ‖m.localBlocks i (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i f)‖ ≤
      ‖coreLift m.qa f‖ := by
  rw [show ‖coreLift m.qa f‖ = ((Finset.univ.sup (fun i => ‖m.localBlocks i
      (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i f)‖₊) :
        ℝ≥0) : ℝ) from rfl]
  exact_mod_cast Finset.le_sup (f := fun i => ‖m.localBlocks i
    (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i f)‖₊)
    (Finset.mem_univ i)

section Global
variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  (d : FiniteSmoothReferenceCharts.Data (E := E) (M := M))

set_option maxHeartbeats 1600000 in
/-- The global low-order pairing bound against the strong core norm. -/
theorem global_pairing {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Core (E := E) V) (φ : M → ℂ) (A : ℝ), 0 ≤ A → Continuous φ →
      (∀ x, ‖φ x‖ ≤ A) →
      (let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
        ∀ x y, ‖φ x - φ y‖ ≤ A * dist x y ^ bt) →
      ‖∫ x, SmoothSupportedManifoldCore.functions V f x * φ x ∂d.measure volume‖ ≤
        C * A * ‖coreLift m.qa f‖ := by
  classical
  have cut := fun i : m.localization.indices => CompactSchwartzCutoff.exists_cutoff
    (ConstructedManifoldLocalization.support_compact m.atlas m.localization i)
    (m.atlas i).open_target
    (ChartLocalization.localSupport_subset_target (m.atlas i) (m.localization.cutoff i)
      (m.localization.support i))
  choose χ χcompact χinside χone using cut
  let w := fun i => LocalizedReferencePairing.weight m.atlas m.localization d χ i
  have perChart : ∀ i : m.localization.indices, ∃ H Z Cl : ℝ, 0 ≤ H ∧ 0 ≤ Z ∧ 0 ≤ Cl ∧
      (∀ y, ‖w i y‖ ≤ Z) ∧ Continuous (w i) ∧ tsupport (w i) ⊆ (m.atlas i).target ∧
      (∀ (φ : M → ℂ) (A : ℝ), 0 ≤ A → (∀ x, ‖φ x‖ ≤ A) →
        (let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
          ∀ x y, ‖φ x - φ y‖ ≤ A * dist x y ^ bt) →
        ∀ y z, ‖NativeChartTest.reading (m.atlas i) (w i) φ y -
          NativeChartTest.reading (m.atlas i) (w i) φ z‖ ≤ H * A * ‖y - z‖ ^ bt) ∧
      (∀ (g : SchwartzJetSpace.supportedCore
          (ConstructedManifoldLocalization.support m.atlas m.localization i))
        (v : BoundedHolderSpace.graph E bt),
        tsupport (BoundedHolderSpace.physical E bt v) ⊆ tsupport (w i) →
        ‖∫ x, g.val x * BoundedHolderSpace.physical E bt v x‖ ≤ Cl * ‖v‖ * ‖m.localBlocks i g‖) := by
    intro i
    have smooth : ContDiff ℝ ∞ (w i) :=
      d.chartTestDensity_smooth (m.atlas i) (m.atlas_mem i) (χ i) (χinside i)
    have supp : tsupport (w i) ⊆ tsupport (χ i) := tsupport_mul_subset_left
    have compact : HasCompactSupport (w i) :=
      IsCompact.of_isClosed_subset (χcompact i) (isClosed_tsupport _) supp
    have inside : tsupport (w i) ⊆ (m.atlas i).target := supp.trans (χinside i)
    obtain ⟨Λ, lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compact smooth (by simp)
    obtain ⟨H, hH, hol⟩ := NativeChartTest.reading_holder (m.atlas i) (w i) (m.atlas_mem i) inside
      compact lip hbt hbt1
    obtain ⟨Z, hZ⟩ := smooth.continuous.norm.bddAbove_range_of_hasCompactSupport compact.norm
    have hZy : ∀ y, ‖w i y‖ ≤ Z := fun y => hZ ⟨y, rfl⟩
    obtain ⟨Cl, hCl, pairing⟩ := localBound i (tsupport (w i)) compact
    exact ⟨H, Z, Cl, hH, (norm_nonneg _).trans (hZy 0), hCl, hZy, smooth.continuous, inside, hol,
      pairing⟩
  choose H Z Cl hH hZ hCl hZy hcont hinside hol pairing using perChart
  refine ⟨∑ i, Cl i * (Z i + H i), Finset.sum_nonneg fun i _ =>
    mul_nonneg (hCl i) (add_nonneg (hZ i) (hH i)), ?_⟩
  intro f φ A hA hφ bound holder
  have vanish : ∀ x, x ∉ S → SmoothSupportedManifoldCore.functions V f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (m.region_subset_support (f.property.2 h)))
  rw [LocalizedReferencePairing.integral_decomposition m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) d volume χ
    χone f vanish φ hφ]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  -- the chart test
  let r : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (NativeChartTest.reading (m.atlas i) (w i) φ)
    (NativeChartTest.reading_continuous (m.atlas i) (w i) (hinside i) (hcont i) φ hφ)
    (Z i * A) (NativeChartTest.reading_norm_le (m.atlas i) (w i) φ (hZy i) hA bound)
  have rHolder : ∀ y z, ‖r y - r z‖ ≤ (H i * A) * dist y z ^ bt := fun y z => by
    rw [dist_eq_norm]
    exact hol i φ A hA bound holder y z
  let ψ := BoundedHolderSpace.ofBound E bt r (H i * A) rHolder
  have hψ : ‖ψ‖ ≤ (Z i + H i) * A := by
    refine (BoundedHolderSpace.norm_ofBound_le E bt r (mul_nonneg (hH i) hA) rHolder).trans ?_
    have hr : ‖r‖ ≤ Z i * A :=
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (mul_nonneg (hZ i) hA) _
    rw [add_mul]
    exact max_le (hr.trans (le_add_of_nonneg_right (mul_nonneg (hH i) hA)))
      (le_add_of_nonneg_left (mul_nonneg (hZ i) hA))
  have physψ : BoundedHolderSpace.physical E bt ψ = r := rfl
  have suppψ : tsupport (BoundedHolderSpace.physical E bt ψ) ⊆ tsupport (w i) := by
    rw [physψ]
    apply closure_minimal _ (isClosed_tsupport _)
    intro y hy
    by_contra out
    exact hy (NativeChartTest.reading_of_not_mem_tsupport (m.atlas i) (w i) φ out)
  have term := pairing i (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
    (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i f) ψ suppψ
  rw [physψ] at term
  calc ‖∫ y, (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
          (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i f).val y *
          NativeChartTest.reading (m.atlas i) (LocalizedReferencePairing.weight m.atlas m.localization
            d χ i) φ y‖
      = ‖∫ y, (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
          (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i f).val y *
          r y‖ := rfl
    _ ≤ Cl i * ‖ψ‖ * ‖m.localBlocks i (ConstructedManifoldLocalization.localize m.atlas
          m.localization m.atlas_mem (SmoothSupportedManifoldCore.functions V)
          (SmoothSupportedManifoldCore.smooth V) i f)‖ := term
    _ ≤ Cl i * ((Z i + H i) * A) * ‖coreLift m.qa f‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hψ (hCl i)) (local_le_core m f i) (norm_nonneg _)
          (mul_nonneg (hCl i) (mul_nonneg (add_nonneg (hZ i) (hH i)) hA))
    _ = Cl i * (Z i + H i) * A * ‖coreLift m.qa f‖ := by ring

end Global

end ConditionedStochasticStabilityHyperbolic.PhysicalModelFullTestPairing
