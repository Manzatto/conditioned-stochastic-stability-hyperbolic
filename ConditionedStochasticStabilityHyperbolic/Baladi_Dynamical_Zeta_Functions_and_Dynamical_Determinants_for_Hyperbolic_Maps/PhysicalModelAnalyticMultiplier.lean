module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestPairing
public import LeanShared.Analysis.ConeMultiplierBound
public import LeanShared.Geometry.SupportedChartExtension
public import LeanShared.Geometry.SupportedCoreMultipliers
meta import Lean.LibrarySuggestions.Basic

/-! Bounded multiplication on the strong space of a physical model. For a smooth global function
`ψ`, each chart localization of `ψ f` is the localization of `f` multiplied by the Schwartz
function `a_i = ζ_i (ψ ∘ κ_i⁻¹)` (`ζ_i` a cutoff equal to one on the local support), so the
Euclidean multiplier bound on each chart, together with the finite chart supremum, bounds
multiplication by `ψ` in the strong core norm. The leaf family of every chart is assumed
translation-closed and the exponents satisfy the first-commutator conditions. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelAnalyticMultiplier"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff SchwartzMap NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelAnalyticMultiplier
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

instance leaf_sFinite {J : ℝ} (L : GraphLeafNorm.GraphLeaf U E J) :
    SFinite (L.measure μ) := by
  unfold GraphLeafNorm.GraphLeaf.measure GraphLeafNorm.GraphLeaf.sourceMeasure
  infer_instance

/-- Each chart localization of `ψ f` is the localization of `f` times a fixed Schwartz function. -/
theorem chart_multiplier (i : m.localization.indices) (ψ : M → ℂ)
    (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ) :
    ∃ a : 𝓢(E, ℂ), ∀ c : Core (E := E) V,
      (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
          (SmoothSupportedManifoldCore.multiplier V ψ hψ c)).val =
        LeafCommutator.mul a (ConstructedManifoldLocalization.localize m.atlas m.localization
          m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
            i c).val := by
  obtain ⟨ζ, ζc, ζin, ζone⟩ := CompactSchwartzCutoff.exists_cutoff
    (ConstructedManifoldLocalization.support_compact m.atlas m.localization i)
    (m.atlas i).open_target
    (ChartLocalization.localSupport_subset_target (m.atlas i) (m.localization.cutoff i)
      (m.localization.support i))
  let θ : M → ℂ := SupportedChartExtension.function (m.atlas i) ζ
  have hθs : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ θ :=
    SupportedChartExtension.smooth (m.atlas i) (m.atlas_mem i) (ζ.smooth ⊤) ζc ζin
  have hθc : HasCompactSupport θ := SupportedChartExtension.compact_support (m.atlas i) ζc ζin
  have hθsupp : tsupport θ ⊆ (m.atlas i).source := by
    refine (SupportedChartExtension.support_subset (m.atlas i) ζc ζin).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (m.atlas i).map_target (ζin hy)
  have smooth := ChartLocalization.coordinate_contDiff (m.atlas i) θ hθsupp (m.atlas_mem i) hθs hθc
    ψ hψ
  have compact := ChartLocalization.coordinate_hasCompactSupport (m.atlas i) θ hθsupp hθc ψ
  refine ⟨compact.toSchwartzMap smooth, fun c => ?_⟩
  ext y
  rw [LeafCommutator.mul_apply]
  change _ = ChartLocalization.coordinate (m.atlas i) θ ψ y * _
  by_cases hy : y ∈ (m.atlas i).target
  · have hx : (m.atlas i).symm y ∈ (m.atlas i).source := (m.atlas i).map_target hy
    rw [← (m.atlas i).right_inv hy, ConstructedManifoldLocalization.localize_apply _ _ _ _ _ _ _ _ hx,
      ConstructedManifoldLocalization.localize_apply _ _ _ _ _ _ _ _ hx,
      ChartLocalization.coordinate_chart (m.atlas i) θ ψ _ hx,
      SmoothSupportedManifoldCore.multiplier_apply]
    by_cases h0 : m.localization.cutoff i ((m.atlas i).symm y) = 0
    · rw [h0]
      ring
    · have one : θ ((m.atlas i).symm y) = 1 := by
        change SupportedChartExtension.function (m.atlas i) ζ ((m.atlas i).symm y) = 1
        rw [SupportedChartExtension.coordinate (m.atlas i) y hy]
        apply ζone
        rw [← (m.atlas i).right_inv hy]
        exact ⟨_, subset_tsupport _ h0, rfl⟩
      rw [one]
      ring
  · have hy' : y ∉ ConstructedManifoldLocalization.support m.atlas m.localization i := fun h =>
      hy (ChartLocalization.localSupport_subset_target (m.atlas i) (m.localization.cutoff i)
        (m.localization.support i) h)
    rw [(ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
          (SmoothSupportedManifoldCore.multiplier V ψ hψ c)).property y hy',
      (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
          c).property y hy', mul_zero]

set_option maxHeartbeats 1600000 in
/-- Multiplication by a smooth global function is bounded in the strong core norm. -/
theorem analytic_multiplier
    (translate : ∀ i c (z : E), ∃ c', ((m.leaves i c).measure μ).map (fun x => x + z) =
      (m.leaves i c').measure μ)
    (h1 : ∀ i σ s, m.exponent i σ - 1 - m.exponent i s < 0)
    (h2 : ∀ i s, -1 - m.exponent i s < 0) (h3 : ∀ i σ, m.exponent i σ ≤ 1)
    (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : Core (E := E) V,
      ‖coreLift m.qa (SmoothSupportedManifoldCore.multiplier V ψ hψ c)‖ ≤ C * ‖coreLift m.qa c‖ := by
  have perChart : ∀ i : m.localization.indices, ∃ C : ℝ, 0 ≤ C ∧ ∀ c : Core (E := E) V,
      ‖m.localBlocks i (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
          (SmoothSupportedManifoldCore.multiplier V ψ hψ c))‖ ≤
        C * ‖m.localBlocks i (ConstructedManifoldLocalization.localize m.atlas m.localization
          m.atlas_mem (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
            i c)‖ := by
    intro i
    obtain ⟨a, ha⟩ := chart_multiplier m i ψ hψ
    obtain ⟨C, hC, bound⟩ := ConeMultiplierBound.multiplier_bound μ m.slope_nonnegative (m.leaves i)
      (ConstructedManifoldLocalization.support m.atlas m.localization i) (m.radial i) (m.angle i)
      (m.exponent i) (m.boundedBlocks i) (translate i) (h1 i) (h2 i) (h3 i) a
    exact ⟨C, hC, fun c => bound _ _ (ha c)⟩
  choose C hC bound using perChart
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC i, fun c => ?_⟩
  have hB : 0 ≤ (∑ i, C i) * ‖coreLift m.qa c‖ :=
    mul_nonneg (Finset.sum_nonneg fun i _ => hC i) (norm_nonneg _)
  have each (i : m.localization.indices) :
      ‖m.localBlocks i (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
          (SmoothSupportedManifoldCore.multiplier V ψ hψ c))‖ ≤
        (∑ i, C i) * ‖coreLift m.qa c‖ :=
    (bound i c).trans (mul_le_mul
      (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i))
      (PhysicalModelFullTestPairing.local_le_core m c i) (norm_nonneg _)
      (Finset.sum_nonneg fun i _ => hC i))
  rw [show ‖coreLift m.qa (SmoothSupportedManifoldCore.multiplier V ψ hψ c)‖ =
      ((Finset.univ.sup (fun i => ‖m.localBlocks i
        (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
          (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
            (SmoothSupportedManifoldCore.multiplier V ψ hψ c))‖₊) : ℝ≥0) : ℝ) from rfl]
  have sup : (Finset.univ.sup (fun i => ‖m.localBlocks i
      (ConstructedManifoldLocalization.localize m.atlas m.localization m.atlas_mem
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
          (SmoothSupportedManifoldCore.multiplier V ψ hψ c))‖₊) : ℝ≥0) ≤
        Real.toNNReal ((∑ i, C i) * ‖coreLift m.qa c‖) :=
    Finset.sup_le fun i _ => (Real.le_toNNReal_iff_coe_le hB).mpr (each i)
  exact (NNReal.coe_le_coe.mpr sup).trans (le_of_eq (Real.coe_toNNReal _ hB))

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnalyticMultiplier
