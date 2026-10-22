module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafHolderCoreBounds
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafIntegralControl
public import LeanShared.Analysis.LowOrderChartPairing
public import LeanShared.Analysis.SchwartzAmbientLeafEntry
meta import Lean.LibrarySuggestions.Basic

/-! Low-order pairing on one chart of the complete heterogeneous fake-leaf carrier: the integral of
a supported core function against a compactly supported Hölder test of order `b` is bounded by
the test's Hölder norm times the carrier's local block norm, whenever `b + t(s) > 0`. The
parallel affine leaves belong to the full fake-leaf family (with the induced Haar volume), and
each of their integrals is controlled by the block norm. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AllFakeLeafLowOrderPairing"

public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafLowOrderPairing
open LeanShared AllFakeLeafModel

variable {E I ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Finite I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
  (planes : I → Submodule ℝ E) (plus : I → Set E)
  (cone : ∀ i, ConeData (planes i) (plus i))
  (coordinates : ∀ i, EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] planes i)
  (basis : ∀ i, OrthonormalBasis ι ℝ (planes i))
  {minus : Set E} (radial : ConeDyadicSymbols.RadialCutoff)
  {Cp : Set E} (angle : ConeDyadicSymbols.AngularCutoff Cp minus)
  {K : Set E} (compactK : IsCompact K) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (exponent : Bool → ℝ) (margin : ∀ sign, exponent sign ≤ b) (i : I)

theorem induced_le (f : SchwartzJetSpace.supportedCore K) (j : ℕ × Bool)
    (Γ : Index (planes i) (plus i)) :
    (∫ x, ‖ConeFourierBlocks.block (ConeDyadicSymbols.symbols radial angle j) f.val x‖
        ∂inducedVolume (planes i) volume Γ.val) ≤
      ((2 : ℝ) ^ (exponent j.2 * j.1))⁻¹ *
        ‖SchwartzAmbientBlocks.coreMap (volume : Measure (EuclideanSpace ℝ ι))
          (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
          (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i) K
          (ConeDyadicSymbols.symbols radial angle) exponent
          (AllFakeLeafHolderCoreBounds.bounded planes plus cone coordinates basis radial angle
            compactK hb hb1 exponent margin i) f‖ := by
  let a : Heterogeneous.ChartIndex planes plus :=
    Function.update (Heterogeneous.defaultIndex planes plus) i Γ
  have ha : a i = Γ := Function.update_self _ _ _
  have entry := SchwartzAmbientLeafEntry.leaf_le_core (volume : Measure (EuclideanSpace ℝ ι))
    (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
    (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i) K
    (ConeDyadicSymbols.symbols radial angle) exponent
    (AllFakeLeafHolderCoreBounds.bounded planes plus cone coordinates basis radial angle
      compactK hb hb1 exponent margin i) f j a
  have measure : (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i a).measure
      (volume : Measure (EuclideanSpace ℝ ι)) = inducedVolume (planes i) volume Γ.val := by
    rw [AllFakeLeafHolderCoreBounds.leaves, Heterogeneous.leaves_measure, ha,
      (coordinates i).measurePreserving.map_eq]
  rw [measure] at entry
  exact entry

/-- The single-chart low-order pairing bound against the carrier's local block norm. -/
theorem chart_pairing {Kt : Set E} (compactT : IsCompact Kt) {bt : ℝ} (hbt : 0 < bt)
    (hbt1 : bt ≤ 1) (ht : ∀ s, 0 < bt + exponent s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzJetSpace.supportedCore K)
      (v : BoundedHolderSpace.graph E bt),
      tsupport (BoundedHolderSpace.physical E bt v) ⊆ Kt →
      ‖∫ x, f.val x * BoundedHolderSpace.physical E bt v x‖ ≤ C * ‖v‖ *
        ‖SchwartzAmbientBlocks.coreMap (volume : Measure (EuclideanSpace ℝ ι))
          (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
          (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i) K
          (ConeDyadicSymbols.symbols radial angle) exponent
          (AllFakeLeafHolderCoreBounds.bounded planes plus cone coordinates basis radial angle
            compactK hb hb1 exponent margin i) f‖ := by
  obtain ⟨L, hdensity, _graphs, control⟩ :=
    exists_parallel_integral_control (planes i) (plus i) (cone i) (basis i)
  obtain ⟨C0, hC0, bound⟩ := LowOrderChartPairing.chart_bound radial angle (planes i) L compactT
    hbt hbt1 exponent ht
  refine ⟨C0 / GraphJacobian.density (basis i) L, div_nonneg hC0 hdensity.le, ?_⟩
  intro f v support
  set N := ‖SchwartzAmbientBlocks.coreMap (volume : Measure (EuclideanSpace ℝ ι))
      (GraphJacobian.densityBound_nonneg (ι := ι) (Heterogeneous.commonSlope planes plus cone))
      (AllFakeLeafHolderCoreBounds.leaves planes plus cone coordinates basis i) K
      (ConeDyadicSymbols.symbols radial angle) exponent
      (AllFakeLeafHolderCoreBounds.bounded planes plus cone coordinates basis radial angle
        compactK hb hb1 exponent margin i) f‖ with hN
  have hB : 0 ≤ N / GraphJacobian.density (basis i) L := div_nonneg (norm_nonneg _) hdensity.le
  have leaves : ∀ (n : ℕ) (s : Bool) (w : (planes i)ᗮ),
      ∫ u : planes i, ‖ConeFourierBlocks.block (ConeDyadicSymbols.symbols radial angle (n, s)) f.val
          ((u : E) + (L u : E) + (w : E))‖ ≤
        ((2 : ℝ) ^ (exponent s * n))⁻¹ * (N / GraphJacobian.density (basis i) L) := by
    intro n s w
    have h := control (ConeFourierBlocks.block (ConeDyadicSymbols.symbols radial angle (n, s)) f.val)
      (((2 : ℝ) ^ (exponent s * n))⁻¹ * N)
      (ConeFourierBlocks.block _ f.val).continuous
      (fun Γ => induced_le planes plus cone coordinates basis radial angle compactK hb hb1 exponent
        margin i f (n, s) Γ) w
    rw [mul_div_assoc] at h
    exact h
  have result := bound f.val v support (N / GraphJacobian.density (basis i) L) hB leaves
  calc ‖∫ x, f.val x * BoundedHolderSpace.physical E bt v x‖
      ≤ C0 * ‖v‖ * (N / GraphJacobian.density (basis i) L) := result
    _ = C0 / GraphJacobian.density (basis i) L * ‖v‖ * N := by ring

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafLowOrderPairing
