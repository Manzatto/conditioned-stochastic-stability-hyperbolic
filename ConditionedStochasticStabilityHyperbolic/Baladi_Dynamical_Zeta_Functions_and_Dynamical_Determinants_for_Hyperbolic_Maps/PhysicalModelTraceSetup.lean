module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceCharts
public import LeanShared.Geometry.TraceChartCutoffs
public import LeanShared.Dynamics.RegularizedLefschetzSetup
meta import Lean.LibrarySuggestions.Basic

/-! Trace charts of a physical model whose map sends the weight support into the core region.
The real localization cutoffs sum to one on the compact set `R = T(tsupport g) ⊆ V`; a smooth
partition of unity `c'_j` on `R` subordinate to `{c_j ≠ 0} ∩ V` gives the chart weights
`wt_j = (c'_j / c_j) ∘ φ_j⁻¹` and chart bumps `cut_j` equal to one on a uniform thickening of
`φ_j(tsupport c'_j)`. The partition identity of the trace family holds at every image point of
the weight support, and `c_j · wt_j ∘ φ_j = c'_j` matches the regularized Lefschetz cutoffs. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTraceSetup"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Metric Bundle
open scoped Manifold ContDiff SchwartzMap
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

theorem trace_charts (a : Ω) (β : m.localization.indices → M → ℝ)
    (hβ : ∀ j x, m.localization.cutoff j x = (β j x : ℂ))
    (hβs : ∀ j, ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ (β j))
    (mapCont : Continuous (m.maps a)) (openV : IsOpen V)
    (forwardSupport : m.maps a '' tsupport m.weight ⊆ V) :
    ∃ (tc : TraceCharts m) (c' : m.localization.indices → M → ℝ) (εc : ℝ), 0 < εc ∧
      (∀ j, ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ (c' j)) ∧ (∀ j x, 0 ≤ c' j x) ∧
      (∀ j : m.localization.indices, tsupport (c' j) ⊆ (m.atlas j).source) ∧
      (∀ x ∈ m.maps a '' tsupport m.weight, ∑ j, c' j x = 1) ∧
      (∀ x, m.weight x ≠ 0 → (∑ j : m.localization.indices,
        if m.maps a x ∈ (m.atlas j).source then
          tc.wt j (m.atlas j (m.maps a x)) * m.localization.cutoff j (m.maps a x) else 0) = 1) ∧
      (∀ j : m.localization.indices, ∀ x ∈ (m.atlas j).source,
        (c' j x : ℂ) = m.localization.cutoff j x * tc.wt j (m.atlas j x)) ∧
      (∀ j : m.localization.indices, ∀ z ∈ (m.atlas j).target, c' j ((m.atlas j).symm z) ≠ 0 →
        ∀ u, ‖u - z‖ ≤ εc → tc.cut j u = 1) := by
  let R : Set M := m.maps a '' tsupport m.weight
  have hR : IsCompact R := (isClosed_tsupport _).isCompact.image mapCont
  have hsum : ∀ x ∈ R, ∑ j, β j x = 1 := fun x hx => by
    have total := m.localization.partition x (m.region_subset_support (forwardSupport hx))
    simp only [hβ] at total
    exact_mod_cast total
  have hβsupp : ∀ j, tsupport (β j) ⊆ (m.atlas j).source := fun j => by
    have : tsupport (β j) = tsupport (m.localization.cutoff j) := by
      unfold tsupport
      congr 1
      ext x
      simp [hβ]
    rw [this]
    exact m.localization.support j
  obtain ⟨c', wt, cut, εc, εpos, c'smooth, c'nonneg, c'source, c'V, c'sum, c'eq, cutCompact,
    wtCompact, cutSupp, cutRegion, wtOne, cutOne⟩ :=
    TraceChartCutoffs.exists_cutoffs (fun j : m.localization.indices => m.atlas j)
      (fun j => m.atlas_mem j) β hβs hβsupp hR openV forwardSupport hsum
  have tsupportEq : ∀ j, tsupport (β j) = tsupport (m.localization.cutoff j) := fun j => by
    unfold tsupport
    congr 1
    ext x
    simp [hβ]
  let tc : TraceCharts m :=
    { cut := cut
      cutCompact := cutCompact
      cutSupport := fun j => (cutSupp j).trans (by
        change (m.atlas j) '' tsupport (β j) ⊆ (m.atlas j) '' tsupport (m.localization.cutoff j)
        rw [tsupportEq])
      cutRegion := cutRegion
      wt := wt
      wtCompact := wtCompact
      wtOne := wtOne }
  have matched : ∀ j : m.localization.indices, ∀ x ∈ (m.atlas j).source,
      (c' j x : ℂ) = m.localization.cutoff j x * tc.wt j (m.atlas j x) := fun j x hx => by
    rw [hβ]
    exact c'eq j x hx
  refine ⟨tc, c', εc, εpos, c'smooth, c'nonneg, c'source, c'sum, fun x hx => ?_, matched,
    cutOne⟩
  have inR : m.maps a x ∈ R := mem_image_of_mem _ (subset_tsupport _ hx)
  have terms : ∀ j : m.localization.indices, (if m.maps a x ∈ (m.atlas j).source then
      tc.wt j (m.atlas j (m.maps a x)) * m.localization.cutoff j (m.maps a x) else 0) =
      (c' j (m.maps a x) : ℂ) := fun j => by
    by_cases hs : m.maps a x ∈ (m.atlas j).source
    · rw [ite_eq_left hs, matched j _ hs, mul_comm]
    · rw [ite_eq_right hs]
      have : c' j (m.maps a x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hs (c'source j h)
      rw [this, Complex.ofReal_zero]
  rw [Finset.sum_congr rfl fun j _ => terms j, ← Complex.ofReal_sum, c'sum _ inR,
    Complex.ofReal_one]

section Setup
variable [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
open HyperbolicBasicSet

/-- A regularized Lefschetz trace setup on the model charts, with the partition `c'` and the model
weight. -/
theorem trace_setup {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) (r : ℝ) (hr : 1 < r)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (frame : IsometricFraming bd.hyperbolic)
    (c' : m.localization.indices → M → ℝ) (c'cont : ∀ j, Continuous (c' j))
    (c'nonneg : ∀ j x, 0 ≤ c' j x) (c'source : ∀ j, tsupport (c' j) ⊆ (m.atlas j).source)
    (c'sum : ∀ x ∈ Λ, ∑ j, c' j x = 1)
    (weightCont : Continuous m.weight) (weightNonneg : ∀ x, 0 ≤ m.weight x)
    (weightPos : ∀ x ∈ Λ, 0 < m.weight x) (weightSupport : ∀ x, m.weight x ≠ 0 → x ∈ closure V)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (weightRegular : ∀ l : ℕ, FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q
      (fun x => m.weight ((T : M → M)^[l] x))) :
    ∃ s : TraceSetup bd, ∃ e : s.charts.ι ≃ m.localization.indices,
      (∀ i, s.charts.chart i = m.atlas (e i)) ∧ s.weight = m.weight ∧
      (∀ i, s.cutoff i = c' (e i)) ∧ s.r = r := by
  classical
  choose δ δpos δsub using fun j => (isClosed_tsupport (c' j)).isCompact.exists_cthickening_subset_open
    (m.atlas j).open_source (c'source j)
  obtain ⟨μ0, μpos, μle⟩ := TraceChartCutoffs.exists_margin (fun j => δ j / 3)
    (fun j => by linarith [δpos j])
  let k : Fin (Fintype.card m.localization.indices) ≃ m.localization.indices :=
    (Fintype.equivFin _).symm
  let charts : PeriodicChartConstants.ChartFamily E M :=
    { ι := Fin (Fintype.card m.localization.indices)
      fintype := inferInstance
      chart := fun i => m.atlas (k i)
      mem := fun i => m.atlas_mem _
      domain := fun i => thickening (2 * μ0) (tsupport (c' (k i)))
      isOpen_domain := fun _ => isOpen_thickening
      closure_domain := fun i => (closure_thickening_subset_cthickening _ _).trans
        ((cthickening_mono (by linarith [μle (k i), δpos (k i)]) _).trans (δsub (k i)))
      marked := fun i => cthickening μ0 (tsupport (c' (k i)))
      compact_marked := fun _ => isClosed_cthickening.isCompact
      marked_domain := fun _ => cthickening_subset_thickening' (by positivity) (by linarith) _ }
  have sumFin : ∀ x, ∑ i ∈ (@Finset.univ _ charts.fintype), c' (k i) x = ∑ j, c' j x :=
    fun x => Equiv.sum_comp k (fun j => c' j x)
  let s : TraceSetup bd :=
    { forward := forward
      inverse := inverse
      r := r
      one_lt_r := hr
      regular := regular
      frame := frame
      charts := charts
      cover := fun x hx => by
        obtain ⟨j, hj⟩ : ∃ j, c' j x ≠ 0 := by
          by_contra h
          simp only [not_exists, not_not] at h
          have := c'sum x hx
          simp [h] at this
        exact mem_iUnion.mpr ⟨k.symm j, by
          change x ∈ thickening (2 * μ0) (tsupport (c' (k (k.symm j))))
          rw [Equiv.apply_symm_apply]
          exact self_subset_thickening (by positivity) _ (subset_tsupport _ hj)⟩
      cutoff := fun i => c' (k i)
      cutoff_continuous := fun _ => c'cont _
      cutoff_nonneg := fun _ _ => c'nonneg _ _
      cutoff_sum := fun x hx => (sumFin x).trans (c'sum x hx)
      margin := μ0
      margin_pos := μpos
      cutoff_margin := fun _ => subset_rfl
      weight := m.weight
      weight_continuous := weightCont
      weight_nonneg := weightNonneg
      weight_pos := weightPos
      weight_support := weightSupport
      q := q
      q_pos := hq0
      q_lt_one := hq1
      weight_regular := weightRegular }
  exact ⟨s, k, fun _ => rfl, rfl, fun _ => rfl, rfl⟩

end Setup

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
