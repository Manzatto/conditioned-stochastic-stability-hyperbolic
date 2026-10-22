module
public import LeanShared.Geometry.AtlasHolderRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Strictly subunit fractional regularity is preserved by precomposition with a `C¹` self-map:
the chart Hölder bound of `f` near `φ x` is pulled back through the locally Lipschitz chart
expression of `φ`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

/-- The subunit chart Hölder condition of a regular function, without iterated derivatives. -/
theorem Regular.subunit_holder {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {f : M → F}
    (hf : Regular (E := E) (F := F) a f) (p : M) :
    ∃ U : Set E, IsOpen U ∧ extChartAt (𝓘(ℝ,E)) p p ∈ U ∧
      U ⊆ (extChartAt (𝓘(ℝ,E)) p).target ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ z ∈ U,
        ‖f ((extChartAt (𝓘(ℝ,E)) p).symm y) - f ((extChartAt (𝓘(ℝ,E)) p).symm z)‖ ≤
          C * ‖y - z‖ ^ a := by
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  have neq : a ≠ (⌊a⌋₊ : ℝ) := by rw [floor, Nat.cast_zero]; exact ha.ne'
  obtain ⟨U, hU, hp, hsub, C, hC, bound⟩ := hf.holder neq p
  refine ⟨U, hU, hp, fun y hy => (hsub hy).1, C, hC, fun y hy z hz => ?_⟩
  have b := bound y hy z hz
  rw [floor] at b
  simp only [Nat.cast_zero, sub_zero, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
    ← map_sub, LinearIsometryEquiv.norm_map, chartMap, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp] at b
  exact b

/-- A subunit regular function composed with a `C¹` self-map is regular of the same order. -/
theorem Regular.comp_contMDiff_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {f : M → F}
    (hf : Regular (E := E) (F := F) a f) {φ : M → M}
    (hφ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 φ) : Regular (E := E) (F := F) a (f ∘ φ) := by
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  have fcont : Continuous f := by
    have := hf.differentiable
    rw [floor] at this
    exact this.continuous
  refine regular_of_atlas_holder ha ha1 (fcont.comp hφ.continuous) fun x => ?_
  let e := chartAt E x
  let c := extChartAt (𝓘(ℝ,E)) (φ x)
  obtain ⟨U, hU, hpU, _, C, hC, bound⟩ := hf.subunit_holder ha ha1 (φ x)
  let g : E → E := c ∘ φ ∘ e.symm
  have eExt : (extChartAt (𝓘(ℝ,E)) x : M → E) = e := by
    rw [extChartAt_coe]; rfl
  have eExtSymm : ((extChartAt (𝓘(ℝ,E)) x).symm : E → M) = e.symm := by
    rw [extChartAt_coe_symm]; rfl
  have smooth : ContDiffAt ℝ 1 g (e x) := by
    have h := (contMDiffAt_iff.mp (hφ x)).2
    rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at h
    simpa only [g, c, eExt, eExtSymm, Function.comp_def] using h
  have gx : g (e x) = c (φ x) := by
    simp only [g, Function.comp_apply, e, (chartAt E x).left_inv (mem_chart_source E x)]
  obtain ⟨W, hW, hxW, hWU, A, hA, holder⟩ := LocalHolderComposition.exists_bound ha.le hC smooth
    (hU.mem_nhds (gx ▸ hpU)) bound
  let O : Set E := e.target ∩ e.symm ⁻¹' (φ ⁻¹' c.source)
  have hO : IsOpen O := by
    have := (hφ.continuous.comp_continuousOn e.continuousOn_symm).isOpen_inter_preimage
      e.open_target ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) (φ x)))
    exact this
  have hxO : e x ∈ O := ⟨e.map_source (mem_chart_source E x), by
    change φ (e.symm (e x)) ∈ c.source
    rw [e.left_inv (mem_chart_source E x)]
    exact mem_extChartAt_source (φ x)⟩
  refine ⟨e, chart_mem_maximalAtlas x, mem_chart_source E x, W ∩ O,
    inter_mem (hW.mem_nhds hxW) (hO.mem_nhds hxO), fun y hy => hy.2.1, A, hA,
    fun y hy z hz => ?_⟩
  have back : ∀ w ∈ O, f (φ (e.symm w)) = f (c.symm (g w)) := fun w hw => by
    simp only [g, Function.comp_apply, c.left_inv hw.2]
  change ‖f (φ (e.symm y)) - f (φ (e.symm z))‖ ≤ _
  rw [back y hy.2, back z hz.2]
  exact holder y hy.1 z hz.1

/-- Subunit regularity of a function along every iterate of a `C¹` self-map. -/
theorem Regular.comp_iterate {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {f : M → F}
    (hf : Regular (E := E) (F := F) a f) {φ : M → M}
    (hφ : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 φ) (l : ℕ) :
    Regular (E := E) (F := F) a (fun x => f (φ^[l] x)) := by
  induction l with
  | zero => exact hf
  | succ l ih =>
    have := ih.comp_contMDiff_one ha ha1 hφ
    simpa only [Function.comp_def, Function.iterate_succ_apply] using this

end LeanShared.FractionalManifoldRegularity
