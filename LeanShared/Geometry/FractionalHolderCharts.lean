module
public import LeanShared.Geometry.AtlasHolderRegularity

/-! Actual fractional regularity gives local Hölder estimates in EVERY
genuine smooth chart, not just the chart selected in its definition.
This is the converse atlas-transport step used for chartwise smoothing. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem local_holder_in_chart {f : M → F} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hf : Regular (E := E) (F := F) a f) (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (y : E) (hy : y ∈ e.target) :
    ∃ D : Set E, IsOpen D ∧ y ∈ D ∧ D ⊆ e.target ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ v ∈ D, ∀ w ∈ D, ‖f (e.symm v) - f (e.symm w)‖ ≤ C * ‖v-w‖ ^ a := by
  let x := e.symm y
  let c := extChartAt (𝓘(ℝ,E)) x
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  have unequal : a ≠ (⌊a⌋₊ : ℝ) := by simpa only [floor, Nat.cast_zero] using ha.ne'
  obtain ⟨U, openU, inU, _, C, hC, bound⟩ := hf.holder unequal x
  rw [floor] at bound
  simp only [Nat.cast_zero, sub_zero, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map,
    chartMap, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] at bound
  have inverse : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas he hy
  have transition : ContDiffAt ℝ 1 (c ∘ e.symm) y :=
    (contMDiffAt_extChartAt.comp y inverse).contDiffAt.of_le (by simp)
  obtain ⟨W, openW, inW, _, A, hA, estimate⟩ :=
    LocalHolderComposition.exists_bound ha.le hC transition (openU.mem_nhds inU) bound
  have nearSource : e.symm ⁻¹' c.source ∈ 𝓝 y :=
    inverse.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))
  obtain ⟨O, subO, openO, inO⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_target.mem_nhds hy) nearSource)
  refine ⟨W ∩ O, openW.inter openO, ⟨inW,inO⟩,
    (fun v hv => (subO hv.2).1), A, hA, ?_⟩
  intro v hv w hw
  have invv : c.symm (c (e.symm v)) = e.symm v := c.left_inv (subO hv.2).2
  have invw : c.symm (c (e.symm w)) = e.symm w := c.left_inv (subO hw.2).2
  have result := estimate v hv.1 w hw.1
  change ‖f (c.symm (c (e.symm v))) - f (c.symm (c (e.symm w)))‖ ≤ A * ‖v-w‖ ^ a at result
  simpa only [invv, invw] using result
end LeanShared.FractionalManifoldRegularity
