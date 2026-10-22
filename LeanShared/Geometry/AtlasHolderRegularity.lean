module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import LeanShared.Analysis.LocalHolderComposition
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Fractional regularity transported from a genuine smooth atlas to
the literal chart definition. Coordinate-change Lipschitz constants and
their neighborhoods are derived from smoothness. No global metric on
the manifold is used. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem regular_of_atlas_holder {f : M → F} {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (continuous : Continuous f)
    (atlas : ∀ x : M, ∃ e : OpenPartialHomeomorph M E,
      e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M ∧ x ∈ e.source ∧
      ∃ D : Set E, D ∈ 𝓝 (e x) ∧ D ⊆ e.target ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ D, ∀ z ∈ D,
          ‖f (e.symm y) - f (e.symm z)‖ ≤ C * ‖y-z‖ ^ a) :
    Regular (E := E) (F := F) a f := by
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  refine ⟨ha.le, ?_, ?_⟩
  · rw [floor]
    exact contMDiff_zero_iff.mpr continuous
  · intro _ x
    obtain ⟨e, he, source, D, nearD, _subD, C, hC, holder⟩ := atlas x
    let c := extChartAt (𝓘(ℝ,E)) x
    let y := c x
    have cy : c.symm y = x := extChartAt_to_inv x
    have inverse : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ c.symm y := by
      exact (contMDiffWithinAt_extChartAt_symm_target_self x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    have transition : ContDiffAt ℝ 1 (e ∘ c.symm) y := by
      have forward : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e (c.symm y) := by
        rw [cy]
        exact contMDiffAt_of_mem_maximalAtlas he source
      exact (forward.comp y inverse).contDiffAt.of_le (by simp)
    have nearD' : D ∈ 𝓝 ((e ∘ c.symm) y) := by simpa only [Function.comp_apply, cy] using nearD
    obtain ⟨W, openW, inW, _mapsW, A, hA, bound⟩ :=
      LocalHolderComposition.exists_bound ha.le hC transition nearD' holder
    have nearSource : c.symm ⁻¹' e.source ∈ 𝓝 y :=
      inverse.continuousAt.preimage_mem_nhds (by
        rw [cy]
        exact e.open_source.mem_nhds source)
    obtain ⟨O, subO, openO, inO⟩ := mem_nhds_iff.mp
      (inter_mem ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)) nearSource)
    let Q := W ∩ O
    have inQ : y ∈ Q := ⟨inW, inO⟩
    refine ⟨Q, openW.inter openO, inQ, ?_, A, hA, ?_⟩
    · have included : Q ⊆ c.target := fun v hv => (subO hv.2).1
      change Q ⊆ chartDomain (E := E) (F := F) f x
      simpa only [chartDomain, extChartAt_model_space_eq_id, PartialEquiv.refl_source,
        preimage_univ, inter_univ] using included
    · intro v hv w hw
      have h := bound v hv.1 w hw.1
      have invv : e.symm (e (c.symm v)) = c.symm v := e.left_inv (subO hv.2).2
      have invw : e.symm (e (c.symm w)) = c.symm w := e.left_inv (subO hw.2).2
      rw [floor] 
      simp only [Nat.cast_zero, sub_zero, iteratedFDeriv_zero_eq_comp,
        Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]
      simpa only [chartMap, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        Function.id_comp, Function.comp_apply, id_eq, invv, invw] using h
end LeanShared.FractionalManifoldRegularity
