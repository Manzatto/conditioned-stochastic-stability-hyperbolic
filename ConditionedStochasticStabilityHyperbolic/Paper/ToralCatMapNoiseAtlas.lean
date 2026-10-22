module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMapHL
public import LeanShared.Dynamics.ToralCatMapAffinePatches

/-! A constructed finite ordinary Whitney atlas for the concrete cat map,
using uniformly sized affine quotient patches. All positive-scale target
control statements follow from explicit lift estimates. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology Classical
namespace ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap
open LeanShared.ToralCatMap

theorem exists_finite_affine_cover : ∃ s : Finset (ℝ × ℝ),
    ∀ x : Torus, ∃ a ∈ s, x ∈ affinePatch a := by
  have cover : (univ : Set Torus) ⊆ ⋃ a : ℝ × ℝ, affinePatch a := by
    intro x _
    obtain ⟨a, rfl⟩ := quotient_surjective x
    exact mem_iUnion.mpr ⟨a, quotient_mem_affinePatch a⟩
  obtain ⟨s, cover⟩ := isCompact_univ.elim_finite_subcover affinePatch affinePatch_open cover
  refine ⟨s, ?_⟩
  intro x
  rcases mem_iUnion.mp (cover (mem_univ x)) with ⟨a, ha⟩
  rcases mem_iUnion.mp ha with ⟨inside, member⟩
  exact ⟨a, inside, member⟩

def patchIndex : Finset (ℝ × ℝ) := Classical.choose exists_finite_affine_cover
abbrev PatchIndex := {a : ℝ × ℝ // a ∈ patchIndex}

def patchCenter (i : Fin (Fintype.card PatchIndex)) : ℝ × ℝ :=
  ((Fintype.equivFin PatchIndex).symm i).val

def noiseAtlas : RegularNoise.WhitneyAtlas (E := Model) (LeanShared.ToralCatMap.homeomorph : Torus → Torus) where
  count := Fintype.card PatchIndex
  source i := affineChart (patchCenter i)
  target i := affineChart (map (patchCenter i))
  source_smooth i := affineChart_mem_maximalAtlas _
  target_smooth i := affineChart_mem_maximalAtlas _
  patch i := affinePatch (patchCenter i)
  patch_open i := affinePatch_open _
  patch_cover := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨a, ha, member⟩ := Classical.choose_spec exists_finite_affine_cover x
    refine mem_iUnion.mpr ⟨Fintype.equivFin PatchIndex ⟨a, ha⟩, ?_⟩
    simpa only [patchCenter, Equiv.symm_apply_apply] using member
  patch_compact i := affinePatch_compact _
  patch_source i := affinePatch_source _
  deterministic_target i := by
    simpa only [perturbation_zero] using
      perturbation_affinePatch_target (patchCenter i) 0 (by norm_num [patchRadius])

theorem noiseAtlas_coordinatePatch (i : Fin noiseAtlas.count) :
    noiseAtlas.coordinatePatch i = affineCoordinatePatch (patchCenter i) := rfl

theorem noiseAtlas_coordinate (u : Control) (small : ‖u‖ ≤ patchRadius)
    (i : Fin noiseAtlas.count) (y : Model) (hy : y ∈ noiseAtlas.coordinatePatch i) :
    noiseAtlas.coordinate (perturbation u) i y = affineCoordinate u y :=
  perturbation_affine_coordinate (patchCenter i) u small y hy

theorem noiseAtlas_reference_coordinate (i : Fin noiseAtlas.count) (y : Model)
    (hy : y ∈ noiseAtlas.coordinatePatch i) :
    noiseAtlas.coordinate LeanShared.ToralCatMap.homeomorph i y = affineCoordinate 0 y := by
  have equal : perturbation 0 = (LeanShared.ToralCatMap.homeomorph : Torus → Torus) :=
    funext perturbation_zero
  simpa only [equal] using noiseAtlas_coordinate 0 (by norm_num [patchRadius]) i y hy

end ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMap
