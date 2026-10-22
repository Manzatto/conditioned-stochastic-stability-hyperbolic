module
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! The genuine partial coordinate map of a physical homeomorphism is
C1 in both directions on its actual chart domains. This is the same native
map for every itinerary subdivision with fixed endpoint charts. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ChartedHomeomorphCoordinateMap
variable {E M : Type*} [NormedAddCommGroup E]
  [TopologicalSpace M]
  (c d : OpenPartialHomeomorph M E) (H : M ≃ₜ M)

def coordinateMap : OpenPartialHomeomorph E E :=
  (c.symm.trans H.toOpenPartialHomeomorph).trans d

@[simp] theorem coordinateMap_apply (z : E) : coordinateMap c d H z = d (H (c.symm z)) := rfl
@[simp] theorem coordinateMap_symm_apply (z : E) :
    (coordinateMap c d H).symm z = c (H.symm (d.symm z)) := rfl

theorem coordinateMap_source (z : E) :
    z ∈ (coordinateMap c d H).source ↔ z ∈ c.target ∧ H (c.symm z) ∈ d.source := by
  simp only [coordinateMap, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
    mem_inter_iff, mem_preimage, OpenPartialHomeomorph.symm_source]
  rfl

theorem coordinateMap_target (z : E) :
    z ∈ (coordinateMap c d H).target ↔ z ∈ d.target ∧ H.symm (d.symm z) ∈ c.source := by
  simp only [coordinateMap, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,
    mem_inter_iff, mem_preimage, OpenPartialHomeomorph.symm_target]
  simp only [mem_univ, true_and]
  rfl

variable [NormedSpace ℝ E] [ChartedSpace E M]
  (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)

include hc hd in
theorem forward (hH : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H) :
    ContDiffOn ℝ 1 (coordinateMap c d H) (coordinateMap c d H).source := by
  intro z hz
  have inside := (coordinateMap_source c d H z).mp hz
  have sourceSmooth := (contMDiffAt_symm_of_mem_maximalAtlas hc inside.1).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have targetSmooth := (contMDiffAt_of_mem_maximalAtlas hd inside.2).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  exact ((targetSmooth.comp z (hH.contMDiffAt.comp z sourceSmooth)).contDiffAt).contDiffWithinAt

include hc hd in
theorem backward (hH : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm) :
    ContDiffOn ℝ 1 (coordinateMap c d H).symm (coordinateMap c d H).target := by
  intro z hz
  have inside := (coordinateMap_target c d H z).mp hz
  have sourceSmooth := (contMDiffAt_symm_of_mem_maximalAtlas hd inside.1).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have targetSmooth := (contMDiffAt_of_mem_maximalAtlas hc inside.2).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  exact ((targetSmooth.comp z (hH.contMDiffAt.comp z sourceSmooth)).contDiffAt).contDiffWithinAt

end LeanShared.ChartedHomeomorphCoordinateMap
