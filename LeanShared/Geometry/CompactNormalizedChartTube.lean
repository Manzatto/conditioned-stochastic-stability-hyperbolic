module
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Bounded affine normalizations around a compact genuine chart patch
have one compact physical tube contained in the same chart source. -/
public noncomputable section
open Set Metric
namespace LeanShared.CompactNormalizedChartTube
variable {M E P : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem exists_tube (c : OpenPartialHomeomorph M E) (K : Set M)
    (compact : IsCompact K) (inside : K ⊆ c.source) (B : ℝ) (nonnegativeB : 0 ≤ B) :
    ∃ radius > 0, ∃ S : Set M, IsCompact S ∧ S ⊆ c.source ∧
      ∀ x ∈ K, ∀ L : P →L[ℝ] E, ‖L‖ ≤ B → ∀ z, ‖z‖ ≤ radius →
        c x+L z ∈ c.target ∧ c.symm (c x+L z) ∈ S := by
  have compactCoordinates : IsCompact (c '' K) :=
    compact.image_of_continuousOn (c.continuousOn.mono inside)
  have coordinatesInside : c '' K ⊆ c.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact c.map_source (inside hx)
  obtain ⟨δ,positiveδ,safe⟩ := compactCoordinates.exists_cthickening_subset_open c.open_target coordinatesInside
  let radius := δ/(B+1)
  have positiveRadius : 0 < radius := div_pos positiveδ (by linarith)
  have normalization : (B+1)*radius = δ := by dsimp only [radius]; field_simp
  let S := c.symm '' cthickening δ (c '' K)
  have compactS : IsCompact S := compactCoordinates.cthickening.image_of_continuousOn
    (c.symm.continuousOn.mono safe)
  have sourceS : S ⊆ c.source := by
    rintro _ ⟨y,hy,rfl⟩
    exact c.map_target (safe hy)
  refine ⟨radius,positiveRadius,S,compactS,sourceS,?_⟩
  intro x hx L bound z small
  have displacement : dist (c x+L z) (c x) ≤ δ := by
    rw [dist_eq_norm,add_sub_cancel_left]
    calc
      _ ≤ ‖L‖*‖z‖ := L.le_opNorm z
      _ ≤ B*radius := mul_le_mul bound small (norm_nonneg z) nonnegativeB
      _ ≤ (B+1)*radius := mul_le_mul_of_nonneg_right (by linarith) positiveRadius.le
      _ = δ := normalization
  have member := mem_cthickening_of_dist_le (c x+L z) (c x) δ (c '' K) (mem_image_of_mem c hx) displacement
  exact ⟨safe member,⟨c x+L z,member,rfl⟩⟩

end LeanShared.CompactNormalizedChartTube
