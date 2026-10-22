module
public import LeanShared.Dynamics.HyperbolicAdaptedReferenceCover
public import LeanShared.Geometry.CompactCenteredFrameBounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Finite actual fixed-chart adapted atlas, retaining the chosen one-step
adapted geometry and deriving its common coordinate-frame bounds. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

structure ChartAtlas (system : PatchSystem b) where
  centers : Finset Λ
  patch : Λ → Set Λ
  compact : ∀ c, IsCompact (patch c)
  inside : ∀ c, patch c ⊆ system.frameDomain c
  center_mem : ∀ c, c ∈ interior (patch c)
  cover : (univ : Set Λ) ⊆ ⋃ c ∈ centers, interior (patch c)
  bound : ℝ
  one_le_bound : 1 ≤ bound
  frame_bounds : ∀ c ∈ centers, ∀ y (hy : y ∈ patch c),
    let R := ContinuousCenteredFrameCharts.chartFrame c.val y.val (inside c hy).2
      (system.referenceFrame c ⟨y, inside c hy⟩)
    ‖R.toContinuousLinearMap‖ ≤ bound ∧ ‖R.symm.toContinuousLinearMap‖ ≤ bound

theorem PatchSystem.exists_chart_atlas (system : PatchSystem b) : Nonempty (ChartAtlas system) := by
  classical
  obtain ⟨centers, patch, properties, cover⟩ := system.exists_chart_cover
  have inside (c : Λ) : patch c ⊆ system.frameDomain c := by
    intro y hy
    have member := (system.patch_properties c).2.1 y ((properties c).2.1 hy)
    exact ⟨⟨member.2, member.1⟩, (properties c).2.2.1 y hy⟩
  have localBounds (c : Λ) := CompactCenteredFrameBounds.uniform_bounds
    (system.frameDomain c) (patch c) (properties c).1 (inside c) c.val Subtype.val
    (fun y => y.property.2) (system.referenceFrame c) (system.referenceFrame_sections c)
  choose B oneB bounds using localBounds
  let total := ∑ c ∈ centers, B c
  have total_nonnegative : 0 ≤ total := Finset.sum_nonneg
    (fun c _ => zero_le_one.trans (oneB c))
  have below (c : Λ) (hc : c ∈ centers) : B c ≤ total :=
    Finset.single_le_sum (fun d _ => zero_le_one.trans (oneB d)) hc
  exact ⟨{
    centers := centers
    patch := patch
    compact := fun c => (properties c).1
    inside := inside
    center_mem := fun c => (properties c).2.2.2
    cover := cover
    bound := total + 1
    one_le_bound := by linarith
    frame_bounds := fun c hc y hy =>
      ⟨((bounds c y hy).1.trans (below c hc)).trans (by linarith),
        ((bounds c y hy).2.trans (below c hc)).trans (by linarith)⟩ }⟩

@[expose] def PatchSystem.chartAtlas (system : PatchSystem b) : ChartAtlas system :=
  Classical.choice system.exists_chart_atlas

end LeanShared.HyperbolicAdaptedPatchSystem
