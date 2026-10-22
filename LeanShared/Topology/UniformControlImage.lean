module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! An ordinary open endpoint-image certificate gives a UNIFORM control
radius on a compact phase space. The radius is chosen before starting states
and targets. Only the rank-chart openness source remains classical. -/

@[expose] public noncomputable section
open Set Metric
namespace LeanShared.UniformControlImage
variable {X Ω : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_uniform_radius
    (T : X → X) (hT : Continuous T) (F : X × Ω → X)
    (O : Set Ω) (zero : Ω) (hz : zero ∈ O) (hzero : ∀ x, F (x, zero) = T x)
    (image_open : IsOpen ((fun p : X × Ω => (p.1, F p)) '' (univ ×ˢ O))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : X, dist (T x) y < δ → ∃ a ∈ O, F (x, a) = y := by
  let graph : Set (X × X) := range (fun x => (x, T x))
  have hc : IsCompact graph := isCompact_range (continuous_id.prodMk hT)
  have hi : graph ⊆ (fun p : X × Ω => (p.1, F p)) '' (univ ×ˢ O) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(x, zero), ⟨mem_univ _, hz⟩, by simp only [hzero]⟩
  obtain ⟨δ, hδ, hball⟩ := hc.exists_thickening_subset_open image_open hi
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hm : (x, y) ∈ thickening δ graph := by
    apply mem_thickening_iff.mpr
    refine ⟨(x, T x), ⟨x, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    simpa only [dist_comm] using hxy
  obtain ⟨⟨z, a⟩, ha, heq⟩ := hball hm
  have hzx : z = x := congrArg Prod.fst heq
  have hFy : F (z, a) = y := congrArg Prod.snd heq
  exact ⟨a, ha.2, hzx ▸ hFy⟩

end LeanShared.UniformControlImage
