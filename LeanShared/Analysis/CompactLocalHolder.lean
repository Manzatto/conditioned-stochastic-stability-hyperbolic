module
public import Mathlib.Topology.MetricSpace.Snowflaking
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! A genuine local-to-uniform Hölder bound on compact sets. Snowflaking turns the two-point Hölder
condition into Lipschitz continuity, so the compact local-Lipschitz theorem supplies the uniform
constant. -/
public noncomputable section
open Set Filter Metric
open scoped Topology
namespace LeanShared.CompactLocalHolder
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem bound_on_compact {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {K : Set X} (hK : IsCompact K) (f : X → Y)
    (localBound : ∀ x ∈ K, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ W, ∀ z ∈ W,
        dist (f y) (f z) ≤ C * dist y z ^ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      dist (f x) (f y) ≤ C * dist x y ^ a := by
  let H := Snowflaking X a ha ha1
  let e : H ≃ₜ X := Snowflaking.homeomorph
  have compact : IsCompact (e ⁻¹' K) := e.isCompact_preimage.mpr hK
  have locally : LocallyLipschitzOn (e ⁻¹' K) (fun x => f (e x)) := by
    intro x hx
    obtain ⟨W, hW, hxW, C, hC, hbound⟩ := localBound (e x) hx
    refine ⟨⟨C, hC⟩, e ⁻¹' W, mem_nhdsWithin_of_mem_nhds ((hW.preimage e.continuous).mem_nhds hxW), ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    change dist (f (e y)) (f (e z)) ≤ C * dist (e y) (e z) ^ a
    exact hbound (e y) hy (e z) hz
  obtain ⟨C, bound⟩ := locally.exists_lipschitzOnWith_of_compact compact
  refine ⟨C, C.coe_nonneg, fun x hx y hy => ?_⟩
  have h := bound.dist_le_mul (e.symm x) hx (e.symm y) hy
  change dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ a at h
  exact h
end LeanShared.CompactLocalHolder
