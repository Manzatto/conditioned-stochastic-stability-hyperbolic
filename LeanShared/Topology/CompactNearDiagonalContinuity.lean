module
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Compact

/-! Actual continuity on an open neighborhood of a compact set gives one
near-diagonal radius, even when the second point lies outside the compact set. -/
public section
open Set Filter
open scoped Topology
namespace LeanShared.CompactNearDiagonalContinuity
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem exists_radius (K U : Set X) (compact : IsCompact K) (openU : IsOpen U)
    (inside : K ⊆ U) (f : X → Y) (continuous : ContinuousOn f U)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K, ∀ y, dist x y < η → y ∈ U ∧ dist (f x) (f y) < ε := by
  have coordinate := compact.uniformContinuousAt_of_continuousAt f
    (fun x hx => (continuous x (inside hx)).continuousAt (openU.mem_nhds (inside hx)))
    (Metric.dist_mem_uniformity positive)
  obtain ⟨W,hW,_,domain⟩ := lebesgue_number_of_compact_open compact openU inside
  obtain ⟨η,hη,small⟩ := Metric.mem_uniformity_dist.mp (inter_mem coordinate hW)
  refine ⟨η,hη,fun x hx y hxy => ?_⟩
  have facts := small hxy
  exact ⟨domain x hx facts.2,facts.1 hx⟩
end LeanShared.CompactNearDiagonalContinuity
