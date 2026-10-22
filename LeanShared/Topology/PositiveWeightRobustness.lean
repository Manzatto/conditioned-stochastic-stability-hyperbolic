module

public import Mathlib.Topology.MetricSpace.Thickening

/-! # Actual weights remain positive under a uniform local noise threshold

A fixed compact control collar lies in the positive region of w∘T. A common
C0 perturbation threshold then makes w∘F positive there for every noise map.
The threshold is independent of noisy spectral vectors or their zero sets.
-/

@[expose] public section
open Set Metric
namespace LeanShared.PositiveWeightRobustness
variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]

theorem exists_positive_composition_threshold
    (K : Set X) (hK : IsCompact K) (T : X → Y) (hT : ContinuousOn T K)
    (w : Y → ℝ) (hw : Continuous w) (hpos : ∀ x ∈ K, 0 < w (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : X → Y,
      (∀ x ∈ K, dist (F x) (T x) < δ) → ∀ x ∈ K, 0 < w (F x) := by
  have himage := hK.image_of_continuousOn hT
  have hopen : IsOpen {y | 0 < w y} := isOpen_lt continuous_const hw
  have hsub : T '' K ⊆ {y | 0 < w y} := by
    rintro y ⟨x, hx, rfl⟩
    exact hpos x hx
  obtain ⟨δ, hδ, hδsub⟩ := himage.exists_thickening_subset_open hopen hsub
  refine ⟨δ, hδ, ?_⟩
  intro F hF x hx
  exact hδsub (mem_thickening_iff.mpr ⟨T x, ⟨x, hx, rfl⟩, hF x hx⟩)

/-- The same threshold applies to every sampled map; no density regularity,
noise-law convergence or operator measurability hypothesis is needed. -/
theorem exists_noise_positive_composition_threshold {Ω : Type*}
    (K : Set X) (hK : IsCompact K) (T : X → Y) (hT : ContinuousOn T K)
    (w : Y → ℝ) (hw : Continuous w) (hpos : ∀ x ∈ K, 0 < w (T x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : X × Ω → Y,
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ∀ x ∈ K, ∀ ω, 0 < w (F (x, ω)) := by
  obtain ⟨δ, hδ, hh⟩ := exists_positive_composition_threshold K hK T hT w hw hpos
  exact ⟨δ, hδ, fun F hF x hx ω => hh (fun y => F (y, ω)) (fun y hy => hF y hy ω) x hx⟩

end LeanShared.PositiveWeightRobustness
