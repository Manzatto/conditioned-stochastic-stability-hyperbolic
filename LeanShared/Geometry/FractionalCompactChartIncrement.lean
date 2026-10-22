module

public import LeanShared.Geometry.FractionalHolderCharts
public import LeanShared.Analysis.CompactLocalHolderNeighborhood
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual fractional manifold regularity supplies uniform Hölder increments
on every compact genuine chart patch. The neighborhood radius and constant
are constructed from local chart regularity and compactness. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem Regular.compact_chart_increment {f : M → F} {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (regular : Regular (E := E) (F := F) a f)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set M) (compact : IsCompact K) (inside : K ⊆ c.source) :
    ∃ r > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ v : E, ‖v‖ ≤ r →
      ‖f (c.symm (c x + v)) - f x‖ ≤ C * ‖v‖ ^ a := by
  have compactCenters : IsCompact (c '' K) :=
    compact.image_of_continuousOn (c.continuousOn.mono inside)
  obtain ⟨r, positiveR, C, nonnegativeC, bound⟩ :=
    CompactLocalHolder.bound_near_compact ha ha1.le (c '' K) c.target
      compactCenters c.open_target (by rintro _ ⟨x, hx, rfl⟩; exact c.map_source (inside hx))
      (fun y => f (c.symm y)) (fun y hy => by
        obtain ⟨W, openW, inW, _, A, nonnegativeA, holder⟩ :=
          local_holder_in_chart ha ha1 regular c hc y hy
        exact ⟨W, openW, inW, A, nonnegativeA, fun z hz w hw => by
          simpa only [dist_eq_norm] using holder z hz w hw⟩)
  refine ⟨r, positiveR, C, nonnegativeC, fun x hx v hv => ?_⟩
  have estimate := bound (c x) ⟨x, hx, rfl⟩ (c x + v)
    (by simpa only [dist_eq_norm, add_sub_cancel_left] using hv)
  simpa only [dist_eq_norm, add_sub_cancel_left, c.left_inv (inside hx)] using estimate

end LeanShared.FractionalManifoldRegularity
