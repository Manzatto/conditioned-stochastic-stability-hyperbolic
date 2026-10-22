module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Analysis.ProjectionInvariantSplitting
public import LeanShared.Geometry.InvariantTangentDistributionIterates
public import LeanShared.Geometry.InvariantTangentDistributionInverse

/-! The actual stable projection commutes with all forward and backward
derivative cocycles. These identities follow from the two invariant tangent
subspaces in `HyperbolicData`; they are not extra splitting assumptions. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

private theorem from_invariant_subspaces (h : HyperbolicData (E := E) T Λ)
    (x y : M) (hx : x ∈ Λ) (hy : y ∈ Λ)
    (A : TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) y)
    (stable : (h.stable x).map A.toLinearMap = h.stable y)
    (unstable : (h.unstable x).map A.toLinearMap = h.unstable y) :
    (h.projection y).comp A = A.comp (h.projection x) := by
  have hp := congrArg ContinuousLinearMap.toLinearMap (h.projection_idempotent x hx)
  have hq := congrArg ContinuousLinearMap.toLinearMap (h.projection_idempotent y hy)
  have ranges : (h.projection x).toLinearMap.range.map A.toLinearMap ≤
      (h.projection y).toLinearMap.range := by
    rw [h.projection_range x hx, h.projection_range y hy, stable]
  have kernels : (h.projection x).toLinearMap.ker.map A.toLinearMap ≤
      (h.projection y).toLinearMap.ker := by
    rw [h.projection_kernel x hx, h.projection_kernel y hy, unstable]
  have equality := ProjectionInvariantSplitting.intertwines
    (h.projection x).toLinearMap (h.projection y).toLinearMap A.toLinearMap
    hp hq ranges kernels
  ext v
  exact congrArg (fun L => L v) equality

theorem HyperbolicData.projection_derivative_commutes
    (h : HyperbolicData (E := E) T Λ) (x : M) (hx : x ∈ Λ) :
    (h.projection (T x)).comp (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).comp (h.projection x) := by
  have hy : T x ∈ Λ := h.invariant ▸ mem_image_of_mem T hx
  exact from_invariant_subspaces h x (T x) hx hy _
    (h.stable_invariant x hx) (h.unstable_invariant x hx)

theorem HyperbolicData.projection_iterate_commutes
    (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (n : ℕ) (x : M) (hx : x ∈ Λ) :
    (h.projection ((T : M → M)^[n] x)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T : M → M)^[n]) x) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T : M → M)^[n]) x).comp (h.projection x) := by
  have preserves : MapsTo T Λ Λ := fun _ inside => h.invariant ▸ mem_image_of_mem T inside
  exact from_invariant_subspaces h x _ hx (preserves.iterate n hx) _
    (InvariantTangentDistributionIterates.map_iterate T forward Λ preserves
      h.stable h.stable_invariant n x hx)
    (InvariantTangentDistributionIterates.map_iterate T forward Λ preserves
      h.unstable h.unstable_invariant n x hx)

theorem HyperbolicData.projection_inverse_iterate_commutes
    (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (n : ℕ) (x : M) (hx : x ∈ Λ) :
    (h.projection ((T.symm : M → M)^[n] x)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm : M → M)^[n]) x) =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm : M → M)^[n]) x).comp (h.projection x) := by
  have preserves : MapsTo T.symm Λ Λ := by
    intro y inside
    rw [← h.invariant] at inside
    obtain ⟨z, hz, rfl⟩ := inside
    simpa only [T.symm_apply_apply] using hz
  have stable := InvariantTangentDistributionIterates.map_inverse T forward inverse Λ
    h.invariant h.stable h.stable_invariant
  have unstable := InvariantTangentDistributionIterates.map_inverse T forward inverse Λ
    h.invariant h.unstable h.unstable_invariant
  exact from_invariant_subspaces h x _ hx (preserves.iterate n hx) _
    (InvariantTangentDistributionIterates.map_iterate T.symm inverse Λ preserves
      h.stable stable n x hx)
    (InvariantTangentDistributionIterates.map_iterate T.symm inverse Λ preserves
      h.unstable unstable n x hx)

end LeanShared.HyperbolicBasicSet
