module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Geometry.ComplementaryBundleEndomorphism
public import LeanShared.Geometry.ReversedInvariantTangentDistribution

/-! Reversing the genuine hyperbolic diffeomorphism swaps its actual stable
and unstable subspaces. The complementary projection and inverse tangent
invariance are derived; no second hyperbolic package is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Topology Bundle

set_option maxHeartbeats 1600000 in
def HyperbolicData.reversed
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    HyperbolicData (E := E) T.symm Λ := by
  have idempotent (x : M) (hx : x ∈ Λ) (v : TangentSpace (𝓘(ℝ, E)) x) :
      h.projection x (h.projection x v) = h.projection x v :=
    congrArg (fun P => P v) (h.projection_idempotent x hx)
  refine {
    compact := h.compact
    invariant := ?_
    stable := h.unstable
    unstable := h.stable
    complementary := fun x hx => (h.complementary x hx).symm
    projection := fun x => ContinuousLinearMap.id ℝ _ - h.projection x
    projection_range := ?_
    projection_kernel := ?_
    projection_idempotent := ?_
    continuous_splitting := ComplementaryBundleEndomorphism.continuousOn _ h.projection Λ h.continuous_splitting
    stable_invariant := ReversedInvariantTangentDistribution.invariant T forward inverse Λ h.invariant
      h.unstable h.unstable_invariant
    unstable_invariant := ReversedInvariantTangentDistribution.invariant T forward inverse Λ h.invariant
      h.stable h.stable_invariant
    constant := h.constant
    contraction := h.contraction
    constant_pos := h.constant_pos
    contraction_pos := h.contraction_pos
    contraction_lt_one := h.contraction_lt_one
    stable_bound := h.unstable_bound
    unstable_bound := h.stable_bound }
  · calc
      T.symm '' Λ = T.symm '' (T '' Λ) := congrArg (fun s => T.symm '' s) h.invariant.symm
      _ = Λ := by simp only [Set.image_image,Homeomorph.symm_apply_apply,Set.image_id']
  · intro x hx
    rw [← h.projection_kernel x hx]
    ext v
    constructor
    · rintro ⟨w,rfl⟩
      change h.projection x (w - h.projection x w) = 0
      rw [map_sub,idempotent x hx,sub_self]
    · intro hv
      refine ⟨v,?_⟩
      change v - h.projection x v = v
      change h.projection x v = 0 at hv
      rw [hv,sub_zero]
  · intro x hx
    rw [← h.projection_range x hx]
    ext v
    change (v - h.projection x v = 0) ↔ ∃ w, h.projection x w = v
    constructor
    · intro hv
      exact ⟨v,(sub_eq_zero.mp hv).symm⟩
    · rintro ⟨w,rfl⟩
      rw [idempotent x hx,sub_self]
  · intro x hx
    ext v
    change (v - h.projection x v) - h.projection x (v - h.projection x v) = v - h.projection x v
    rw [map_sub,idempotent x hx,sub_self,sub_zero]

end LeanShared.HyperbolicBasicSet
