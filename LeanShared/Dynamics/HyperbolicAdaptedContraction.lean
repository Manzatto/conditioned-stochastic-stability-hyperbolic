module
public import LeanShared.Dynamics.HyperbolicAdaptedForms
public import LeanShared.Geometry.ReversedInvariantTangentDistribution

/-! The finite adapted form contracts the actual stable derivative and actual
inverse-unstable derivative in one step. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedContraction
open HyperbolicAdaptedForms HyperbolicFiniteAdaptedEnergy
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem projection_stable (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (x : M) (hx : x ∈ Λ) (v : TangentSpace (𝓘(ℝ, E)) x) (hv : v ∈ h.stable x) :
    h.projection x v = v := by
  rw [← h.projection_range x hx] at hv
  obtain ⟨w, rfl⟩ := hv
  exact congrArg (fun L => L w) (h.projection_idempotent x hx)

theorem projection_unstable (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (x : M) (hx : x ∈ Λ) (v : TangentSpace (𝓘(ℝ, E)) x) (hv : v ∈ h.unstable x) :
    h.projection x v = 0 := by
  rwa [← h.projection_kernel x hx] at hv

theorem stable_self (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (a : ℝ) (N : ℕ) (x : M) (hx : x ∈ Λ)
    (v : TangentSpace (𝓘(ℝ, E)) x) (hv : v ∈ h.stable x) :
    splitForm T T.symm h.projection a N x v v = iterateEnergy T a N x v := by
  rw [splitForm_self, projection_stable h x hx v hv, sub_self]
  simp [iterateEnergy, FiniteAdaptedEnergy.energy]

theorem unstable_self (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (a : ℝ) (N : ℕ) (x : M) (hx : x ∈ Λ)
    (v : TangentSpace (𝓘(ℝ, E)) x) (hv : v ∈ h.unstable x) :
    splitForm T T.symm h.projection a N x v v = iterateEnergy T.symm a N x v := by
  rw [splitForm_self, projection_unstable h x hx v hv, sub_zero]
  simp [iterateEnergy, FiniteAdaptedEnergy.energy]

theorem exists_one_step [FiniteDimensional ℝ E] (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (slack : h.contraction < a) :
    ∃ N : ℕ, 0 < N ∧
      (∀ x ∈ Λ, ∀ v ∈ h.stable x,
        splitForm T T.symm h.projection a N (T x)
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v)
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v) ≤
        a ^ 2 * splitForm T T.symm h.projection a N x v v) ∧
      (∀ x ∈ Λ, ∀ v ∈ h.unstable x,
        splitForm T T.symm h.projection a N (T.symm x)
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x v)
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x v) ≤
        a ^ 2 * splitForm T T.symm h.projection a N x v v) := by
  obtain ⟨N, length, Bs, Bu, _, _, stable, unstable⟩ :=
    HyperbolicFiniteAdaptedEnergy.HyperbolicData.exists_two_sided_energy
      h forward backward a slack
  have inverseInvariant := ReversedInvariantTangentDistribution.invariant T
    (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero)
    Λ h.invariant h.unstable h.unstable_invariant
  refine ⟨N, length, ?_, ?_⟩
  · intro x hx v hv
    have image : T x ∈ Λ := h.invariant ▸ mem_image_of_mem T hx
    have member : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v ∈ h.stable (T x) := by
      rw [← h.stable_invariant x hx]
      exact ⟨v, hv, rfl⟩
    rw [stable_self h a N (T x) image _ member, stable_self h a N x hx v hv]
    exact (stable x hx v hv).2.2
  · intro x hx v hv
    have image : T.symm x ∈ Λ := by
      obtain ⟨y, hy, equal⟩ := h.invariant.symm ▸ hx
      simpa only [← equal, Homeomorph.symm_apply_apply] using hy
    have member : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm x v ∈ h.unstable (T.symm x) := by
      rw [← inverseInvariant x hx]
      exact ⟨v, hv, rfl⟩
    rw [unstable_self h a N (T.symm x) image _ member, unstable_self h a N x hx v hv]
    exact (unstable x hx v hv).2.2

end LeanShared.HyperbolicAdaptedContraction
