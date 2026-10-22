module
public import LeanShared.Dynamics.HyperbolicEntireOrbitSeparation
public import LeanShared.Dynamics.BilateralInvariantOrbit
public import Mathlib.Tactic.Linarith

/-! Expansivity is proved from actual compact hyperbolic basic-set data.
No expansivity, nonlinear chart, shadowing, or adapted cocycle certificate is
assumed. The stronger ambient version also permits the second point outside
the invariant set. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
open LeanShared.BilateralHomeomorphismOrbit

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_ambient_expansivity_radius
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Λ, ∀ y : M,
      (∀ j : ℕ, dist ((T : M → M)^[j] x) ((T : M → M)^[j] y) ≤ c ∧
        dist ((T.symm : M → M)^[j] x) ((T.symm : M → M)^[j] y) ≤ c) → x = y := by
  obtain ⟨N, _positiveN, η, positiveη, separates⟩ := b.exists_entire_orbit_separation forward inverse
  refine ⟨η / 2, by linarith, fun x hx y close => ?_⟩
  let reference : ℤ → Λ := fun n =>
    ⟨BilateralHomeomorphismOrbit.orbit (T^N) x n, pow_orbit_mem T Λ b.hyperbolic.invariant x hx N n⟩
  have referenceStep : ∀ n, (T^N) (reference (n + 1)).val = (reference n).val :=
    fun n => step (T^N) x n
  have actualStep : ∀ n, (T^N) (BilateralHomeomorphismOrbit.orbit (T^N) y (n + 1)) = BilateralHomeomorphismOrbit.orbit (T^N) y n :=
    fun n => step (T^N) y n
  have nearby : ∀ n, dist (reference n).val (BilateralHomeomorphismOrbit.orbit (T^N) y n) < η := by
    intro n
    exact (pow_dist_le T N x y (η / 2) (fun j => (close j).1) (fun j => (close j).2) n).trans_lt
      (by linarith)
  have same := separates reference referenceStep (BilateralHomeomorphismOrbit.orbit (T^N) y) actualStep nearby 0
  have base : y = x := by simpa only [reference, BilateralHomeomorphismOrbit.zero] using same
  exact base.symm

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_expansivity_radius
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Λ, ∀ y ∈ Λ,
      (∀ j : ℕ, dist ((T : M → M)^[j] x) ((T : M → M)^[j] y) ≤ c ∧
        dist ((T.symm : M → M)^[j] x) ((T.symm : M → M)^[j] y) ≤ c) → x = y := by
  obtain ⟨c, positive, expansive⟩ := b.exists_ambient_expansivity_radius forward inverse
  exact ⟨c, positive, fun x hx y _hy close => expansive x hx y close⟩

end LeanShared.HyperbolicBasicSet
