module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicSpecification
public import LeanShared.Dynamics.OrbitEnergyConcatenation

/-! Actual periodic orbits preserve weighted separated orbit sums up to a uniform transition cost. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
open BilateralHomeomorphismOrbit ThermodynamicDefinitions
open scoped BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

set_option maxHeartbeats 1800000 in
theorem BasicData.weighted_periodic_shadowing (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (mixing : MixingOn T Λ) (ε : ℝ) (positiveε : 0 < ε)
    (φ : M → ℝ) (B D : ℝ) (lower : ∀ x ∈ Λ, -B ≤ φ x)
    (bowen : ∀ n : ℕ, ∀ x ∈ Λ, ∀ y ∈ Λ,
      (∀ j ≤ n, dist ((T : M → M)^[j] x) ((T : M → M)^[j] y) < ε) →
      |orbitSum T φ (n + 1) x - orbitSum T φ (n + 1) y| ≤ D) :
    ∃ gap : ℕ, 0 < gap ∧ ∀ n : ℕ, ∀ s : Finset M,
      Separated T Λ (n + 1) (3 * ε) s →
      ∃ q : Finset M, Separated T Λ (n + gap) ε q ∧
        (∀ z ∈ q, (T : M → M)^[n + gap] z = z) ∧
        Real.exp (-(D + (gap - 1 : ℕ) * B)) *
          (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) ≤
          ∑ z ∈ q, Real.exp (orbitSum T φ (n + gap) z) := by
  classical
  have invariant : MapsTo T Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  obtain ⟨gap, positiveGap, shadows⟩ := b.periodic_specification forward inverse mixing ε positiveε
  refine ⟨gap, positiveGap, fun n s separated => ?_⟩
  have traces (x : s) : ∃ z ∈ Λ, (T : M → M)^[n + gap] z = z ∧
      ∀ j ≤ n, dist ((T : M → M)^[j] z) ((T : M → M)^[j] x.val) < ε :=
    shadows n x.val (separated.1 x.val x.property)
  choose z member fixed trace using traces
  have separates (x y : s) (different : x ≠ y) :
      ∃ j < n + gap, ε ≤ dist ((T : M → M)^[j] (z x)) ((T : M → M)^[j] (z y)) := by
    obtain ⟨j, hj, apart⟩ := separated.2 x.val x.property y.val y.property
      (fun same => different (Subtype.ext same))
    refine ⟨j, by omega, ?_⟩
    have first := trace x j (by omega)
    have second := trace y j (by omega)
    have triangle := dist_triangle4 ((T : M → M)^[j] x.val) ((T : M → M)^[j] (z x))
      ((T : M → M)^[j] (z y)) ((T : M → M)^[j] y.val)
    rw [dist_comm] at first
    linarith
  have injective : Function.Injective z := by
    intro x y same
    by_contra different
    obtain ⟨j, _, apart⟩ := separates x y different
    rw [same, dist_self] at apart
    exact (not_le_of_gt positiveε) apart
  refine ⟨Finset.univ.image z, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact member a
  · intro x hx y hy different
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hy
    exact separates a c (fun same => different (congrArg z same))
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact fixed a
  · rw [Finset.sum_image (fun _ _ _ _ same => injective same)]
    have sourceSum := Finset.sum_coe_sort s (fun x => Real.exp (orbitSum T φ (n + 1) x))
    rw [← sourceSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have first := bowen n (z x) (member x) x.val (separated.1 x.val x.property) (trace x)
    have tail := orbitSum_lower T φ Λ invariant B lower (gap - 1)
      (invariant.iterate (n + 1) (member x))
    have size : n + gap = (n + 1) + (gap - 1) := by omega
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [size, orbitSum_add T φ (n + 1) (gap - 1) (z x)]
    have energy := (abs_le.mp first).1
    linarith

end LeanShared.HyperbolicBasicSet
