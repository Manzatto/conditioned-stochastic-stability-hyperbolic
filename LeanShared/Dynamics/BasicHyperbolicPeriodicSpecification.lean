module

public import LeanShared.Dynamics.BasicHyperbolicClosing
public import LeanShared.Dynamics.BasicHyperbolicForwardSpecification

/-! Actual periodic specification with a uniform transition length. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
open BilateralHomeomorphismOrbit
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

set_option maxHeartbeats 1800000 in
theorem BasicData.periodic_specification (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (mixing : MixingOn T Λ) (ε : ℝ) (positiveε : 0 < ε) :
    ∃ gap : ℕ, 0 < gap ∧ ∀ n : ℕ, ∀ x ∈ Λ,
      ∃ z ∈ Λ, (T : M → M)^[n + gap] z = z ∧
        ∀ j ≤ n, dist ((T : M → M)^[j] z) ((T : M → M)^[j] x) < ε := by
  obtain ⟨η, positiveη, closes⟩ := b.closing forward inverse (ε / 2) (by positivity)
  let δ := min (ε / 2) (η / 3)
  have positiveδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨gap, positiveGap, traces⟩ :=
    b.finite_specification forward (inverse.mdifferentiable one_ne_zero) mixing δ positiveδ
  refine ⟨gap, positiveGap, fun n x hx => ?_⟩
  let length : ℕ → ℕ := fun i => if i = 0 then n else 0
  let points : ℕ → Λ := fun _ => ⟨x, hx⟩
  obtain ⟨q, near⟩ := traces length points 1
  have first (j : ℕ) (hj : j ≤ n) :
      dist ((T : M → M)^[j] q.val) ((T : M → M)^[j] x) < δ := by
    have estimate := near 0 (by omega) j (show j ≤ length 0 by simpa [length] using hj)
    simpa only [FiniteOrbitWordAssembly.offset, Finset.range_zero, Finset.sum_empty,
      zero_add, points] using estimate
  have last : dist ((T : M → M)^[n + gap] q.val) x < δ := by
    have estimate := near 1 (by omega) 0 (by simp [length])
    simpa [FiniteOrbitWordAssembly.offset, length, points] using estimate
  have nearReturn : dist ((T : M → M)^[n + gap] q.val) q.val < η := by
    have start := first 0 (by omega)
    simp only [Function.iterate_zero_apply] at start
    have triangle := dist_triangle ((T : M → M)^[n + gap] q.val) x q.val
    have δsmall : δ ≤ η / 3 := min_le_right _ _
    rw [dist_comm x q.val] at triangle
    linarith
  obtain ⟨z, hz, fixed, close⟩ := closes (n + gap) (by omega) q.val q.property nearReturn
  refine ⟨z, hz, fixed, fun j hj => ?_⟩
  have a := close j (by omega)
  have c := first j hj
  have triangle := dist_triangle ((T : M → M)^[j] z) ((T : M → M)^[j] q.val)
    ((T : M → M)^[j] x)
  have δsmall : δ ≤ ε / 2 := min_le_left _ _
  linarith

end LeanShared.HyperbolicBasicSet
