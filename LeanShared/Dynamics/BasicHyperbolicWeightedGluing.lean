module
public import LeanShared.Dynamics.BasicHyperbolicSeparatedGluing
public import LeanShared.Dynamics.WeightedSeparatedOrbitGluing
public import LeanShared.Dynamics.OrbitEnergyConcatenation

/-! Actual mixing hyperbolic specification gives a product lower bound for
weighted separated orbit sums. All shadowing points and their separation
are constructed internally; the explicit loss counts the transition gap. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff BigOperators
open FiniteOrbitWordAssembly ThermodynamicDefinitions

set_option maxHeartbeats 2400000 in
theorem BasicData.weighted_separated_gluing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (mixing:MixingOn T Λ) (ε:ℝ) (positiveε:0<ε)
    (φ : M → ℝ) (B D : ℝ) (lower : ∀ x ∈ Λ, -B ≤ φ x)
    (bowen : ∀ n : ℕ, ∀ x ∈ Λ, ∀ y ∈ Λ,
      (∀ j ≤ n, dist (((T : M → M)^[j]) x) (((T : M → M)^[j]) y) < ε) →
      |orbitSum T φ (n + 1) x - orbitSum T φ (n + 1) y| ≤ D) :
    ∃ gap : ℕ, 0 < gap ∧ ∀ n m : ℕ, ∀ s t : Finset M,
      Separated T Λ (n + 1) (3 * ε) s → Separated T Λ (m + 1) (3 * ε) t →
      ∃ q : Finset M, Separated T Λ (n + gap + m + 1) ε q ∧
        Real.exp (-(2 * D + (gap - 1 : ℕ) * B)) *
          (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
          (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)) ≤
            ∑ z ∈ q, Real.exp (orbitSum T φ (n + gap + m + 1) z) := by
  classical
  have invariant : MapsTo T Λ Λ := by
    intro x hx
    rw [← b.hyperbolic.invariant]
    exact mem_image_of_mem T hx
  obtain ⟨gap, positiveGap, specification⟩ := b.finite_specification forward inverse mixing ε positiveε
  refine ⟨gap, positiveGap, fun n m s t first second => ?_⟩
  let I := {p : M × M // p ∈ s.product t}
  have traces (p : I) : ∃ z : Λ,
      (∀ j ≤ n, dist (((T : M → M)^[j]) z.val) (((T : M → M)^[j]) p.val.1) < ε) ∧
      ∀ j ≤ m, dist (((T : M → M)^[n + gap + j]) z.val)
        (((T : M → M)^[j]) p.val.2) < ε := by
    let length := fun i : ℕ => if i = 0 then n else m
    let points := fun i : ℕ => if i = 0 then
      (⟨p.val.1, first.1 _ (Finset.mem_product.mp p.property).1⟩ : Λ) else
      ⟨p.val.2, second.1 _ (Finset.mem_product.mp p.property).2⟩
    obtain ⟨z, trace⟩ := specification length points 1
    refine ⟨z, ?_, ?_⟩
    · intro j hj
      have estimate := trace 0 (by omega) j (show j ≤ length 0 by simpa only [length, ite_eq_left rfl] using hj)
      simpa only [offset, Finset.range_zero, Finset.sum_empty, zero_add, points, ite_eq_left rfl] using estimate
    · intro j hj
      have estimate := trace 1 (by omega) j (show j ≤ length 1 by simpa only [length, ite_eq_right Nat.one_ne_zero] using hj)
      simpa [offset, length, points] using estimate
  choose z firstTrace secondTrace using traces
  apply weighted_traced_pairs T Λ s t n m gap ε positiveε first second
    (fun p => (z p).val) (fun p => (z p).property) firstTrace secondTrace
    (fun x => Real.exp (orbitSum T φ (n + gap + m + 1) x))
    (fun x => Real.exp (orbitSum T φ (n + 1) x))
    (fun y => Real.exp (orbitSum T φ (m + 1) y))
    (Real.exp (-(2 * D + (gap - 1 : ℕ) * B)))
  intro p
  have firstEnergy := bowen n (z p).val (z p).property p.val.1
    (first.1 _ (Finset.mem_product.mp p.property).1) (firstTrace p)
  have secondEnergy := bowen m (((T : M → M)^[n + gap]) (z p).val)
    (invariant.iterate (n + gap) (z p).property) p.val.2
    (second.1 _ (Finset.mem_product.mp p.property).2) (fun j hj => by
      rw [← Function.iterate_add_apply, Nat.add_comm j (n + gap)]
      exact secondTrace p j hj)
  have energy := orbitSum_gluing_lower T φ Λ invariant B lower n m gap positiveGap
    p.val.1 p.val.2 (z p).val (z p).property D firstEnergy secondEnergy
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end LeanShared.HyperbolicBasicSet
