module
public import LeanShared.Dynamics.BasicHyperbolicForwardSpecification
public import LeanShared.Dynamics.SeparatedOrbitGluing

/-! Literal compact mixing hyperbolic basic data glue independent separated
orbit choices. The fixed transition length precedes both segment horizons
and both finite separated sets. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
open FiniteOrbitWordAssembly ThermodynamicDefinitions

set_option maxHeartbeats 1600000 in
theorem BasicData.separated_orbit_gluing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (mixing:MixingOn T Λ) (ε:ℝ) (positiveε:0<ε) :
    ∃ gap : ℕ, 0 < gap ∧ ∀ n m : ℕ, ∀ s t : Finset M,
      Separated T Λ (n + 1) (3 * ε) s → Separated T Λ (m + 1) (3 * ε) t →
      ∃ q : Finset M, Separated T Λ (n + gap + m + 1) ε q ∧
        q.card = s.card * t.card := by
  classical
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
  exact separated_traced_pairs T Λ s t n m gap ε positiveε first second
    (fun p => (z p).val) (fun p => (z p).property) firstTrace secondTrace

end LeanShared.HyperbolicBasicSet
