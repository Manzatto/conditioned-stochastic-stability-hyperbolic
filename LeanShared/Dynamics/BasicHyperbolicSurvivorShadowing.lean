module

public import LeanShared.Dynamics.BasicHyperbolicFiniteNearShadowing
public import LeanShared.Dynamics.FiniteSurvivorCoreTracking

/-! Fixed transient ends are sufficient to shadow every surviving middle
segment by one basic-set orbit, uniformly in its length. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff

theorem BasicData.survivor_shadowing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (ε:ℝ) (positiveε:0<ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ n : ℕ, ∀ y : M,
      (∀ j ≤ n+2*L, (T : M → M)^[j] y ∈ closure V) →
      ∃ x : Λ, ∀ j ≤ n,
        dist ((T : M → M)^[j] x.val) ((T : M → M)^[L+j] y) < ε := by
  obtain ⟨δ, positiveδ, shadow⟩ := b.finite_near_shadowing forward inverse ε positiveε
  have core : isolatedCore T (closure V) ⊆ Metric.thickening δ Λ := by
    rw [← b.isolated]
    exact Metric.self_subset_thickening positiveδ Λ
  obtain ⟨L, positiveL, capture⟩ := exists_uniform_middle_core_neighborhood T
    isClosed_closure.isCompact Metric.isOpen_thickening core
  refine ⟨L, positiveL, fun n y survives => ?_⟩
  have near (j : ℕ) (hj : j ≤ n) :
      (T : M → M)^[j] ((T : M → M)^[L] y) ∈ Metric.thickening δ Λ := by
    rw [← Function.iterate_add_apply, Nat.add_comm j L]
    exact capture n y survives j hj
  obtain ⟨x, traces⟩ := shadow n ((T : M → M)^[L] y) near
  refine ⟨x, fun j hj => ?_⟩
  simpa only [← Function.iterate_add_apply, Nat.add_comm j L] using traces j hj

end LeanShared.HyperbolicBasicSet
