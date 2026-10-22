module

public import LeanShared.Dynamics.BasicHyperbolicFiniteShadowing
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-! Every sufficiently near-core finite genuine orbit segment is uniformly
shadowed by a single orbit in the actual basic set, independently of length. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff

set_option maxHeartbeats 1600000 in
theorem BasicData.finite_near_shadowing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (ε:ℝ) (positiveε:0<ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ y : M,
      (∀ j ≤ n, (T : M → M)^[j] y ∈ Metric.thickening δ Λ) →
      ∃ x : Λ, ∀ j ≤ n, dist ((T : M → M)^[j] x.val) ((T : M → M)^[j] y) < ε := by
  obtain ⟨η, positiveη, shadow⟩ := b.finite_shadowing forward inverse (ε/2) (by positivity)
  obtain ⟨τ, positiveτ, uniform⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous T.continuous)
    (η/2) (by positivity)
  let δ := min (ε/2) (min τ (η/2))
  have positiveδ : 0 < δ := lt_min (by positivity) (lt_min positiveτ (by positivity))
  refine ⟨δ, positiveδ, fun n y near => ?_⟩
  have witnesses (i : Fin (n+1)) : ∃ x ∈ Λ, dist ((T : M → M)^[n-i.val] y) x < δ :=
    Metric.mem_thickening_iff.mp (near (n-i.val) (Nat.sub_le _ _))
  choose point member close using witnesses
  let p : Fin (n+1) → Λ := fun i => ⟨point i, member i⟩
  have pseudo (j : ℕ) (hj : j < n) :
      dist (T (p ⟨j+1, by omega⟩).val) (p ⟨j, by omega⟩).val < η := by
    have first : dist (T (p ⟨j+1, by omega⟩).val)
        (T ((T : M → M)^[n-(j+1)] y)) < η/2 := by
      apply uniform
      simpa only [p, dist_comm] using
        (close ⟨j+1, by omega⟩).trans_le ((min_le_right (ε/2) _).trans (min_le_left τ (η/2)))
    have last : dist ((T : M → M)^[n-j] y) (p ⟨j, by omega⟩).val < η/2 :=
      (close ⟨j, by omega⟩).trans_le ((min_le_right (ε/2) _).trans (min_le_right τ (η/2)))
    have same : T ((T : M → M)^[n-(j+1)] y) = (T : M → M)^[n-j] y := by
      rw [show n-j = n-(j+1)+1 by omega, Function.iterate_succ_apply']
    rw [same] at first
    exact (dist_triangle _ _ _).trans_lt (by linarith)
  obtain ⟨orbit, orbitStep, shadows⟩ := shadow n p pseudo
  have iterate (j : ℕ) (k : ℤ) : (T : M → M)^[j] (orbit k).val = (orbit (k-j)).val := by
    induction j with
    | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, sub_zero]
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      have step := orbitStep (k - (j+1))
      rw [show k - (j+1) + 1 = k-j by omega] at step
      simpa only [Nat.cast_add, Nat.cast_one] using step
  refine ⟨orbit n, fun j hj => ?_⟩
  have shadowAt := shadows ⟨n-j, by omega⟩
  have nearAt := close ⟨n-j, by omega⟩
  have index : n-(n-j)=j := by omega
  simp only [index] at nearAt
  have castIndex : (n : ℤ) - (j : ℤ) = ((n-j : ℕ) : ℤ) := by omega
  rw [iterate, castIndex]
  have second : dist (p ⟨n-j, by omega⟩).val ((T : M → M)^[j] y) < ε/2 :=
    (by simpa only [p, dist_comm] using nearAt.trans_le (min_le_left (ε/2) (min τ (η/2))))
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end LeanShared.HyperbolicBasicSet
