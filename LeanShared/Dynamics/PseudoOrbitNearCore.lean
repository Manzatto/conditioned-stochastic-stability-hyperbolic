module
public import LeanShared.Dynamics.EntireOrbitInCore
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Compactness.Compact

/-! Pseudo-orbits in a closed isolating set stay near its isolated core. For a
homeomorphism of a compact metric space and a closed set `K`, every bilateral pseudo-orbit
in `K` with sufficiently small jumps is uniformly within any prescribed distance of the
isolated core `isolatedCore T K`. Compactness of `ℤ → X` and a cluster point argument:
the limit of shifted counterexamples would be an entire orbit in `K` at positive
distance from the core. -/
public noncomputable section
open Set Filter Metric
open scoped Topology
namespace LeanShared.PseudoOrbitNearCore

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem near_core (T : X ≃ₜ X) (K : Set X) (hK : IsClosed K) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℤ → X, (∀ n, y n ∈ K) →
      (∀ n, dist (T (y (n + 1))) (y n) < δ) →
      ∀ n, infDist (y n) (isolatedCore T K) < η := by
  by_contra contra
  push Not at contra
  -- counterexamples for δ = 1/(k+1), shifted so that the bad time is zero
  have bad (k : ℕ) : ∃ z : ℤ → X, (∀ n, z n ∈ K) ∧
      (∀ n, dist (T (z (n + 1))) (z n) < 1 / ((k : ℝ) + 1)) ∧
      η ≤ infDist (z 0) (isolatedCore T K) := by
    obtain ⟨y, inside, step, n, far⟩ := contra (1 / ((k : ℝ) + 1)) (by positivity)
    refine ⟨fun j => y (n + j), fun j => inside _, fun j => ?_, by simpa only [add_zero] using far⟩
    simpa only [← add_assoc] using step (n + j)
  choose z inside step far using bad
  obtain ⟨w, -, cluster⟩ := (isCompact_univ (X := ℤ → X)).exists_clusterPt
    (f := map z atTop) (by simp)
  -- closed conditions pass to the cluster point
  have closed_mem (C : Set (ℤ → X)) (hC : IsClosed C) (eventually : ∀ᶠ k in atTop, z k ∈ C) :
      w ∈ C := by
    have : ClusterPt w (𝓟 C) := cluster.mono (by
      rw [le_principal_iff]
      exact eventually)
    exact hC.closure_eq ▸ mem_closure_iff_clusterPt.mpr this
  have inK (n : ℤ) : w n ∈ K :=
    closed_mem {v | v n ∈ K} (hK.preimage (continuous_apply n))
      (Eventually.of_forall fun k => inside k n)
  have orbit (n : ℤ) : T (w (n + 1)) = w n := by
    apply dist_le_zero.mp
    apply le_of_forall_pos_le_add
    intro ε hε
    rw [zero_add]
    have closedSet : IsClosed {v : ℤ → X | dist (T (v (n + 1))) (v n) ≤ ε} :=
      isClosed_le ((T.continuous.comp (continuous_apply (n + 1))).dist (continuous_apply n))
        continuous_const
    apply closed_mem _ closedSet
    obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop k0] with k hk
    have : 1 / ((k : ℝ) + 1) ≤ 1 / ((k0 : ℝ) + 1) := by
      gcongr
    exact ((step k n).trans_le this).le.trans hk0.le
  have farW : η ≤ infDist (w 0) (isolatedCore T K) :=
    closed_mem {v | η ≤ infDist (v 0) (isolatedCore T K)}
      (isClosed_le continuous_const ((continuous_infDist_pt _).comp (continuous_apply 0)))
      (Eventually.of_forall far)
  have core : w 0 ∈ isolatedCore T K :=
    BilateralHomeomorphismOrbit.mem_isolatedCore T K w orbit inK 0
  rw [infDist_zero_of_mem core] at farW
  linarith

end LeanShared.PseudoOrbitNearCore
