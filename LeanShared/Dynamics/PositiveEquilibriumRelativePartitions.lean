module

public import LeanShared.Dynamics.ConstructedBowenVoronoi
public import LeanShared.Dynamics.EquilibriumPartitionRelativeBound

/-! For an arbitrary equilibrium, actual separated spanning orbits
construct finite partitions with uniformly bounded relative entropy
against the Gibbs law, at every horizon. No Gibbs estimate on the tested
equilibrium or supplied partition is assumed. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1800000 in
theorem exists_positive_equilibrium_relative_partitions (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (μ ν : ProbabilityMeasure X) (state : IsEquilibriumState T φ univ μ)
    (P A D ε : ℝ) (pressureP : pressure T φ univ = (P : EReal))
    (positiveA : 0 < A) (positive : 0 < ε) (coarse : 2 * ε ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (lower : ∀ n y, ENNReal.ofReal (A * Real.exp (orbitSum T φ n y - (n : ℝ) * P)) ≤
      (ν : Measure X) {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ε / 3}) :
    ∀ n : ℕ, ∃ k : ℕ, ∃ _positiveK : 0 < k, ∃ Q : MeasurablePartition (X := X) k,
      (∀ i, 0 < (ν : Measure X).real (Q.atom i)) ∧
      (∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i →
        ∀ j ≤ n, dist (T^[j] x) (T^[j] y) < 2 * ε) ∧
      (∑ i, (μ : Measure X).real (Q.atom i) * Real.log
        ((μ : Measure X).real (Q.atom i) / (ν : Measure X).real (Q.atom i))) ≤ D - Real.log A := by
  intro n
  obtain ⟨k, positiveK, centers, near, inside, mesh⟩ :=
    exists_bowen_voronoi T c positiveC expansive ε positive n
  let Q := bowenVoronoiPartition T T.continuous centers positiveK n
  refine ⟨k, positiveK, Q, ?_, mesh, ?_⟩
  · intro i
    have reference : ENNReal.ofReal (A * Real.exp (orbitSum T φ (n + 1) (centers i) - (n + 1 : ℕ) * P)) ≤
        (ν : Measure X) (Q.atom i) := by
      apply (lower (n + 1) (centers i)).trans
      exact measure_mono (fun x close => inside i x (fun j hj => close j (by omega)))
    have positiveMass : 0 < (ν : Measure X) (Q.atom i) :=
      (ENNReal.ofReal_pos.mpr (mul_pos positiveA (Real.exp_pos _))).trans_le reference
    exact ENNReal.toReal_pos positiveMass.ne' (measure_ne_top (ν : Measure X) (Q.atom i))
  · apply equilibrium_partition_relative_bound Q T c positiveC expansive φ μ ν state
      P A D pressureP positiveA (n + 1) (by omega) (fun i => orbitSum T φ (n + 1) (centers i))
    · intro i x y hx hy j hj
      exact (mesh i x y hx hy j (by omega)).le.trans coarse
    · intro i x member
      have distortion := bowen (n + 1) x (centers i) (fun j hj => near i x member j (by omega))
      have upper := (abs_le.mp distortion).2
      linarith
    · intro i
      apply (lower (n + 1) (centers i)).trans
      apply measure_mono
      intro x close
      exact inside i x (fun j hj => close j (by omega))

end LeanShared.ThermodynamicDefinitions
