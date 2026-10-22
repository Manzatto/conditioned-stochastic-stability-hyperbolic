module
public import LeanShared.Dynamics.GibbsUpperEntropyEnergy
public import LeanShared.Dynamics.ExpansivePressureLowerVariational
public import LeanShared.Dynamics.SmallBoundaryPartition

/-! The SAME invariant probability constructed with the upper Gibbs bound
attains actual pressure. No equilibrium-state identification is a source. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem equilibrium_of_upper_gibbs
    (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (ε H P : ℝ) (positiveε : 0 < ε) (positiveH : 0 < H)
    (pressureP : pressure T φ univ = (P : EReal))
    (ν : ProbabilityMeasure X) (invariant : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (gibbs : ∀ n z U, IsOpen U →
      (∀ x ∈ U, ∀ j < n, dist (T^[j] x) (T^[j] z) < ε) →
      (ν : Measure X) U ≤ ENNReal.ofReal (H * Real.exp (orbitSum T φ n z - (n : ℝ) * P))) :
    IsEquilibriumState T φ univ ν := by
  obtain ⟨a, Q, _, mesh⟩ := exists_small_boundary_partition (ν : Measure X) ε positiveε
  have numeric := Q.free_energy_ge_of_upper_gibbs T T.continuous ν invariant φ
    ε H P positiveH mesh gibbs
  have lowerRate : (Q.entropyRate T (ν : Measure X) : EReal) ≤ entropy T (ν : Measure X) := by
    unfold entropy
    apply le_iSup_of_le a
    apply le_iSup_of_le Q
    rw [Q.liminf_eq_entropyRate T (ν : Measure X) invariant]
  have lower : (P : EReal) ≤ entropy T (ν : Measure X) +
      ((∫ x, φ x ∂(ν : Measure X) : ℝ) : EReal) := by
    calc
      _ ≤ ((Q.entropyRate T (ν : Measure X) + ∫ x, φ x ∂(ν : Measure X) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr numeric
      _ = _ := EReal.coe_add _ _
      _ ≤ _ := add_le_add lowerRate le_rfl
  have upper := entropy_free_energy_le_pressure T c positiveC expansive ν invariant φ
  refine ⟨T.continuous.measurable, invariant.map_eq, by simp, φ.integrable _, ?_⟩
  exact le_antisymm upper (pressureP ▸ lower)

end LeanShared.ThermodynamicDefinitions
