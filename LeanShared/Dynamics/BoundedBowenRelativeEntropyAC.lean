module

public import LeanShared.Dynamics.CenteredPartitionNeighbourhood
public import LeanShared.Dynamics.FiniteRelativeEntropySubsetBound
public import LeanShared.Dynamics.PartitionSingleEntropy
public import Mathlib.MeasureTheory.Measure.Regular

/-! Uniform finite relative entropy on actual long Bowen partitions
implies absolute continuity of invariant probabilities. Centered cells
approximate compact/open pairs; exponentially tilted finite tests force
any tested mass on a reference-null set to vanish. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 2400000 in
theorem absolutelyContinuous_of_bowen_relative_bound (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (μ ν : ProbabilityMeasure X)
    (invariantμ : MeasurePreserving T (μ : Measure X) μ)
    (invariantν : MeasurePreserving T (ν : Measure X) ν) (B : ℝ)
    (partitions : ∀ n : ℕ, ∃ k : ℕ, ∃ _positiveK : 0 < k,
      ∃ Q : MeasurablePartition (X := X) k,
        (∀ i, 0 < (ν : Measure X).real (Q.atom i)) ∧
        (∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i →
          ∀ j ≤ n, dist (T^[j] x) (T^[j] y) ≤ c) ∧
        (∑ i, (μ : Measure X).real (Q.atom i) * Real.log
          ((μ : Measure X).real (Q.atom i) / (ν : Measure X).real (Q.atom i))) ≤ B) :
    (μ : Measure X) ≪ (ν : Measure X) := by
  intro E zero
  by_contra nonzero
  let F := toMeasurable (ν : Measure X) E
  have measurableF : MeasurableSet F := measurableSet_toMeasurable (ν : Measure X) E
  have zeroF : (ν : Measure X) F = 0 := by simpa only [F, measure_toMeasurable] using zero
  have nonzeroF : (μ : Measure X) F ≠ 0 := by
    intro impossible
    exact nonzero (measure_mono_null (subset_toMeasurable (ν : Measure X) E) impossible)
  obtain ⟨K, subK, compactK, positiveK⟩ := measurableF.exists_lt_isCompact_of_ne_top
    (measure_ne_top (μ : Measure X) F) (pos_iff_ne_zero.mpr nonzeroF)
  have zeroK : (ν : Measure X) K = 0 := measure_mono_null subK zeroF
  have realK : 0 < (μ : Measure X).real K :=
    ENNReal.toReal_pos positiveK.ne' (measure_ne_top (μ : Measure X) K)
  let t := (|B + Real.log 2| + 1) / (μ : Measure X).real K
  have positiveT : 0 < t := by dsimp [t]; positivity
  have smallK : (ν : Measure X) K < ENNReal.ofReal (Real.exp (-t)) := by
    rw [zeroK]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  obtain ⟨U, subU, openU, smallU⟩ := K.exists_isOpen_lt_of_lt _ smallK
  have realSmallU : (ν : Measure X).real U < Real.exp (-t) := by
    have bound := (ENNReal.toReal_lt_toReal (measure_ne_top (ν : Measure X) U) ENNReal.ofReal_ne_top).mpr smallU
    simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using bound
  obtain ⟨N, detects⟩ := exists_centered_partition_union T c expansive K U compactK openU subU
  obtain ⟨k, hk, Q, positiveQ, mesh, relative⟩ := partitions (2 * N)
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨s, covers, contained⟩ := detects k Q mesh
  let R := fun i => ((T.symm : X → X)^[N]) ⁻¹' Q.atom i
  have measurableR (i : Fin k) : MeasurableSet (R i) :=
    (Q.measurable i).preimage (T.symm.continuous.measurable.iterate N)
  have disjointR : PairwiseDisjoint (s : Set (Fin k)) R := by
    intro i _ j _ different
    exact (Q.disjoint different).preimage _
  have inverseμ : MeasurePreserving T.symm (μ : Measure X) μ :=
    MeasurePreserving.symm T.toMeasurableEquiv invariantμ
  have inverseν : MeasurePreserving T.symm (ν : Measure X) ν :=
    MeasurePreserving.symm T.toMeasurableEquiv invariantν
  have massμ (i : Fin k) : (μ : Measure X).real (R i) = (μ : Measure X).real (Q.atom i) := by
    simp only [measureReal_def, R, (inverseμ.iterate N).measure_preimage (Q.measurable i).nullMeasurableSet]
  have massν (i : Fin k) : (ν : Measure X).real (R i) = (ν : Measure X).real (Q.atom i) := by
    simp only [measureReal_def, R, (inverseν.iterate N).measure_preimage (Q.measurable i).nullMeasurableSet]
  have lower : (μ : Measure X).real K ≤ ∑ i ∈ s, (μ : Measure X).real (Q.atom i) := by
    have bound := (measureReal_mono (μ := (μ : Measure X)) covers (measure_ne_top (μ : Measure X) _)).trans
      (measureReal_biUnion_finset_le s R)
    simpa only [massμ] using bound
  have small : (∑ i ∈ s, (ν : Measure X).real (Q.atom i)) ≤ Real.exp (-t) := by
    have equality := measureReal_biUnion_finset (μ := (ν : Measure X)) disjointR (fun i _ => measurableR i) (fun i _ => measure_ne_top (ν : Measure X) (R i))
    simp only [massν] at equality
    rw [← equality]
    exact (measureReal_mono (μ := (ν : Measure X)) contained (measure_ne_top (ν : Measure X) _)).trans realSmallU.le
  have test := LeanShared.FiniteRelativeEntropy.subset_mass_bound
    (fun i => (μ : Measure X).real (Q.atom i)) (fun i => (ν : Measure X).real (Q.atom i))
    s t (fun _ => measureReal_nonneg) positiveQ
    (Q.atom_masses_total (μ : Measure X)) (Q.atom_masses_total (ν : Measure X)) small
  have upper : t * (μ : Measure X).real K ≤ B + Real.log 2 :=
    (mul_le_mul_of_nonneg_left lower positiveT.le).trans (test.trans (add_le_add relative le_rfl))
  have exactT : t * (μ : Measure X).real K = |B + Real.log 2| + 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ realK.ne'
  rw [exactT] at upper
  linarith [le_abs_self (B + Real.log 2)]

end LeanShared.ThermodynamicDefinitions
