module

public import LeanShared.Dynamics.ExpansivePartitionCoding
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp

/-! Compact separated cores of a finite Borel partition lose arbitrarily
little probability mass. -/
public noncomputable section
open Set Function MeasureTheory
open scoped ENNReal BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The compact cores are constructed by inner regularity, and their
complement is bounded for the actual probability measure. -/
theorem MeasurablePartition.exists_compact_cores {k : ℕ}
    (P : MeasurablePartition (X := X) k) (μ : ProbabilityMeasure X)
    (ε : ℝ) (positive : 0 < ε) :
    ∃ K : Fin k → Set X, (∀ i, K i ⊆ P.atom i) ∧ (∀ i, IsCompact (K i)) ∧
      (μ : Measure X).real (⋃ i, K i)ᶜ < ε := by
  have fraction : 0 < ε/(k+1 : ℝ) := div_pos positive (by positivity)
  have cores (i : Fin k) : ∃ K, K ⊆ P.atom i ∧ IsCompact K ∧
      (μ : Measure X) (P.atom i \ K) < ENNReal.ofReal (ε/(k+1 : ℝ)) :=
    (P.measurable i).exists_isCompact_sdiff_lt (measure_ne_top _ _)
      (ne_of_gt (ENNReal.ofReal_pos.mpr fraction))
  choose K subset compact small using cores
  have smallReal (i : Fin k) : (μ : Measure X).real (P.atom i \ K i) < ε/(k+1 : ℝ) := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top (μ : Measure X) _) ENNReal.ofReal_ne_top).mpr (small i)
    simpa only [Measure.real,ENNReal.toReal_ofReal fraction.le] using h
  have missing : (⋃ i, K i)ᶜ ⊆ ⋃ i, P.atom i \ K i := by
    intro x hx
    refine mem_iUnion.mpr ⟨P.label x,P.label_mem x,?_⟩
    exact fun member => hx (mem_iUnion.mpr ⟨P.label x,member⟩)
  refine ⟨K,subset,compact,?_⟩
  calc
    (μ : Measure X).real (⋃ i, K i)ᶜ ≤ (μ : Measure X).real (⋃ i, P.atom i \ K i) :=
      measureReal_mono missing
    _ ≤ ∑ i, (μ : Measure X).real (P.atom i \ K i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin k, ε/(k+1 : ℝ) := Finset.sum_le_sum (fun i _ => (smallReal i).le)
    _ < ε := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [←mul_div_assoc]
      apply (div_lt_iff₀ (show 0 < (k : ℝ)+1 by positivity)).mpr
      nlinarith

omit [CompactSpace X] [BorelSpace X] in
/-- Finitely many pairwise-disjoint compact cores have one common
strictly positive separation scale. Empty cores cause no exception. -/
theorem MeasurablePartition.compact_cores_separated {k : ℕ} [Nonempty X]
    (P : MeasurablePartition (X := X) k) (K : Fin k → Set X)
    (subset : ∀ i, K i ⊆ P.atom i) (compact : ∀ i, IsCompact (K i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, δ < dist x y := by
  classical
  have nonempty : Nonempty (Fin k) := ⟨P.label (Classical.arbitrary X)⟩
  let : Nonempty (Fin k) := nonempty
  have pairScale (p : Fin k × Fin k) : ∃ δ : ℝ, 0 < δ ∧
      (p.1 ≠ p.2 → ∀ x ∈ K p.1, ∀ y ∈ K p.2, δ < dist x y) := by
    by_cases equal : p.1=p.2
    · exact ⟨1,zero_lt_one,fun different => (different equal).elim⟩
    have disjoint : Disjoint (K p.1) (K p.2) :=
      (P.disjoint equal).mono (subset p.1) (subset p.2)
    obtain ⟨r,positive,separated⟩ := Metric.exists_pos_forall_lt_edist
      (compact p.1) (compact p.2).isClosed disjoint
    refine ⟨r,positive,fun _ x hx y hy => ?_⟩
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (edist_ne_top x y)).mpr (separated x hx y hy)
    simpa only [ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] using h
  choose r positive separated using pairScale
  let δ := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin k × Fin k)).Nonempty) r
  refine ⟨δ,(Finset.lt_inf'_iff _).mpr (fun p _ => positive p),?_⟩
  intro i j different x hx y hy
  exact (Finset.inf'_le r (Finset.mem_univ (i,j))).trans_lt (separated (i,j) different x hx y hy)

end LeanShared.ThermodynamicDefinitions
