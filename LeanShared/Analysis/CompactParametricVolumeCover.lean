module
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Compact

/-! Finite rectangular covers turn genuine local uniform control-volume
estimates into one estimate for every state of a compact state space. -/
public noncomputable section
namespace LeanShared.CompactParametricVolumeCover
open Set MeasureTheory
open scoped ENNReal BigOperators

theorem exists_uniform_bound
    {X A Y : Type*} [TopologicalSpace X] [TopologicalSpace A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Y]
    (ρ : Measure A) (σ : Measure Y) {K : Set X} {L : Set A}
    (compactK : IsCompact K) (compactL : IsCompact L) {f : X × A → Y}
    (measurableF : ∀ x ∈ K, AEMeasurable (fun a => f (x, a)) (ρ.restrict L))
    (localBound : ∀ x ∈ K, ∀ a ∈ L,
      ∃ U : Set X, ∃ V : Set A, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ a ∈ V ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ y ∈ U, ∀ B : Set Y, MeasurableSet B →
        ρ ((fun b => f (y, b)) ⁻¹' B ∩ V) ≤ C * σ B) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x ∈ K, (ρ.restrict L).map (fun a => f (x, a)) ≤ C • σ := by
  classical
  have patches (p : K × L) := localBound p.1.val p.1.property p.2.val p.2.property
  choose U V openU openV state control C finiteC bound using patches
  have cover : K ×ˢ L ⊆ ⋃ p : K × L, U p ×ˢ V p := by
    intro z hz
    exact mem_iUnion.mpr ⟨(⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩), state _, control _⟩
  obtain ⟨indices, subcover⟩ := (compactK.prod compactL).elim_finite_subcover
    (fun p => U p ×ˢ V p) (fun p => (openU p).prod (openV p)) cover
  refine ⟨∑ p ∈ indices, C p, ?_, ?_⟩
  · exact (ENNReal.sum_lt_top.mpr (fun p _ => lt_top_iff_ne_top.mpr (finiteC p))).ne
  · intro x hx
    apply Measure.le_iff.mpr
    intro B measurableB
    rw [Measure.map_apply_of_aemeasurable (measurableF x hx) measurableB,
      Measure.restrict_apply' compactL.measurableSet, Measure.smul_apply, smul_eq_mul]
    calc
      ρ ((fun a => f (x, a)) ⁻¹' B ∩ L) ≤
          ρ (⋃ p ∈ indices, (fun a => f (x, a)) ⁻¹' B ∩
            (if x ∈ U p then V p else ∅)) := by
        apply measure_mono
        intro a ha
        obtain ⟨p, hp⟩ := mem_iUnion.mp (subcover (show (x, a) ∈ K ×ˢ L from ⟨hx, ha.2⟩))
        obtain ⟨inIndices, stateControl⟩ := mem_iUnion.mp hp
        exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨inIndices, ha.1,
          by simpa only [ite_eq_left stateControl.1] using stateControl.2⟩⟩
      _ ≤ ∑ p ∈ indices, ρ ((fun a => f (x, a)) ⁻¹' B ∩
          (if x ∈ U p then V p else ∅)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ p ∈ indices, C p * σ B := by
        apply Finset.sum_le_sum
        intro p _
        by_cases hp : x ∈ U p
        · simpa only [ite_eq_left hp] using bound p x hp B measurableB
        · simp only [ite_eq_right hp, inter_empty, measure_empty]
          exact zero_le
      _ = (∑ p ∈ indices, C p) * σ B := (Finset.sum_mul _ _ _).symm

end LeanShared.CompactParametricVolumeCover
