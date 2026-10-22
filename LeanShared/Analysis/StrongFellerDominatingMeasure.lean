module
public import Mathlib.Topology.Bases
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

/-! Setwise-continuous subprobability rows on a separable state space admit a
single finite dominating measure. It is constructed from dense-state rows. -/
public noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace LeanShared.StrongFellerDominatingMeasure
variable {X Y : Type*} [TopologicalSpace X] [SeparableSpace X] [MeasurableSpace Y]

theorem exists_finite (κ : X → Measure Y) [∀ x, IsFiniteMeasure (κ x)]
    (mass : ∀ x, κ x univ ≤ 1)
    (continuous_rows : ∀ B, MeasurableSet B → Continuous (fun x => (κ x).real B)) :
    ∃ μ : Measure Y, IsFiniteMeasure μ ∧ ∀ x, κ x ≪ μ := by
  classical
  rcases isEmpty_or_nonempty X with empty | nonempty
  · let _ : IsEmpty X := empty
    exact ⟨0,inferInstance,fun x => isEmptyElim x⟩
  let _ : Nonempty X := nonempty
  obtain ⟨d,dense⟩ := exists_dense_seq X
  let rows : ℕ → Measure Y := fun n => ((2 : ℝ≥0∞)⁻¹)^n • κ (d n)
  let μ := Measure.sum rows
  have total : μ univ ≤ (2 : ℝ≥0∞) := by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    calc
      _ ≤ ∑' n : ℕ, ((2 : ℝ≥0∞)⁻¹)^n := by
        apply ENNReal.tsum_le_tsum
        intro n
        change ((2 : ℝ≥0∞)⁻¹)^n*κ (d n) univ ≤ ((2 : ℝ≥0∞)⁻¹)^n
        exact mul_le_of_le_one_right' (mass (d n))
      _ = 2 := ENNReal.tsum_geometric_two
  have finite : IsFiniteMeasure μ := ⟨total.trans_lt (by simp)⟩
  refine ⟨μ,finite,fun x => ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro B measurable null
  have zeroDense (n : ℕ) : κ (d n) B=0 := by
    have weighted := (Measure.sum_apply_eq_zero.mp null) n
    change ((2 : ℝ≥0∞)⁻¹)^n*κ (d n) B=0 at weighted
    exact (mul_eq_zero.mp weighted).resolve_left (pow_ne_zero n (by simp))
  have agree : (fun x => (κ x).real B)=(fun _ : X => (0 : ℝ)) :=
    dense.equalizer (continuous_rows B measurable) continuous_const (by
      funext n
      simp only [Function.comp_def,Measure.real,zeroDense n,ENNReal.toReal_zero])
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (congrFun agree x)
end LeanShared.StrongFellerDominatingMeasure
