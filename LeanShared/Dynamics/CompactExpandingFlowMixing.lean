module

public import LeanShared.Dynamics.HyperbolicBasicSet
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! A compact additive group with a dense real one-parameter flow is
topologically mixed by any automorphism that expands that flow. Compactness
turns density into a uniform bounded-time hitting statement. -/

public noncomputable section
namespace LeanShared.CompactExpandingFlowMixing
open Set Function Filter
open scoped Topology BigOperators

variable {G : Type*} [AddCommGroup G] [MetricSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G]

private theorem bounded_hitting (flow : ℝ →+ G)
    (dense : DenseRange flow) (W : Set G) (openW : IsOpen W) (nonemptyW : W.Nonempty) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : G, ∃ t : ℝ, |t| < B ∧ x + flow t ∈ W := by
  classical
  let D : ℝ → Set G := fun t => {x | x + flow t ∈ W}
  have openD (t : ℝ) : IsOpen (D t) := openW.preimage (continuous_id.add continuous_const)
  have covers (x : G) : ∃ t, x ∈ D t := by
    have openTranslated : IsOpen ((fun y : G => x + y) ⁻¹' W) :=
      openW.preimage (continuous_const.add continuous_id)
    obtain ⟨w, memberW⟩ := nonemptyW
    have nonemptyTranslated : ((fun y : G => x + y) ⁻¹' W).Nonempty :=
      ⟨w - x, by simpa only [mem_preimage, ← add_sub_assoc, add_sub_cancel_left] using memberW⟩
    obtain ⟨t, hit⟩ := dense.exists_mem_open openTranslated nonemptyTranslated
    exact ⟨t, hit⟩
  obtain ⟨s, cover⟩ := isCompact_univ.elim_finite_subcover D openD (by
    intro x _
    obtain ⟨t, member⟩ := covers x
    exact mem_iUnion.mpr ⟨t, member⟩)
  let B := 1 + ∑ t ∈ s, |t|
  have nonnegativeSum : 0 ≤ ∑ t ∈ s, |t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B, by dsimp only [B]; linarith, fun x => ?_⟩
  rcases mem_iUnion.mp (cover (mem_univ x)) with ⟨t, ht⟩
  rcases mem_iUnion.mp ht with ⟨memberS, hit⟩
  have bounded : |t| ≤ ∑ t ∈ s, |t| :=
    Finset.single_le_sum (fun _ _ => abs_nonneg _) memberS
  exact ⟨t, by dsimp only [B]; linarith, hit⟩

theorem mixing (flow : ℝ →+ G) (continuous : Continuous flow) (dense : DenseRange flow)
    (T : G ≃ₜ G) (additive : ∀ x y, T (x + y) = T x + T y)
    (rate : ℝ) (expanding : 1 < rate) (scales : ∀ t, T (flow t) = flow (rate * t)) :
    HyperbolicBasicSet.MixingOn T univ := by
  classical
  have positiverate : 0 < rate := zero_lt_one.trans expanding
  have iterate_add (n : ℕ) (x y : G) :
      (T : G → G)^[n] (x + y) = (T : G → G)^[n] x + (T : G → G)^[n] y := by
    induction n with
    | zero => rfl
    | succ n induction =>
      rw [Function.iterate_succ_apply', induction, additive,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
  have iterate_flow (n : ℕ) (t : ℝ) : (T : G → G)^[n] (flow t) = flow (rate ^ n * t) := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    | succ n induction =>
      rw [Function.iterate_succ_apply', induction, scales, ← mul_assoc, ← pow_succ']
  unfold HyperbolicBasicSet.MixingOn
  intro U W openU openW nonemptyU nonemptyW
  obtain ⟨x, _, memberU⟩ := nonemptyU
  have nonemptyW' : W.Nonempty := nonemptyW.mono inter_subset_right
  obtain ⟨B, _positiveB, hit⟩ := bounded_hitting flow dense W openW nonemptyW'
  have near : (fun t : ℝ => x + flow t) ⁻¹' U ∈ 𝓝 (0 : ℝ) := by
    apply ((continuous_const.add continuous).continuousAt).preimage_mem_nhds
    simpa only [Pi.add_apply, map_zero, add_zero] using openU.mem_nhds memberU
  obtain ⟨ε, positiveε, small⟩ := Metric.mem_nhds_iff.mp near
  obtain ⟨N, large⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt expanding).eventually (eventually_gt_atTop (B / ε)))
  refine ⟨N, fun n largeN => ?_⟩
  obtain ⟨t, bounded, hitting⟩ := hit ((T : G → G)^[n] x)
  have positivePower : 0 < rate ^ n := pow_pos positiverate n
  have smallT : |t / rate ^ n| < ε := by
    rw [abs_div, abs_of_pos positivePower, div_lt_iff₀ positivePower]
    have scaled := (div_lt_iff₀ positiveε).mp (large n largeN)
    nlinarith
  have inside : x + flow (t / rate ^ n) ∈ U := small (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using smallT)
  refine ⟨x + flow (t / rate ^ n), ⟨mem_univ _, inside⟩, ?_⟩
  rw [iterate_add, iterate_flow, mul_div_cancel₀ _ positivePower.ne']
  exact hitting

end LeanShared.CompactExpandingFlowMixing
