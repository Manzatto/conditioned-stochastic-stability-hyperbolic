module
public import LeanShared.Analysis.CompactUniformLocalHolder
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Homogeneous local Holder estimates globalize with the SAME parameter
weight. This proves actual operator norm bounds for compact chart patching,
not merely separate finiteness for each input vector. -/
public noncomputable section
namespace LeanShared.CompactUniformLocalHolder
open Set

theorem scaled_bounds
    {X Y P : Type*} [MetricSpace X] [CompactSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : P → X → Y) (weight : P → ℝ) (nonnegative : ∀ p, 0 ≤ weight p)
    (a : ℝ) (ha : 0 ≤ a)
    (localBound : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p,
        (∀ y ∈ W, ‖f p y‖ ≤ B*weight p) ∧
        ∀ y ∈ W, ∀ z ∈ W, ‖f p y-f p z‖ ≤ C*weight p*dist y z^a) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p,
      (∀ x, ‖f p x‖ ≤ B*weight p) ∧
      ∀ x y, ‖f p x-f p y‖ ≤ C*weight p*dist x y^a := by
  let F := fun p x => (weight p)⁻¹ • f p x
  have normalize (p : P) (z : Y) (C : ℝ) (hC : 0 ≤ C) (bound : ‖z‖ ≤ C*weight p) :
      ‖(weight p)⁻¹ • z‖ ≤ C := by
    by_cases zero : weight p = 0
    · simpa only [zero,inv_zero,zero_smul,norm_zero] using hC
    · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (nonnegative p))]
      exact (mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (nonnegative p))).trans_eq
        (by rw [mul_comm C,←mul_assoc,inv_mul_cancel₀ zero,one_mul])
  have localNormalized : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ p,
        (∀ y ∈ W, ‖F p y‖ ≤ B) ∧ ∀ y ∈ W, ∀ z ∈ W, ‖F p y-F p z‖ ≤ C*dist y z^a := by
    intro x
    obtain ⟨W,openW,inside,B,C,hB,hC,bound⟩ := localBound x
    refine ⟨W,openW,inside,B,C,hB,hC,fun p => ⟨fun y hy => normalize p _ B hB ((bound p).1 y hy),?_⟩⟩
    intro y hy z hz
    change ‖(weight p)⁻¹ • f p y-(weight p)⁻¹ • f p z‖ ≤ _
    rw [←smul_sub]
    apply normalize p _ (C*dist y z^a) (mul_nonneg hC (Real.rpow_nonneg dist_nonneg _))
    exact ((bound p).2 y hy z hz).trans_eq (by ring)
  obtain ⟨B,C,hB,hC,bound⟩ := bounds F a ha localNormalized
  have reconstruct (p : P) (x : X) : f p x = weight p • F p x := by
    by_cases zero : weight p = 0
    · obtain ⟨W,_,inside,B,_,_,_,localEstimate⟩ := localBound x
      have actual : ‖f p x‖ ≤ 0 := by simpa only [zero,mul_zero] using (localEstimate p).1 x inside
      have vanish : f p x = 0 := norm_eq_zero.mp (le_antisymm actual (norm_nonneg _))
      simpa only [zero,zero_smul] using vanish
    · dsimp only [F]
      rw [smul_smul,mul_inv_cancel₀ zero,one_smul]
  refine ⟨B,C,hB,hC,fun p => ⟨?_,?_⟩⟩
  · intro x
    rw [reconstruct p x,norm_smul,Real.norm_eq_abs,abs_of_nonneg (nonnegative p)]
    exact (mul_le_mul_of_nonneg_left ((bound p).1 x) (nonnegative p)).trans_eq (mul_comm _ _)
  · intro x y
    have same : f p x-f p y=weight p • (F p x-F p y) := by
      rw [smul_sub,←reconstruct p x,←reconstruct p y]
    rw [same,norm_smul,Real.norm_eq_abs,abs_of_nonneg (nonnegative p)]
    exact (mul_le_mul_of_nonneg_left ((bound p).2 x y) (nonnegative p)).trans_eq (by ring)

end LeanShared.CompactUniformLocalHolder
