module

public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith

/-! # A monotone upper-semicontinuous perturbation modulus

An arbitrary nonnegative perturbation size tending to zero need not itself
satisfy Keller--Liverani's monotonicity or semicontinuity requirements. Cap its
size at one, take the monotone running supremum and regularize by right limits.
Adding the noise parameter makes the resulting modulus strictly positive.
-/

@[expose] public noncomputable section
open Filter Set Function
open scoped Topology NNReal
namespace LeanShared.PerturbationModulus

variable (φ : ℝ≥0 → ℝ)

def envelope (x : ℝ≥0) : ℝ := sSup ((fun u => min (φ u) 1) '' Iic x)

private theorem envelope_bounded (x : ℝ≥0) :
    BddAbove ((fun u => min (φ u) 1) '' Iic x) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨u, _, rfl⟩
  exact min_le_right _ _

private theorem envelope_nonempty (x : ℝ≥0) :
    (((fun u => min (φ u) 1) '' Iic x) : Set ℝ).Nonempty :=
  ⟨min (φ 0) 1, ⟨0, (show (0 : ℝ≥0) ≤ x from bot_le), rfl⟩⟩

theorem le_envelope (x : ℝ≥0) : min (φ x) 1 ≤ envelope φ x :=
  le_csSup (envelope_bounded φ x) ⟨x, le_rfl, rfl⟩

theorem envelope_monotone : Monotone (envelope φ) := by
  intro x y hxy
  apply csSup_le (envelope_nonempty φ x)
  rintro _ ⟨u, hu, rfl⟩
  exact le_csSup (envelope_bounded φ y) ⟨u, hu.trans hxy, rfl⟩

theorem envelope_nonneg (hφ : ∀ x, 0 ≤ φ x) (x : ℝ≥0) : 0 ≤ envelope φ x :=
  (le_min (hφ x) zero_le_one).trans (le_envelope φ x)

theorem envelope_tendsto_zero (hφ : ∀ x, 0 ≤ φ x)
    (hlim : Tendsto φ (𝓝 0) (𝓝 0)) : Tendsto (envelope φ) (𝓝 0) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun x => ha.trans_le (envelope_nonneg φ hφ x))
  · intro a ha
    obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp
      (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < a / 2 by linarith)))
    apply (Metric.eventually_nhds_iff.mpr ⟨δ, hδ, ?_⟩)
    intro x hx
    have hbound : envelope φ x ≤ a / 2 := by
      apply csSup_le (envelope_nonempty φ x)
      rintro _ ⟨u, hu, rfl⟩
      apply (min_le_left _ _).trans
      apply le_of_lt (hsmall ?_)
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg u.coe_nonneg]
      have hx' : (x : ℝ) < δ := by simpa [NNReal.dist_eq, abs_of_nonneg x.coe_nonneg] using hx
      exact lt_of_le_of_lt hu hx'
    exact hbound.trans_lt (by linarith)

/-- A monotone function's right-limit regularization is upper semicontinuous.
The proof chooses a larger parameter whose value is below a prescribed bound. -/
theorem monotone_rightLim_upperSemicontinuous
    {f : ℝ≥0 → ℝ} (hf : Monotone f) : UpperSemicontinuous f.rightLim := by
  intro x a ha
  have hb : BddBelow (f '' Ioi x) := by
    refine ⟨f x, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hf hy.le
  have hn : (f '' Ioi x).Nonempty := ⟨f (x + 1), ⟨x + 1, by simp, rfl⟩⟩
  rw [hf.rightLim_eq_sInf] at ha
  obtain ⟨_, ⟨y, hy, rfl⟩, hya⟩ := (csInf_lt_iff hb hn).mp ha
  filter_upwards [Iio_mem_nhds hy] with z hz
  exact (hf.rightLim_le hz).trans_lt hya

theorem right_envelope_tendsto_zero (hφ : ∀ x, 0 ≤ φ x)
    (hlim : Tendsto φ (𝓝 0) (𝓝 0)) :
    Tendsto (envelope φ).rightLim (𝓝 0) (𝓝 0) := by
  have hmono := envelope_monotone φ
  have hnonneg (x : ℝ≥0) : 0 ≤ (envelope φ).rightLim x :=
    (envelope_nonneg φ hφ x).trans (hmono.le_rightLim le_rfl)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun x => ha.trans_le (hnonneg x))
  · intro a ha
    obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp
      ((envelope_tendsto_zero φ hφ hlim).eventually (gt_mem_nhds ha))
    let y : ℝ≥0 := ⟨δ / 2, by positivity⟩
    have hy : 0 < y := by change 0 < δ / 2; positivity
    have hfy : envelope φ y < a := hsmall (by
      simp only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg y.coe_nonneg]
      change δ / 2 < δ
      linarith)
    filter_upwards [Iio_mem_nhds hy] with x hx
    exact (hmono.rightLim_le hx).trans_lt hfy

/-- The monotone right-continuous envelope, plus the strictly positive noise
parameter. Only local domination of the uncapped perturbation is needed. -/
def modulus (hφ : ∀ x, 0 ≤ φ x) (x : ℝ≥0) : ℝ≥0 :=
  ⟨(envelope φ).rightLim x + x,
    add_nonneg ((envelope_nonneg φ hφ x).trans
      ((envelope_monotone φ).le_rightLim le_rfl)) x.coe_nonneg⟩

theorem modulus_monotone (hφ : ∀ x, 0 ≤ φ x) : Monotone (modulus φ hφ) := by
  intro x y hxy
  apply NNReal.coe_le_coe.mp
  change (envelope φ).rightLim x + x ≤ (envelope φ).rightLim y + y
  exact add_le_add ((envelope_monotone φ).rightLim hxy) hxy

theorem modulus_upperSemicontinuous (hφ : ∀ x, 0 ≤ φ x) :
    UpperSemicontinuous (modulus φ hφ) := by
  have hreal : UpperSemicontinuous (fun x : ℝ≥0 => (envelope φ).rightLim x + (x : ℝ)) :=
    (monotone_rightLim_upperSemicontinuous (envelope_monotone φ)).add
      NNReal.continuous_coe.upperSemicontinuous
  intro x a ha
  have ha' : (envelope φ).rightLim x + x < (a : ℝ) := NNReal.coe_lt_coe.mpr ha
  exact (hreal x a ha').mono (fun y hy => NNReal.coe_lt_coe.mp hy)

theorem modulus_pos (hφ : ∀ x, 0 ≤ φ x) (x : ℝ≥0) (hx : 0 < x) :
    0 < modulus φ hφ x := by
  apply NNReal.coe_pos.mp
  change 0 < (envelope φ).rightLim x + x
  exact add_pos_of_nonneg_of_pos ((envelope_nonneg φ hφ x).trans
    ((envelope_monotone φ).le_rightLim le_rfl)) (NNReal.coe_pos.mpr hx)

theorem modulus_tendsto_zero (hφ : ∀ x, 0 ≤ φ x)
    (hlim : Tendsto φ (𝓝 0) (𝓝 0)) :
    Tendsto (modulus φ hφ) (𝓝 0) (𝓝 0) := by
  apply NNReal.tendsto_coe.mp
  change Tendsto (fun x : ℝ≥0 => (envelope φ).rightLim x + (x : ℝ)) (𝓝 0) (𝓝 0)
  simpa only [NNReal.coe_zero, add_zero] using
    (right_envelope_tendsto_zero φ hφ hlim).add
      (NNReal.continuous_coe.continuousAt.tendsto)

theorem eventually_le_modulus (hφ : ∀ x, 0 ≤ φ x)
    (hlim : Tendsto φ (𝓝 0) (𝓝 0)) :
    ∀ᶠ x in 𝓝 (0 : ℝ≥0), φ x ≤ (modulus φ hφ x : ℝ) := by
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx
  have hcap : φ x ≤ envelope φ x := by simpa only [min_eq_left hx.le] using le_envelope φ x
  exact (hcap.trans ((envelope_monotone φ).le_rightLim le_rfl)).trans
    (le_add_of_nonneg_right x.coe_nonneg)

/-- Arbitrary nonnegative perturbation convergence admits a genuine KL
modulus. Its positive, monotone USC requirements are all proved. -/
theorem exists_modulus (hφ : ∀ x, 0 ≤ φ x) (hlim : Tendsto φ (𝓝 0) (𝓝 0)) :
    ∃ τ : ℝ≥0 → ℝ≥0, Monotone τ ∧ UpperSemicontinuous τ ∧
      (∀ x, 0 < x → 0 < τ x) ∧ Tendsto τ (𝓝 0) (𝓝 0) ∧
      ∀ᶠ x in 𝓝 (0 : ℝ≥0), φ x ≤ (τ x : ℝ) :=
  ⟨modulus φ hφ, modulus_monotone φ hφ, modulus_upperSemicontinuous φ hφ,
    modulus_pos φ hφ, modulus_tendsto_zero φ hφ hlim, eventually_le_modulus φ hφ hlim⟩

/-- Choose a closed positive parameter window on which the genuine modulus
dominates the actual uncapped perturbation, including the zero parameter. -/
theorem exists_modulus_window (hφ : ∀ x, 0 ≤ φ x)
    (hlim : Tendsto φ (𝓝 0) (𝓝 0)) :
    ∃ (τ : ℝ≥0 → ℝ≥0) (window : ℝ≥0), 0 < window ∧
      Monotone τ ∧ UpperSemicontinuous τ ∧ (∀ x, 0 < x → 0 < τ x) ∧
      Tendsto τ (𝓝 0) (𝓝 0) ∧ ∀ x ≤ window, φ x ≤ (τ x : ℝ) := by
  obtain ⟨τ, hmono, husc, hpos, hzero, hdom⟩ := exists_modulus φ hφ hlim
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp hdom
  let window : ℝ≥0 := ⟨δ / 2, by positivity⟩
  refine ⟨τ, window, ?_, hmono, husc, hpos, hzero, ?_⟩
  · change 0 < δ / 2
    positivity
  · intro x hx
    apply hsmall
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg x.coe_nonneg]
    have hx' : (x : ℝ) ≤ δ / 2 := hx
    linarith

end LeanShared.PerturbationModulus
