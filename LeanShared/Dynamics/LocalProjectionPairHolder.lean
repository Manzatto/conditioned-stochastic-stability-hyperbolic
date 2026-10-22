module

public import LeanShared.Dynamics.HyperbolicProjectionPerturbation
public import LeanShared.Dynamics.BunchedLocalRelationHolder
import Mathlib.Tactic.NoncommRing

/-! Hölder projection comparison on actual local pair states. Source and
target coordinates may change at every step, and cocycle/invariance
identities are required only for close pairs. No ambient metric on the
state index or globally trivial tangent bundle is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicProjectionPerturbation
variable {I R : Type*} [NormedRing R]

set_option maxHeartbeats 1800000 in
theorem local_pair_holder
    (distance : I → ℝ) (F G : I → I) (p q a ai b d di e : I → R)
    (κ B C L α r : ℝ)
    (κnonnegative : 0 ≤ κ) (Bnonnegative : 0 ≤ B)
    (Lnonnegative : 0 ≤ L) (αnonnegative : 0 ≤ α) (positiveR : 0 < r)
    (small : 2 * κ ^ 2 < 1) (bunched : (2 * κ ^ 2) * L ^ α < 1)
    (distanceNonnegative : ∀ i, 0 ≤ distance i)
    (bounded : ∀ i, ‖p i‖ ≤ B ∧ ‖q i‖ ≤ B ∧ ‖1 - q i‖ ≤ B)
    (idempotentP : ∀ i, p i * p i = p i) (idempotentQ : ∀ i, q i * q i = q i)
    (forwardDistance : ∀ i, distance i < r → distance (F i) ≤ L * distance i)
    (backwardDistance : ∀ i, distance i < r → distance (G i) ≤ L * distance i)
    (forwardInverse : ∀ i, distance i < r → ai i * a i = 1)
    (backwardInverse : ∀ i, distance i < r → di i * d i = 1)
    (forwardInvariant : ∀ i, distance i < r → p (F i) * a i = a i * p i)
    (forwardOther : ∀ i, distance i < r → q (F i) * b i = b i * q i)
    (backwardInvariant : ∀ i, distance i < r → (1 - p (G i)) * d i = d i * (1 - p i))
    (backwardOther : ∀ i, distance i < r → (1 - q (G i)) * e i = e i * (1 - q i))
    (forwardStable : ∀ i, distance i < r → ‖b i * q i‖ ≤ κ)
    (forwardUnstable : ∀ i, distance i < r → ‖ai i * (1 - p (F i))‖ ≤ κ)
    (backwardStable : ∀ i, distance i < r → ‖e i * (1 - q i)‖ ≤ κ)
    (backwardUnstable : ∀ i, distance i < r → ‖di i * p (G i)‖ ≤ κ)
    (forwardHolder : ∀ i, distance i < r → ‖a i - b i‖ ≤ C * distance i ^ α)
    (backwardHolder : ∀ i, distance i < r → ‖d i - e i‖ ≤ C * distance i ^ α) :
    ∃ H ≥ 0, ∀ i, ‖p i - q i‖ ≤ H * distance i ^ α := by
  have complementP (i : I) : (1 - p i) * (1 - p i) = 1 - p i := by
    have h := idempotentP i
    noncomm_ring [h]
  have complementQ (i : I) : (1 - q i) * (1 - q i) = 1 - q i := by
    have h := idempotentQ i
    noncomm_ring [h]
  have recurrence (i : I) (near : distance i < r) : ‖p i - q i‖ ≤
      (2 * κ ^ 2) * max ‖p (F i) - q (F i)‖ ‖p (G i) - q (G i)‖ +
        (2 * κ * B * C) * distance i ^ α := by
    have first := cross_bound (a i) (ai i) (b i) (p i) (q i) (p (F i)) (q (F i))
      (forwardInverse i near) (forwardInvariant i near) (forwardOther i near)
      (idempotentP (F i)) (idempotentQ i) κ B
      (forwardUnstable i near) (forwardStable i near) (bounded i).2.1
    have other := cross_bound (d i) (di i) (e i) (1 - p i) (1 - q i)
      (1 - p (G i)) (1 - q (G i))
      (backwardInverse i near) (backwardInvariant i near) (backwardOther i near)
      (complementP (G i)) (complementQ i) κ B
      (by simpa only [sub_sub_cancel] using backwardUnstable i near)
      (backwardStable i near) (bounded i).2.2
    have subtract : (1 - q (G i)) - (1 - p (G i)) = p (G i) - q (G i) := by abel
    simp only [sub_sub_cancel, subtract] at other
    rw [norm_sub_rev (q (F i)) (p (F i))] at first
    have decomposition : p i - q i = p i * (1 - q i) - (1 - p i) * q i := by noncomm_ring
    have triangle : ‖p i - q i‖ ≤ ‖p i * (1 - q i)‖ + ‖(1 - p i) * q i‖ := by
      rw [decomposition]
      exact norm_sub_le _ _
    have coefficient : 0 ≤ κ * B := mul_nonneg κnonnegative Bnonnegative
    have firstHolder := mul_le_mul_of_nonneg_left (forwardHolder i near) coefficient
    have otherHolder := mul_le_mul_of_nonneg_left (backwardHolder i near) coefficient
    have firstMax := mul_le_mul_of_nonneg_left
      (le_max_left ‖p (F i) - q (F i)‖ ‖p (G i) - q (G i)‖) (sq_nonneg κ)
    have otherMax := mul_le_mul_of_nonneg_left
      (le_max_right ‖p (F i) - q (F i)‖ ‖p (G i) - q (G i)‖) (sq_nonneg κ)
    nlinarith
  apply BunchedLocalRelationHolder.bound distance (fun i => ‖p i - q i‖)
    (2 * κ ^ 2) (2 * κ * B * C) L α (2 * B) r
    (by positivity) small Lnonnegative αnonnegative (by positivity) positiveR bunched distanceNonnegative
  · intro i
    exact (norm_sub_le _ _).trans ((add_le_add (bounded i).1 (bounded i).2.1).trans_eq (by ring))
  · intro i near
    rcases le_total ‖p (F i) - q (F i)‖ ‖p (G i) - q (G i)‖ with h | h
    · exact ⟨G i, backwardDistance i near, by simpa only [max_eq_right h] using recurrence i near⟩
    · exact ⟨F i, forwardDistance i near, by simpa only [max_eq_left h] using recurrence i near⟩

end LeanShared.HyperbolicProjectionPerturbation
