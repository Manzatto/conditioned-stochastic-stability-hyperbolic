module
public import LeanShared.Dynamics.LocalPeriodicJacobian

/-! Periodic chains of chart maps produce local periodic closing data. Maps
`h_j : E → E` along a periodic chart orbit `h_j (a_j) = a_{j+1}`, normalized by linear
isomorphisms `L_j : U × S ≃ E` in which the derivative at `a_j` is the split hyperbolic map
`A_j × B_j`, with an `α`-Hölder derivative on the `ρ`-ball, give the centered maps
`H_j w = L_{j+1}⁻¹ (h_j (a_j + L_j w) - a_{j+1})` (radially extended for continuity).
Their derivatives are `δ`-close to `A_j × B_j` on a ball of a radius depending only on
the uniform constants, and Hölder at the origin with `K = bound^(2+α) C`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal Topology
open Set Metric
namespace LeanShared.ChartChainClosing

variable {U S E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A periodic chain of chart maps along a periodic orbit. -/
structure Chain (U S E : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedAddCommGroup E] [NormedSpace ℝ E] where
  period : ℕ
  period_pos : 0 < period
  h : ℤ → E → E
  h' : ℤ → E → E →L[ℝ] E
  a : ℤ → E
  L : ℤ → (U × S) ≃L[ℝ] E
  A : ℤ → U ≃L[ℝ] U
  B : ℤ → S →L[ℝ] S
  ρ : ℝ
  ρ_pos : 0 < ρ
  bound : ℝ
  bound_pos : 0 < bound
  holderC : ℝ
  holderC_nonneg : 0 ≤ holderC
  α : ℝ
  α_pos : 0 < α
  k : ℝ≥0
  hyperbolicA : ∀ j, ‖(A j).symm.toContinuousLinearMap‖ ≤ k
  hyperbolicB : ∀ j, ‖B j‖ ≤ k
  orbit : ∀ j, h j (a j) = a (j + 1)
  derivative : ∀ j y, y ∈ closedBall (a j) ρ → HasFDerivAt (h j) (h' j y) y
  diagonal : ∀ j, (L (j + 1)).symm.toContinuousLinearMap.comp
    ((h' j (a j)).comp (L j).toContinuousLinearMap) = (A j : U →L[ℝ] U).prodMap (B j)
  holder : ∀ j y, y ∈ closedBall (a j) ρ → ‖h' j y - h' j (a j)‖ ≤ holderC * ‖y - a j‖ ^ α
  continuousOn : ∀ j, ContinuousOn (h j) (closedBall (a j) ρ)
  L_bound : ∀ j, ‖(L j).toContinuousLinearMap‖ ≤ bound
  L_inv_bound : ∀ j, ‖(L j).symm.toContinuousLinearMap‖ ≤ bound
  periodic_h : ∀ j, h (j + period) = h j
  periodic_h' : ∀ j, h' (j + period) = h' j
  periodic_a : ∀ j, a (j + period) = a j
  periodic_L : ∀ j, L (j + period) = L j
  periodic_A : ∀ j, A (j + period) = A j
  periodic_B : ∀ j, B (j + period) = B j

namespace Chain

variable (c : Chain U S E)

/-- The Hölder constant at the origin of the centered maps. -/
@[expose] def holderK : ℝ := c.bound ^ 2 * c.holderC * c.bound ^ c.α

theorem holderK_nonneg : 0 ≤ c.holderK := by
  have := c.bound_pos
  have := c.holderC_nonneg
  unfold holderK
  positivity

/-- The radius of the centered data for a closeness `δ`. -/
@[expose] def radius (δ : ℝ) : ℝ :=
  min (c.ρ / (2 * c.bound)) ((δ / (c.holderK + 1)) ^ c.α⁻¹)

theorem radius_pos (δ : ℝ) (hδ : 0 < δ) : 0 < c.radius δ := by
  have := c.bound_pos
  have := c.ρ_pos
  have := c.holderK_nonneg
  exact lt_min (by positivity) (Real.rpow_pos_of_pos (by positivity) _)

/-- The exact centered map. -/
@[expose] def centered (j : ℤ) (w : U × S) : U × S :=
  (c.L (j + 1)).symm (c.h j (c.a j + c.L j w) - c.a (j + 1))

/-- The radially extended centered map. -/
@[expose] def H (δ : ℝ) (j : ℤ) (w : U × S) : U × S :=
  c.centered j (RadialBallRetraction.retract (2 * c.radius δ) w)

/-- The centered derivative. -/
@[expose] def H' (j : ℤ) (w : U × S) : (U × S) →L[ℝ] (U × S) :=
  (c.L (j + 1)).symm.toContinuousLinearMap.comp ((c.h' j (c.a j + c.L j w)).comp
    (c.L j).toContinuousLinearMap)

theorem inside (δ : ℝ) (j : ℤ) (w : U × S) (hw : ‖w‖ ≤ 2 * c.radius δ) :
    c.a j + c.L j w ∈ closedBall (c.a j) c.ρ := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have := c.bound_pos
  calc ‖c.L j w‖ ≤ c.bound * ‖w‖ :=
        ((c.L j).toContinuousLinearMap.le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (c.L_bound j) (norm_nonneg _))
    _ ≤ c.bound * (2 * (c.ρ / (2 * c.bound))) :=
        mul_le_mul_of_nonneg_left (hw.trans (mul_le_mul_of_nonneg_left (min_le_left _ _)
          (by norm_num))) this.le
    _ = c.ρ := by field_simp

theorem H_eq (δ : ℝ) (hδ : 0 < δ) (j : ℤ) (w : U × S) (hw : ‖w‖ ≤ 2 * c.radius δ) :
    c.H δ j w = c.centered j w := by
  rw [H, RadialBallRetraction.retract_eq_self _ (by linarith [c.radius_pos δ hδ]) hw]

theorem H_zero (δ : ℝ) (j : ℤ) : c.H δ j 0 = 0 := by
  simp only [H, RadialBallRetraction.retract, norm_zero, smul_zero, centered, map_zero, add_zero,
    c.orbit, sub_self]

theorem hasFDerivAt_centered (δ : ℝ) (j : ℤ) (w : U × S)
    (hw : ‖w‖ ≤ 2 * c.radius δ) : HasFDerivAt (c.centered j) (c.H' j w) w := by
  have affine : HasFDerivAt (fun v : U × S => c.a j + c.L j v) (c.L j).toContinuousLinearMap w :=
    ((c.L j).hasFDerivAt).const_add (c.a j)
  have inner := (c.derivative j _ (c.inside δ j w hw)).comp w affine
  have outer := ((c.L (j + 1)).symm.hasFDerivAt).comp w (inner.sub_const (c.a (j + 1)))
  exact outer

theorem hasFDerivAt_H (δ : ℝ) (hδ : 0 < δ) (j : ℤ) (w : U × S) (hw : ‖w‖ ≤ c.radius δ) :
    HasFDerivAt (c.H δ j) (c.H' j w) w := by
  have hr := c.radius_pos δ hδ
  have local_eq : c.H δ j =ᶠ[𝓝 w] c.centered j := by
    have : ball w (c.radius δ) ∈ 𝓝 w := ball_mem_nhds w hr
    filter_upwards [this] with v hv
    rw [mem_ball, dist_eq_norm] at hv
    apply c.H_eq δ hδ j v
    calc ‖v‖ = ‖(v - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 2 * c.radius δ := by linarith
  exact (c.hasFDerivAt_centered δ j w (by linarith)).congr_of_eventuallyEq local_eq

theorem H'_zero (j : ℤ) : c.H' j 0 = (c.A j : U →L[ℝ] U).prodMap (c.B j) := by
  rw [H', map_zero, add_zero]
  exact c.diagonal j

theorem H'_holder (δ : ℝ) (j : ℤ) (w : U × S) (hw : ‖w‖ ≤ 2 * c.radius δ) :
    ‖c.H' j w - (c.A j : U →L[ℝ] U).prodMap (c.B j)‖ ≤ c.holderK * ‖w‖ ^ c.α := by
  rw [← c.H'_zero j]
  have difference : c.H' j w - c.H' j 0 = (c.L (j + 1)).symm.toContinuousLinearMap.comp
      ((c.h' j (c.a j + c.L j w) - c.h' j (c.a j)).comp (c.L j).toContinuousLinearMap) := by
    simp only [H', map_zero, add_zero, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [difference]
  have hb := c.bound_pos
  have holder := c.holder j _ (c.inside δ j w hw)
  rw [add_sub_cancel_left] at holder
  have Lw : ‖c.L j w‖ ≤ c.bound * ‖w‖ :=
    ((c.L j).toContinuousLinearMap.le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (c.L_bound j) (norm_nonneg _))
  have Lwα : ‖c.L j w‖ ^ c.α ≤ c.bound ^ c.α * ‖w‖ ^ c.α := by
    rw [← Real.mul_rpow hb.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) Lw c.α_pos.le
  calc ‖(c.L (j + 1)).symm.toContinuousLinearMap.comp
        ((c.h' j (c.a j + c.L j w) - c.h' j (c.a j)).comp (c.L j).toContinuousLinearMap)‖
      ≤ ‖(c.L (j + 1)).symm.toContinuousLinearMap‖ *
          (‖c.h' j (c.a j + c.L j w) - c.h' j (c.a j)‖ * ‖(c.L j).toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ c.bound * (c.holderC * (c.bound ^ c.α * ‖w‖ ^ c.α) * c.bound) := by
        apply mul_le_mul (c.L_inv_bound (j + 1)) _ (by positivity) hb.le
        apply mul_le_mul _ (c.L_bound j) (norm_nonneg _) (by
          have := c.holderC_nonneg
          positivity)
        exact holder.trans (mul_le_mul_of_nonneg_left Lwα c.holderC_nonneg)
    _ = c.holderK * ‖w‖ ^ c.α := by simp only [holderK]; ring

theorem H'_close (δ : ℝ) (hδ : 0 < δ) (j : ℤ) (w : U × S) (hw : ‖w‖ ≤ c.radius δ) :
    ‖c.H' j w - (c.A j : U →L[ℝ] U).prodMap (c.B j)‖ ≤ δ := by
  have hr := c.radius_pos δ hδ
  refine (c.H'_holder δ j w (by linarith)).trans ?_
  have hK := c.holderK_nonneg
  have wα : ‖w‖ ^ c.α ≤ δ / (c.holderK + 1) := by
    have h1 : ‖w‖ ≤ (δ / (c.holderK + 1)) ^ c.α⁻¹ := hw.trans (min_le_right _ _)
    have h2 := Real.rpow_le_rpow (norm_nonneg w) h1 c.α_pos.le
    rwa [Real.rpow_inv_rpow (by positivity) c.α_pos.ne'] at h2
  calc c.holderK * ‖w‖ ^ c.α ≤ c.holderK * (δ / (c.holderK + 1)) :=
        mul_le_mul_of_nonneg_left wα hK
    _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

theorem continuous_H (δ : ℝ) (hδ : 0 < δ) (j : ℤ) : Continuous (c.H δ j) := by
  have hr := c.radius_pos δ hδ
  have retractC : Continuous (RadialBallRetraction.retract (E := U × S) (2 * c.radius δ)) :=
    (RadialBallRetraction.lipschitz_retract _ (by linarith)).continuous
  have maps : MapsTo (fun w : U × S => c.a j + c.L j (RadialBallRetraction.retract (2 * c.radius δ) w))
      univ (closedBall (c.a j) c.ρ) := fun w _ =>
    c.inside δ j _ (RadialBallRetraction.norm_retract_le _ (by linarith) w)
  have inner : Continuous (fun w : U × S =>
      c.h j (c.a j + c.L j (RadialBallRetraction.retract (2 * c.radius δ) w))) := by
    rw [← continuousOn_univ]
    exact (c.continuousOn j).comp
      (continuous_const.add ((c.L j).continuous.comp retractC)).continuousOn maps
  exact (c.L (j + 1)).symm.continuous.comp (inner.sub continuous_const)

/-- The local periodic closing data of a chart chain. -/
@[expose] def toData (δ : ℝ≥0) (hδ : 0 < δ) (small : c.k + δ * 2 < 1) :
    LocalPeriodicClosing.Data U S where
  A := c.A
  B := c.B
  H := c.H δ
  H' := c.H'
  k := c.k
  δ := δ
  small := small
  inverse := c.hyperbolicA
  stable := c.hyperbolicB
  r := c.radius δ
  r_pos := c.radius_pos δ hδ
  zero := c.H_zero δ
  derivative := c.hasFDerivAt_H δ hδ
  derivative_zero := c.H'_zero
  close := c.H'_close δ hδ
  continuous := c.continuous_H δ hδ
  period := c.period
  period_pos := c.period_pos
  periodic_A := c.periodic_A
  periodic_B := c.periodic_B
  periodic_H := fun j => by
    funext w
    simp only [H, centered, show j + (c.period : ℤ) + 1 = j + 1 + c.period by ring,
      c.periodic_h, c.periodic_a, c.periodic_L]
  periodic_H' := fun j => by
    funext w
    simp only [H', show j + (c.period : ℤ) + 1 = j + 1 + c.period by ring,
      c.periodic_h', c.periodic_a, c.periodic_L]

theorem toData_holder (δ : ℝ≥0) (hδ : 0 < δ) (small : c.k + δ * 2 < 1) (j : ℤ) (v : U × S)
    (hv : ‖v‖ ≤ (c.toData δ hδ small).r) :
    ‖(c.toData δ hδ small).H' j v - (c.toData δ hδ small).D j‖ ≤ c.holderK * ‖v‖ ^ c.α :=
  c.H'_holder δ j v (by
    have := c.radius_pos δ hδ
    change ‖v‖ ≤ c.radius δ at hv
    linarith)

end Chain
end LeanShared.ChartChainClosing
