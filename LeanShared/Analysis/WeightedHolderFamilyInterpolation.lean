module
public import LeanShared.Analysis.HolderWeightComposition
public import LeanShared.Analysis.HolderPowerInterpolation

/-! The interpolation source for actual weighted actions follows from
uniform higher Holder weight bounds and map Lipschitz constants. The
parameter set has no topology and no continuity assumption. -/
public noncomputable section
namespace LeanShared.HolderWeightComposition
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem family_interpolation
    {X P : Type*} [MetricSpace X] {a b B C : ℝ} (hb : 0 ≤ b) (hba : b < a)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (ψ : P → X →ᵇ ℂ)
    (values : ∀ p, ‖ψ p‖ ≤ B)
    (weights : ∀ p x y, ‖ψ p x-ψ p y‖ ≤ C*dist x y^a)
    {L : NNReal} (g : P → X → X) (lip : ∀ p, LipschitzWith L (g p))
    (f : BoundedHolderSpace.graph X a) (v : P → BoundedHolderSpace.graph X b)
    (physical : ∀ p x, BoundedHolderSpace.physical X b (v p) x =
      ψ p x*BoundedHolderSpace.physical X a f (g p x))
    (p q : P) {e : ℝ} (he : 0 ≤ e)
    (error : ∀ x, ‖BoundedHolderSpace.physical X b (v p) x-
      BoundedHolderSpace.physical X b (v q) x‖ ≤ e) :
    ‖v p-v q‖ ≤ (2*((B*(L:ℝ)^a+C)*‖f‖)+6*(B*‖f‖)+3)*e^((a-b)/a) := by
  have ha : 0 ≤ a := hb.trans hba.le
  let D := (B*(L:ℝ)^a+C)*‖f‖
  have hD : 0 ≤ D := by positivity
  have increment (p : P) (x y : X) :
      ‖BoundedHolderSpace.physical X b (v p) x-
        BoundedHolderSpace.physical X b (v p) y‖ ≤ D*dist x y^a := by
    rw [physical,physical]
    have actual := HolderWeightComposition.increment ha (ψ p) hC (weights p) (g p) (lip p) f x y
    change ‖ψ p x*BoundedHolderSpace.physical X a f (g p x)-
      ψ p y*BoundedHolderSpace.physical X a f (g p y)‖ ≤ _ at actual
    apply actual.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_right (values p) (Real.rpow_nonneg L.coe_nonneg a)) le_rfl)
        (norm_nonneg f)) (Real.rpow_nonneg dist_nonneg a)
  have value (p : P) (x : X) : ‖BoundedHolderSpace.physical X b (v p) x‖ ≤ B*‖f‖ := by
    rw [physical,norm_mul]
    exact mul_le_mul ((ψ p).norm_coe_le_norm x |>.trans (values p))
      (((BoundedHolderSpace.physical X a f).norm_coe_le_norm _).trans
        (BoundedHolderSpace.physical_norm_le X a f)) (norm_nonneg _) hB
  have difference x : BoundedHolderSpace.physical X b (v p-v q) x =
      BoundedHolderSpace.physical X b (v p) x-BoundedHolderSpace.physical X b (v q) x := by
    rw [map_sub,BoundedContinuousFunction.sub_apply]
  have normBound : ‖BoundedHolderSpace.physical X b (v p-v q)‖ ≤ 2*(B*‖f‖) :=
    (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun x => by
      rw [difference]
      exact (norm_sub_le _ _).trans ((add_le_add (value p x) (value q x)).trans_eq (by ring)))
  have uniform : ‖BoundedHolderSpace.physical X b (v p-v q)‖ ≤ e :=
    (BoundedContinuousFunction.norm_le he).mpr (fun x => by rw [difference]; exact error x)
  have increments x y : ‖BoundedHolderSpace.physical X b (v p-v q) x-
      BoundedHolderSpace.physical X b (v p-v q) y‖ ≤ (2*D)*dist x y^a := by
    rw [difference,difference]
    have rearrange : (BoundedHolderSpace.physical X b (v p) x-BoundedHolderSpace.physical X b (v q) x)-
        (BoundedHolderSpace.physical X b (v p) y-BoundedHolderSpace.physical X b (v q) y) =
        (BoundedHolderSpace.physical X b (v p) x-BoundedHolderSpace.physical X b (v p) y)-
        (BoundedHolderSpace.physical X b (v q) x-BoundedHolderSpace.physical X b (v q) y) := by abel
    rw [rearrange]
    exact (norm_sub_le _ _).trans ((add_le_add (increment p x y) (increment q x y)).trans_eq (by ring))
  have estimate := HolderInterpolation.power_norm_bound hb hba (by positivity : 0 ≤ 2*D)
    (by positivity : 0 ≤ 2*(B*‖f‖)) he (v p-v q) normBound uniform increments
  exact estimate.trans_eq (by dsimp only [D] at *; ring)

end LeanShared.HolderWeightComposition
