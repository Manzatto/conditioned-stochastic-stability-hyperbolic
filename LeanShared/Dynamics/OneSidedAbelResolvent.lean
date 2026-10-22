module

public import LeanShared.Dynamics.OneSidedAbelSums
public import LeanShared.Dynamics.OneSidedTransferGrowth
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual convergent positive Abel sums satisfy the resolvent identity
and retain the uniform distortion cone.  A concrete norm disk supplies
convergence; normalized sums over all actually convergent nonnegative
parameters have compact closure.  No spectral boundary claim is made.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter
open scoped Topology NNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def weightedAbel (ψ : C(FuturePath R, ℝ)) (t : ℝ) : C(FuturePath R, ℝ) :=
  ∑' m : ℕ, t ^ m • weightedIterateOne ψ m

theorem weightedAbel_summable_norm_disk [Nonempty (FuturePath R)]
    (ψ : C(FuturePath R, ℝ)) (t : ℝ) (small : |t| * ‖weightedTransferOperator ψ‖ < 1) :
    Summable (fun m : ℕ => t ^ m • weightedIterateOne ψ m) := by
  have bound (m : ℕ) : ‖t ^ m • weightedIterateOne ψ m‖ ≤ (|t| * ‖weightedTransferOperator ψ‖) ^ m := by
    rw [norm_smul, norm_pow, Real.norm_eq_abs, ← weightedTransferOperator_power_norm]
    calc
      _ ≤ |t| ^ m * ‖weightedTransferOperator ψ‖ ^ m :=
        mul_le_mul_of_nonneg_left (norm_pow_le (weightedTransferOperator ψ) m) (pow_nonneg (abs_nonneg t) m)
      _ = _ := (mul_pow _ _ _).symm
  exact Summable.of_norm_bounded
    (summable_geometric_of_lt_one (mul_nonneg (abs_nonneg t) (norm_nonneg (weightedTransferOperator ψ))) small) bound

omit [CompactSpace A] in
theorem weightedAbelPartial_tendsto (ψ : C(FuturePath R, ℝ)) (t : ℝ)
    (summable : Summable (fun m : ℕ => t ^ m • weightedIterateOne ψ m)) :
    Tendsto (weightedAbelPartial ψ t) atTop (𝓝 (weightedAbel ψ t)) := by
  exact summable.hasSum.tendsto_sum_nat

theorem weightedAbel_resolvent_identity (ψ : C(FuturePath R, ℝ)) (t : ℝ)
    (summable : Summable (fun m : ℕ => t ^ m • weightedIterateOne ψ m)) :
    weightedAbel ψ t - t • weightedTransferOperator ψ (weightedAbel ψ t) = 1 := by
  have partialLimit := weightedAbelPartial_tendsto ψ t summable
  have mapped := ((weightedTransferOperator ψ).continuous.tendsto (weightedAbel ψ t)).comp partialLimit
  have left := partialLimit.sub (mapped.const_smul t)
  have right := (tendsto_const_nhds (x := (1 : C(FuturePath R, ℝ)))).sub summable.tendsto_atTop_zero
  have identity : (fun N => weightedAbelPartial ψ t N - t • weightedTransferOperator ψ (weightedAbelPartial ψ t N)) =
      (fun N : ℕ => 1 - t ^ N • weightedIterateOne ψ N) :=
    funext (weightedAbelPartial_resolvent_identity ψ t)
  simp only [Function.comp_def] at left
  rw [identity] at left
  simpa only [sub_zero] using tendsto_nhds_unique left right

omit [CompactSpace A] in
theorem weightedAbel_nonnegative (ψ : C(FuturePath R, ℝ)) (t : ℝ) (nonnegative : 0 ≤ t)
    (summable : Summable (fun m : ℕ => t ^ m • weightedIterateOne ψ m)) (a : FuturePath R) :
    0 ≤ weightedAbel ψ t a := by
  have point := ((ContinuousMap.evalCLM ℝ a).continuous.tendsto (weightedAbel ψ t)).comp
    (weightedAbelPartial_tendsto ψ t summable)
  exact ge_of_tendsto point (Eventually.of_forall (fun N => weightedAbelPartial_nonnegative ψ t nonnegative N a))

omit [CompactSpace A] in
theorem weightedAbel_ratio (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (t : ℝ) (nonnegative : 0 ≤ t)
    (summable : Summable (fun m : ℕ => t ^ m • weightedIterateOne ψ m)) :
    PrefixRatioBound (weightedAbel ψ t) θ (Cψ * θ / (1 - θ)) := by
  intro n a b same
  have partialLimit := weightedAbelPartial_tendsto ψ t summable
  have first := ((ContinuousMap.evalCLM ℝ b).continuous.tendsto (weightedAbel ψ t)).comp partialLimit
  have second := (((ContinuousMap.evalCLM ℝ a).continuous.tendsto (weightedAbel ψ t)).comp partialLimit).const_mul
    (Real.exp (Cψ * θ / (1 - θ) * θ ^ n))
  exact le_of_tendsto_of_tendsto first second (Eventually.of_forall (fun N =>
    weightedAbelPartial_ratio ψ θ Cψ positiveθ smallθ nonnegativeψ potential t nonnegative N n a b same))

@[expose] def AbelParameter (ψ : C(FuturePath R, ℝ)) :=
  {t : ℝ≥0 // Summable (fun m : ℕ => (t : ℝ) ^ m • weightedIterateOne ψ m)}

theorem normalizedWeightedAbels_relativelyCompact (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n) :
    IsCompact (closure (range (fun p : AbelParameter ψ =>
      ‖weightedAbel ψ p.val‖⁻¹ • weightedAbel ψ p.val))) :=
  normalizedConeFamily_relativelyCompact (fun p : AbelParameter ψ => weightedAbel ψ p.val)
    θ (Cψ * θ / (1 - θ)) positiveθ smallθ
    (div_nonneg (mul_nonneg nonnegativeψ positiveθ.le) (sub_pos.mpr smallθ).le)
    (fun p => weightedAbel_nonnegative ψ p.val p.val.property p.property)
    (fun p => weightedAbel_ratio ψ θ Cψ positiveθ smallθ nonnegativeψ potential p.val p.val.property p.property)

end LeanShared.BilateralShadowingCoding
