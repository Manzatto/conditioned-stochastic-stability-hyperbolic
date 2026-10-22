module

public import LeanShared.Dynamics.OneSidedCylinderApproximation
public import LeanShared.Dynamics.ComplexOneSidedVariationBanach

/-! Literal finite-cylinder approximations prove compactness of the
complex prefix-variation physical inclusion by operator-norm convergence.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter
open scoped Topology
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def complexCylinderFunction (n : ℕ) (c : RealizedPrefix R n → ℂ) : C(FuturePath R, ℂ) :=
  ⟨fun a => c (realizedPrefix n a), continuous_of_discreteTopology.comp (realizedPrefix_continuous n)⟩

@[expose] def complexCylinderLinear (n : ℕ) : (RealizedPrefix R n → ℂ) →ₗ[ℂ] C(FuturePath R, ℂ) where
  toFun := complexCylinderFunction n
  map_add' c d := by apply ContinuousMap.ext; intro a; rfl
  map_smul' r c := by apply ContinuousMap.ext; intro a; rfl

theorem complexCylinderLinear_norm_bound (n : ℕ) (c : RealizedPrefix R n → ℂ) : ‖complexCylinderLinear n c‖ ≤ ‖c‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg c)).mpr
  intro a
  exact norm_le_pi_norm c (realizedPrefix n a)

@[expose] def complexCylinderOperator (n : ℕ) : (RealizedPrefix R n → ℂ) →L[ℂ] C(FuturePath R, ℂ) :=
  (complexCylinderLinear n).mkContinuous 1 (fun c => by simpa only [one_mul] using complexCylinderLinear_norm_bound n c)

@[expose] def complexCylinderEvaluations (θ : ℝ) (n : ℕ) :
    complexVariationGraph R θ →L[ℂ] (RealizedPrefix R n → ℂ) :=
  ContinuousLinearMap.pi (fun w => (ContinuousMap.evalCLM ℂ (prefixRepresentative n w)).comp (complexVariationPhysical θ))

@[expose] def complexCylinderApproximation (θ : ℝ) (n : ℕ) :
    complexVariationGraph R θ →L[ℂ] C(FuturePath R, ℂ) :=
  (complexCylinderOperator n).comp (complexCylinderEvaluations θ n)

theorem complexCylinderApproximation_apply (θ : ℝ) (n : ℕ) (v : complexVariationGraph R θ) (a : FuturePath R) :
    complexCylinderApproximation θ n v a =
      complexVariationPhysical θ v (prefixRepresentative n (realizedPrefix n a)) := rfl

theorem complexCylinderApproximation_compact (θ : ℝ) (n : ℕ) :
    IsCompactOperator (complexCylinderApproximation θ n : complexVariationGraph R θ → C(FuturePath R, ℂ)) :=
  (isCompactOperator_of_locallyCompactSpace_rng (complexCylinderOperator (R := R) n)).comp_clm (complexCylinderEvaluations θ n)

theorem complexCylinderApproximation_error (θ : ℝ) (positive : 0 < θ) (n : ℕ) (v : complexVariationGraph R θ) :
    ‖complexCylinderApproximation θ n v - complexVariationPhysical θ v‖ ≤ θ ^ n * ‖v‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  change ‖complexCylinderApproximation θ n v a - complexVariationPhysical θ v a‖ ≤ _
  rw [complexCylinderApproximation_apply, mul_comm]
  exact complexVariationPhysical_increment θ positive.le v n a _ (prefixRepresentative_agrees n a)

-- These are the normed structures, stated directly to keep
-- nested operator-norm inference from unfolding the entire graph.
local instance complexFixedGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance complexFixedGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace
local instance complexFixedContinuousNorm : NormedAddCommGroup C(FuturePath R, ℂ) :=
  ContinuousMap.instNormedAddCommGroup
local instance complexFixedContinuousSpace : NormedSpace ℂ C(FuturePath R, ℂ) :=
  ContinuousMap.normedSpace

theorem complexCylinderApproximation_opNorm_error (θ : ℝ) (positive : 0 < θ) (n : ℕ) :
    ‖complexCylinderApproximation θ n - (complexVariationPhysical θ : complexVariationGraph R θ →L[ℂ] C(FuturePath R, ℂ))‖ ≤ θ ^ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg positive.le n)
  exact complexCylinderApproximation_error θ positive n

set_option maxHeartbeats 600000 in
theorem complexVariationPhysical_compact (θ : ℝ) (positive : 0 < θ) (small : θ < 1) :
    IsCompactOperator (complexVariationPhysical θ : complexVariationGraph R θ → C(FuturePath R, ℂ)) := by
  have error : Tendsto (fun n : ℕ =>
      ‖complexCylinderApproximation θ n - (complexVariationPhysical θ : complexVariationGraph R θ →L[ℂ] C(FuturePath R, ℂ))‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (complexCylinderApproximation_opNorm_error θ positive)
      (tendsto_pow_atTop_nhds_zero_of_lt_one positive.le small)
  exact isCompactOperator_of_tendsto (tendsto_iff_norm_sub_tendsto_zero.mpr error)
    (Eventually.of_forall (complexCylinderApproximation_compact θ))

end LeanShared.BilateralShadowingCoding
