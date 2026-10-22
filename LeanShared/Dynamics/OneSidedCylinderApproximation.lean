module

public import LeanShared.Dynamics.OneSidedVariationBanach
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual finite cylinder approximations on the admitted one-sided
graph.  Their finite-dimensional factorization and uniform geometric
error prove compactness of the literal Banach variation inclusion.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter
open scoped Topology
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def RealizedPrefix (R : A → A → Prop) (n : ℕ) :=
  {w : Fin (n + 1) → A // ∃ a : FuturePath R, ∀ i : Fin (n + 1), a.val i.val = w i}

instance realizedPrefixTopology (n : ℕ) : TopologicalSpace (RealizedPrefix R n) :=
  inferInstanceAs (TopologicalSpace
    {w : Fin (n + 1) → A // ∃ a : FuturePath R, ∀ i : Fin (n + 1), a.val i.val = w i})

instance realizedPrefixDiscrete (n : ℕ) : DiscreteTopology (RealizedPrefix R n) :=
  inferInstanceAs (DiscreteTopology
    {w : Fin (n + 1) → A // ∃ a : FuturePath R, ∀ i : Fin (n + 1), a.val i.val = w i})

instance realizedPrefixFintype (n : ℕ) : Fintype (RealizedPrefix R n) := by
  classical
  exact inferInstanceAs (Fintype
    {w : Fin (n + 1) → A // ∃ a : FuturePath R, ∀ i : Fin (n + 1), a.val i.val = w i})

@[expose] def realizedPrefix (n : ℕ) (a : FuturePath R) : RealizedPrefix R n :=
  ⟨fun i => a.val i.val, a, fun _ => rfl⟩

@[expose] def prefixRepresentative (n : ℕ) (w : RealizedPrefix R n) : FuturePath R :=
  Classical.choose w.property

omit [DiscreteTopology A] [CompactSpace A] [Fintype A] in
theorem realizedPrefix_continuous (n : ℕ) : Continuous (realizedPrefix n : FuturePath R → RealizedPrefix R n) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.val).comp continuous_subtype_val)

omit [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A] in
theorem prefixRepresentative_agrees (n : ℕ) (a : FuturePath R) :
    PrefixAgreement a (prefixRepresentative n (realizedPrefix n a)) n := by
  intro k bound
  exact (Classical.choose_spec (realizedPrefix n a).property ⟨k, by omega⟩).symm

@[expose] def cylinderFunction (n : ℕ) (c : RealizedPrefix R n → ℝ) : C(FuturePath R, ℝ) :=
  ⟨fun a => c (realizedPrefix n a), continuous_of_discreteTopology.comp (realizedPrefix_continuous n)⟩

@[expose] def cylinderLinear (n : ℕ) : (RealizedPrefix R n → ℝ) →ₗ[ℝ] C(FuturePath R, ℝ) where
  toFun := cylinderFunction n
  map_add' c d := by apply ContinuousMap.ext; intro a; rfl
  map_smul' r c := by apply ContinuousMap.ext; intro a; rfl

theorem cylinderLinear_norm_bound (n : ℕ) (c : RealizedPrefix R n → ℝ) : ‖cylinderLinear n c‖ ≤ ‖c‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg c)).mpr
  intro a
  exact norm_le_pi_norm c (realizedPrefix n a)

@[expose] def cylinderOperator (n : ℕ) : (RealizedPrefix R n → ℝ) →L[ℝ] C(FuturePath R, ℝ) :=
  (cylinderLinear n).mkContinuous 1 (fun c => by simpa only [one_mul] using cylinderLinear_norm_bound n c)

@[expose] def cylinderEvaluations (θ : ℝ) (n : ℕ) :
    variationGraph R θ →L[ℝ] (RealizedPrefix R n → ℝ) :=
  ContinuousLinearMap.pi (fun w => (ContinuousMap.evalCLM ℝ (prefixRepresentative n w)).comp (variationPhysical θ))

@[expose] def cylinderApproximation (θ : ℝ) (n : ℕ) :
    variationGraph R θ →L[ℝ] C(FuturePath R, ℝ) :=
  (cylinderOperator n).comp (cylinderEvaluations θ n)

theorem cylinderApproximation_apply (θ : ℝ) (n : ℕ) (v : variationGraph R θ) (a : FuturePath R) :
    cylinderApproximation θ n v a =
      variationPhysical θ v (prefixRepresentative n (realizedPrefix n a)) := rfl

theorem cylinderApproximation_compact (θ : ℝ) (n : ℕ) :
    IsCompactOperator (cylinderApproximation θ n : variationGraph R θ → C(FuturePath R, ℝ)) :=
  (isCompactOperator_of_locallyCompactSpace_rng (cylinderOperator (R := R) n)).comp_clm (cylinderEvaluations θ n)

theorem cylinderApproximation_error (θ : ℝ) (positive : 0 < θ) (n : ℕ) (v : variationGraph R θ) :
    ‖cylinderApproximation θ n v - variationPhysical θ v‖ ≤ θ ^ n * ‖v‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  change ‖cylinderApproximation θ n v a - variationPhysical θ v a‖ ≤ _
  rw [cylinderApproximation_apply, Real.norm_eq_abs, mul_comm]
  exact variationPhysical_increment θ positive.le v n a _ (prefixRepresentative_agrees n a)

-- These are the normed structures, stated directly to keep
-- nested operator-norm inference from unfolding the entire graph.
local instance fixedGraphNorm (θ : ℝ) : NormedAddCommGroup (variationGraph R θ) :=
  (variationGraph R θ).normedAddCommGroup
local instance fixedGraphSpace (θ : ℝ) : NormedSpace ℝ (variationGraph R θ) :=
  (variationGraph R θ).normedSpace
local instance fixedContinuousNorm : NormedAddCommGroup C(FuturePath R, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance fixedContinuousSpace : NormedSpace ℝ C(FuturePath R, ℝ) :=
  ContinuousMap.normedSpace

theorem cylinderApproximation_opNorm_error (θ : ℝ) (positive : 0 < θ) (n : ℕ) :
    ‖cylinderApproximation θ n - (variationPhysical θ : variationGraph R θ →L[ℝ] C(FuturePath R, ℝ))‖ ≤ θ ^ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg positive.le n)
  exact cylinderApproximation_error θ positive n

set_option maxHeartbeats 600000 in
theorem variationPhysical_compact (θ : ℝ) (positive : 0 < θ) (small : θ < 1) :
    IsCompactOperator (variationPhysical θ : variationGraph R θ → C(FuturePath R, ℝ)) := by
  have error : Tendsto (fun n : ℕ =>
      ‖cylinderApproximation θ n - (variationPhysical θ : variationGraph R θ →L[ℝ] C(FuturePath R, ℝ))‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (cylinderApproximation_opNorm_error θ positive)
      (tendsto_pow_atTop_nhds_zero_of_lt_one positive.le small)
  exact isCompactOperator_of_tendsto (tendsto_iff_norm_sub_tendsto_zero.mpr error)
    (Eventually.of_forall (cylinderApproximation_compact θ))

end LeanShared.BilateralShadowingCoding
