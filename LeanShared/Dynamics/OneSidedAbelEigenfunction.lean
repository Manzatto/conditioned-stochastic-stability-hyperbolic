module

public import LeanShared.Dynamics.OneSidedAbelApproach
public import Mathlib.Topology.Sequences

/-! A genuine nonnegative Ruelle eigenfunction from actual Abel sums.
The true coefficient radius is finite and positive; actual resolvent
blowup and compact normalized cone families supply a subsequential
limit satisfying the eigen-equation.  No convergence or eigenvector
oracle is assumed, and no simplicity claim is made for arbitrary graphs.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter
open scoped Topology NNReal ENNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

@[expose] def abelApproachData (ψ : C(FuturePath R, ℝ)) (n : ℕ) : AbelParameter ψ :=
  ⟨abelApproachParameter ψ n, weightedAbel_summable_of_lt_radius ψ _ (abelApproachParameter_inside ψ n)⟩

@[expose] def normalizedAbelApproach (ψ : C(FuturePath R, ℝ)) (n : ℕ) : C(FuturePath R, ℝ) :=
  ‖weightedAbel ψ (abelApproachParameter ψ n)‖⁻¹ • weightedAbel ψ (abelApproachParameter ψ n)

theorem normalizedAbelApproach_norm (ψ : C(FuturePath R, ℝ)) (n : ℕ) :
    ‖normalizedAbelApproach ψ n‖ = 1 := by
  rw [normalizedAbelApproach, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (zero_lt_one.trans (weightedAbel_norm_gt_one ψ _
    (abelApproachParameter_positive ψ n) (abelApproachParameter_inside ψ n))).ne'

theorem normalizedAbelApproach_nonnegative (ψ : C(FuturePath R, ℝ)) (n : ℕ) (a : FuturePath R) :
    0 ≤ normalizedAbelApproach ψ n a :=
  mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    (weightedAbel_nonnegative ψ _ (abelApproachParameter ψ n).property (abelApproachData ψ n).property a)

theorem normalizedAbelApproach_ratio (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (n : ℕ) : PrefixRatioBound (normalizedAbelApproach ψ n) θ (Cψ * θ / (1 - θ)) := by
  intro r a b same
  have ratio := weightedAbel_ratio ψ θ Cψ positiveθ smallθ nonnegativeψ potential
    (abelApproachParameter ψ n) (abelApproachParameter ψ n).property (abelApproachData ψ n).property r a b same
  have scaled := mul_le_mul_of_nonneg_left ratio
    (inv_nonneg.mpr (norm_nonneg (weightedAbel ψ (abelApproachParameter ψ n))))
  change ‖weightedAbel ψ (abelApproachParameter ψ n)‖⁻¹ * weightedAbel ψ (abelApproachParameter ψ n) b ≤
    Real.exp (Cψ * θ / (1 - θ) * θ ^ r) *
      (‖weightedAbel ψ (abelApproachParameter ψ n)‖⁻¹ * weightedAbel ψ (abelApproachParameter ψ n) a)
  simpa only [mul_left_comm] using scaled

theorem normalizedAbelApproach_resolvent (ψ : C(FuturePath R, ℝ)) (n : ℕ) :
    normalizedAbelApproach ψ n - (abelApproachParameter ψ n : ℝ) •
      weightedTransferOperator ψ (normalizedAbelApproach ψ n) =
        ‖weightedAbel ψ (abelApproachParameter ψ n)‖⁻¹ • (1 : C(FuturePath R, ℝ)) := by
  let t := abelApproachParameter ψ n
  let c := ‖weightedAbel ψ t‖⁻¹
  change c • weightedAbel ψ t - (t : ℝ) • weightedTransferOperator ψ (c • weightedAbel ψ t) = c • 1
  calc
    _ = c • (weightedAbel ψ t - (t : ℝ) • weightedTransferOperator ψ (weightedAbel ψ t)) := by
      rw [map_smul, smul_sub, smul_comm (t : ℝ) c]
    _ = _ := by rw [weightedAbel_resolvent_identity ψ t (abelApproachData ψ n).property]

theorem weightedTransfer_exists_nonnegative_eigenfunction (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n) :
    ∃ h : C(FuturePath R, ℝ), ‖h‖ = 1 ∧ (∀ a, 0 ≤ h a) ∧
      PrefixRatioBound h θ (Cψ * θ / (1 - θ)) ∧
        weightedTransferOperator ψ h = (abelRadiusReal ψ)⁻¹ • h := by
  have compact := normalizedWeightedAbels_relativelyCompact ψ θ Cψ positiveθ smallθ nonnegativeψ potential
  have member (n : ℕ) : normalizedAbelApproach ψ n ∈
      closure (range (fun p : AbelParameter ψ => ‖weightedAbel ψ p.val‖⁻¹ • weightedAbel ψ p.val)) :=
    subset_closure ⟨abelApproachData ψ n, rfl⟩
  obtain ⟨h, _inside, subsequence, increasing, limit⟩ := compact.tendsto_subseq member
  have normLimit := limit.norm
  have normIdentity : (fun n => ‖(normalizedAbelApproach ψ ∘ subsequence) n‖) = fun _ : ℕ => (1 : ℝ) :=
    funext (fun n => normalizedAbelApproach_norm ψ (subsequence n))
  rw [normIdentity] at normLimit
  have normOne : ‖h‖ = 1 := tendsto_nhds_unique normLimit tendsto_const_nhds
  have nonnegative (a : FuturePath R) : 0 ≤ h a := by
    have point := ((ContinuousMap.evalCLM ℝ a).continuous.tendsto h).comp limit
    exact ge_of_tendsto point (Eventually.of_forall (fun n => normalizedAbelApproach_nonnegative ψ (subsequence n) a))
  have ratio : PrefixRatioBound h θ (Cψ * θ / (1 - θ)) := by
    intro r a b same
    have first := ((ContinuousMap.evalCLM ℝ b).continuous.tendsto h).comp limit
    have second := (((ContinuousMap.evalCLM ℝ a).continuous.tendsto h).comp limit).const_mul
      (Real.exp (Cψ * θ / (1 - θ) * θ ^ r))
    exact le_of_tendsto_of_tendsto first second (Eventually.of_forall (fun n =>
      normalizedAbelApproach_ratio ψ θ Cψ positiveθ smallθ nonnegativeψ potential (subsequence n) r a b same))
  have parameterLimit := (abelApproachParameter_tendsto ψ).comp increasing.tendsto_atTop
  have reciprocalLimit := (weightedAbel_approach_norm_inv_tendsto_zero ψ).comp increasing.tendsto_atTop
  have mappedLimit := ((weightedTransferOperator ψ).continuous.tendsto h).comp limit
  have residueLimit := limit.sub (parameterLimit.smul mappedLimit)
  have zeroLimit := reciprocalLimit.smul (tendsto_const_nhds (x := (1 : C(FuturePath R, ℝ))))
  have residueAsRight : Tendsto (fun n : ℕ =>
      ‖weightedAbel ψ (abelApproachParameter ψ (subsequence n))‖⁻¹ • (1 : C(FuturePath R, ℝ))) atTop
      (𝓝 (h - abelRadiusReal ψ • weightedTransferOperator ψ h)) := by
    convert residueLimit using 1
    funext n
    exact (normalizedAbelApproach_resolvent ψ (subsequence n)).symm
  have equation : h - abelRadiusReal ψ • weightedTransferOperator ψ h = 0 := by
    simpa only [zero_smul] using tendsto_nhds_unique residueAsRight zeroLimit
  have equal : h = abelRadiusReal ψ • weightedTransferOperator ψ h := sub_eq_zero.mp equation
  refine ⟨h, normOne, nonnegative, ratio, ?_⟩
  calc
    _ = (abelRadiusReal ψ)⁻¹ • (abelRadiusReal ψ • weightedTransferOperator ψ h) := by
      rw [smul_smul, inv_mul_cancel₀ (abelRadiusReal_positive ψ).ne', one_smul]
    _ = _ := by rw [← equal]

end LeanShared.BilateralShadowingCoding
