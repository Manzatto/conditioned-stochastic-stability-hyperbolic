module

public import LeanShared.Dynamics.OneSidedRatioVariation
public import LeanShared.Dynamics.OneSidedCylinderApproximation

/-! Any actual family in the proved logarithmic prefix cone has a
relatively compact family of uniform-norm normalizations.  This applies
to finite positive Abel sums, not merely individual transfer iterates.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A U : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

local instance coneFamilyGraphNorm (θ : ℝ) : NormedAddCommGroup (variationGraph R θ) :=
  (variationGraph R θ).normedAddCommGroup
local instance coneFamilyGraphSpace (θ : ℝ) : NormedSpace ℝ (variationGraph R θ) :=
  (variationGraph R θ).normedSpace
local instance coneFamilyContinuousNorm : NormedAddCommGroup C(FuturePath R, ℝ) :=
  ContinuousMap.instNormedAddCommGroup
local instance coneFamilyContinuousSpace : NormedSpace ℝ C(FuturePath R, ℝ) :=
  ContinuousMap.normedSpace

@[expose] def normalizedConeGraph (f : C(FuturePath R, ℝ)) (θ K : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ ≤ 1) (nonnegativeK : 0 ≤ K)
    (positiveF : ∀ a, 0 ≤ f a) (ratio : PrefixRatioBound f θ K) : variationGraph R θ :=
  ‖f‖⁻¹ • ratioVariationElement f θ K positiveθ smallθ nonnegativeK positiveF ratio

omit [Fintype A] in
theorem normalizedConeGraph_physical (f : C(FuturePath R, ℝ)) (θ K : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ ≤ 1) (nonnegativeK : 0 ≤ K)
    (positiveF : ∀ a, 0 ≤ f a) (ratio : PrefixRatioBound f θ K) :
    variationPhysical θ (normalizedConeGraph f θ K positiveθ smallθ nonnegativeK positiveF ratio) = ‖f‖⁻¹ • f := by
  rw [normalizedConeGraph, map_smul]
  rfl

omit [Fintype A] in
theorem normalizedConeGraph_norm (f : C(FuturePath R, ℝ)) (θ K : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ ≤ 1) (nonnegativeK : 0 ≤ K)
    (positiveF : ∀ a, 0 ≤ f a) (ratio : PrefixRatioBound f θ K) :
    ‖normalizedConeGraph f θ K positiveθ smallθ nonnegativeK positiveF ratio‖ ≤ Real.exp K := by
  rw [normalizedConeGraph, norm_smul, norm_inv, norm_norm]
  by_cases zero : ‖f‖ = 0
  · simp only [zero, inv_zero, zero_mul]
    exact (Real.exp_pos _).le
  · calc
      _ ≤ ‖f‖⁻¹ * (Real.exp K * ‖f‖) :=
        mul_le_mul_of_nonneg_left
          (ratioVariationElement_norm f θ K positiveθ smallθ nonnegativeK positiveF ratio)
          (inv_nonneg.mpr (norm_nonneg f))
      _ = _ := by field_simp

theorem normalizedConeFamily_relativelyCompact (f : U → C(FuturePath R, ℝ)) (θ K : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeK : 0 ≤ K)
    (positiveF : ∀ u a, 0 ≤ f u a) (ratio : ∀ u, PrefixRatioBound (f u) θ K) :
    IsCompact (closure (range (fun u => ‖f u‖⁻¹ • f u))) := by
  have physicalCompact : IsCompactOperator ((variationPhysical θ : variationGraph R θ →L[ℝ]
      C(FuturePath R, ℝ)).toLinearMap) := variationPhysical_compact θ positiveθ smallθ
  have compact := physicalCompact.isCompact_closure_image_closedBall
    (f := (variationPhysical θ : variationGraph R θ →L[ℝ] C(FuturePath R, ℝ)).toLinearMap) (Real.exp K)
  apply compact.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨u, rfl⟩
  refine ⟨normalizedConeGraph (f u) θ K positiveθ smallθ.le nonnegativeK (positiveF u) (ratio u), ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      normalizedConeGraph_norm (f u) θ K positiveθ smallθ.le nonnegativeK (positiveF u) (ratio u)
  · exact normalizedConeGraph_physical (f u) θ K positiveθ smallθ.le nonnegativeK (positiveF u) (ratio u)

end LeanShared.BilateralShadowingCoding
