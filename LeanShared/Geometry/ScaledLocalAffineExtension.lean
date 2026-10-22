module
public import LeanShared.Geometry.CutoffAffineDiffeomorphism
public import LeanShared.Analysis.ScaledCutoffDerivative

/-! A local regular map admits a global regular affine extension with a
derivative tolerance chosen before the localization radius. Only the
displacement at the centre is scaled by that radius. -/
@[expose] public noncomputable section
open Set Filter Function Metric
open scoped NNReal Manifold ContDiff Topology
namespace LeanShared.ScaledLocalAffineExtension
open FractionalManifoldRegularity
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The tolerance precedes every choice of radius, affine prototype, and map.
The conclusion includes an actual global homeomorphism, full real-order
regularity of both directions, and the actual global derivative margin. -/
theorem exists_uniform_scaled_tolerance {r η K : ℝ}
    (hr : 1 ≤ r) (positiveη : 0 < η) (nonnegativeK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ → E → ℝ, ∀ R : ℝ, 0 < R →
      ContDiff ℝ ∞ (ρ R) ∧ HasCompactSupport (ρ R) ∧
      tsupport (ρ R) ⊆ closedBall 0 R ∧
      (∀ y ∈ closedBall 0 (R/2), ρ R y = 1) ∧
      ∀ A : E ≃L[ℝ] F, ‖A.symm.toContinuousLinearMap‖ ≤ K → ∀ b : F,
      ∀ U : Set E, IsOpen U → closedBall 0 R ⊆ U →
        ∀ h : E → F, ContDiffOn ℝ (⌊r⌋₊ : ℕ) h U →
          (r ≠ (⌊r⌋₊ : ℝ) → ∀ y ∈ U, JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) h y) →
          ‖h 0-b‖ ≤ δ*R →
          (∀ y ∈ closedBall 0 R, ‖fderiv ℝ h y-A.toContinuousLinearMap‖ ≤ δ) →
            ∃ H : E ≃ₜ F, (∀ y, H y = A y+b+ρ R y • (h y-(A y+b))) ∧
              Regular (E := E) (F := F) r H ∧ Regular (E := F) (F := E) r H.symm ∧
              (∀ y, ‖fderiv ℝ H y-A.toContinuousLinearMap‖ < η) ∧
              (∀ y ∈ closedBall 0 (R/2), H y = h y) ∧
              ∀ y, y ∉ closedBall 0 R → H y = A y+b := by
  let κ : ℝ := min η (K+1)⁻¹
  have positiveκ : 0 < κ := lt_min positiveη (by positivity)
  obtain ⟨δ, positiveδ, ρ, budgets⟩ :=
    ScaledCutoffDerivative.exists_uniform_budget (E := E) (F := F) positiveκ
  refine ⟨δ, positiveδ, ρ, ?_⟩
  intro R positiveR
  obtain ⟨smoothρ, compactρ, supportρ, oneρ, budget⟩ := budgets R positiveR
  refine ⟨smoothρ, compactρ, supportρ, oneρ, ?_⟩
  intro A inverseBound b U openU inside h smooth holder center derivative
  let g : E → F := fun y => h y-(A y+b)
  have localSmooth (y : E) (hy : y ∈ U) : ContDiffAt ℝ (⌊r⌋₊ : ℕ) h y :=
    (smooth y hy).contDiffAt (openU.mem_nhds hy)
  have residualSmooth : ContDiffOn ℝ (⌊r⌋₊ : ℕ) g U := by
    intro y hy
    exact ((localSmooth y hy).sub (A.contDiff.contDiffAt.add contDiffAt_const)).contDiffWithinAt
  have residualHolder (unequal : r ≠ (⌊r⌋₊ : ℝ)) (y : E) (hy : y ∈ U) :
      JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) g y := by
    have negativeSmooth : ContDiff ℝ ∞ (fun v => -(A v+b)) :=
      (A.contDiff.add contDiff_const).neg
    have subunit : r-(⌊r⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one r]
    have negativeJet : JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) (fun v => -(A v+b)) y :=
      JetAt.of_contDiff_succ subunit (negativeSmooth.of_le (by simp)).contDiffAt
    simpa only [g, sub_eq_add_neg] using (holder unequal y hy).add negativeJet
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hr)
  have residualCenter : ‖g 0‖ ≤ δ*R := by
    simpa only [g, map_zero, zero_add] using center
  have residualDerivative (y : E) (hy : y ∈ closedBall 0 R) :
      ‖fderiv ℝ (g) y‖ ≤ δ := by
    have actual : HasFDerivAt (g)
        (fderiv ℝ (h) y-A.toContinuousLinearMap) y :=
      ((localSmooth y (inside hy)).differentiableAt
        (by exact_mod_cast (Nat.ne_of_gt order))).hasFDerivAt.sub (A.hasFDerivAt.add_const b)
    rw [actual.fderiv]
    exact derivative y hy
  obtain ⟨cutoffC1, k, small, bound⟩ := budget U openU inside (g)
    (residualSmooth.of_le (by exact_mod_cast order)) residualCenter residualDerivative
  have cutoffRegular := CutoffAffineDiffeomorphism.regular_cutoff (ρ R) smoothρ
    openU (supportρ.trans inside) (zero_le_one.trans hr) (g)
    residualSmooth residualHolder
  have inverseThreshold : (K+1)⁻¹ ≤ (‖A.symm.toContinuousLinearMap‖+1)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (show 0 < ‖A.symm.toContinuousLinearMap‖+1 by positivity) (show ‖A.symm.toContinuousLinearMap‖+1 ≤ K+1 by linarith)
  obtain ⟨H, literal, forward, inverse⟩ := SmallAffinePerturbation.exists_regular_homeomorph
    A b hr (fun y => ρ R y • (h y-(A y+b))) cutoffRegular k bound
    (CutoffAffineDiffeomorphism.small_of_inflated A k
      (small.trans_le ((min_le_right _ _).trans inverseThreshold)))
  refine ⟨H, literal, forward, inverse, ?_, ?_, ?_⟩
  · intro y
    have same : (H : E → F) = SmallAffinePerturbation.map A b
        (fun z => ρ R z • g z) := funext literal
    rw [same, (SmallAffinePerturbation.hasFDerivAt_map A b
      (cutoffC1.differentiable (by norm_num)) y).fderiv]
    have cancel : (A.toContinuousLinearMap+fderiv ℝ (fun z => ρ R z • g z) y)-
        A.toContinuousLinearMap = fderiv ℝ (fun z => ρ R z • g z) y := by abel
    rw [cancel]
    exact (bound y).trans_lt (small.trans_le (min_le_left _ _))
  · intro y hy
    rw [literal y, oneρ y hy, one_smul]
    abel
  · intro y hy
    have outside : y ∉ tsupport (ρ R) := fun h => hy (supportρ h)
    rw [literal y, image_eq_zero_of_notMem_tsupport outside, zero_smul, add_zero]

end LeanShared.ScaledLocalAffineExtension
