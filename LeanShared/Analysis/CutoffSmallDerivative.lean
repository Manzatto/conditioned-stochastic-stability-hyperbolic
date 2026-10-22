module
public import LeanShared.Analysis.CompactC1UniformFamily

/-! One actual compact C1 cutoff supplies a positive tolerance converting
small local residual values and actual derivatives into a small global
derivative bound. The tolerance is constructed from the cutoff itself. -/
@[expose] public noncomputable section
open Set Filter
open scoped NNReal ContDiff Topology BoundedContinuousFunction
namespace LeanShared.CutoffSmallDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_cutoff (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ)
    {U : Set E} (openU : IsOpen U) (inside : tsupport ρ ⊆ U)
    (g : E → F) (regular : ContDiffOn ℝ 1 g U) : ContDiff ℝ 1 (fun x => ρ x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport ρ
  · exact hρ.contDiffAt.smul
      ((regular x (inside hx)).contDiffAt (openU.mem_nhds (inside hx)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]

/-- A requested positive global derivative bound determines an actual
positive local C1 tolerance for this fixed cutoff. -/
theorem exists_tolerance (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (compact : HasCompactSupport ρ)
    {U : Set E} (openU : IsOpen U) (inside : tsupport ρ ⊆ U)
    {κ : ℝ} (positive : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : E → F, ContDiffOn ℝ 1 g U →
      (∀ x ∈ tsupport ρ, ‖g x‖ ≤ δ ∧ ‖fderiv ℝ g x‖ ≤ δ) →
      ContDiff ℝ 1 (fun x => ρ x • g x) ∧ ∃ k : ℝ≥0, (k : ℝ) < κ ∧
        ∀ x, ‖fderiv ℝ (fun y => ρ y • g y) x‖ ≤ k := by
  obtain ⟨Lρ, lipρ⟩ := CompactC1Lipschitz.exists_lipschitz ρ hρ compact
  let ρb : E →ᵇ ℝ := ofCompactSupport ρ hρ.continuous compact
  let A : ℝ := (Lρ : ℝ)+‖ρb‖
  have nonnegativeA : 0 ≤ A := add_nonneg Lρ.coe_nonneg (norm_nonneg _)
  let δ := κ / (2*(A+1))
  have positiveδ : 0 < δ := div_pos positive (by positivity)
  have scale : 2*(A+1)*δ = κ := by
    dsimp only [δ]
    field_simp
  have small : A*δ < κ := by
    rw [← scale]
    nlinarith
  refine ⟨δ, positiveδ, ?_⟩
  intro g regular control
  refine ⟨contDiff_cutoff ρ hρ openU inside g regular,
    ⟨A*δ, mul_nonneg nonnegativeA positiveδ.le⟩, small, ?_⟩
  intro x
  change ‖fderiv ℝ (fun y => ρ y • g y) x‖ ≤ A*δ
  by_cases hx : x ∈ tsupport ρ
  · have hdρ := (hρ.differentiable (by norm_num) x).hasFDerivAt
    have hdg := (((regular x (inside hx)).contDiffAt
      (openU.mem_nhds (inside hx))).differentiableAt (by norm_num)).hasFDerivAt
    change ‖fderiv ℝ (ρ • g) x‖ ≤ A*δ
    rw [(hdρ.smul hdg).fderiv]
    calc
      _ ≤ ‖ρ x • fderiv ℝ g x‖+‖(fderiv ℝ ρ x).smulRight (g x)‖ := norm_add_le _ _
      _ = ‖ρ x‖*‖fderiv ℝ g x‖+‖fderiv ℝ ρ x‖*‖g x‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ ‖ρb‖*δ+(Lρ : ℝ)*δ := add_le_add
        (mul_le_mul (ρb.norm_coe_le_norm x) (control x hx).2 (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ lipρ) (control x hx).1
          (norm_nonneg _) Lρ.coe_nonneg)
      _ = A*δ := by dsimp only [A]; ring
  · rw [fderiv_of_notMem_tsupport ℝ
      (fun h => hx (tsupport_smul_subset_left ρ g h)), norm_zero]
    exact mul_nonneg nonnegativeA positiveδ.le

end LeanShared.CutoffSmallDerivative
