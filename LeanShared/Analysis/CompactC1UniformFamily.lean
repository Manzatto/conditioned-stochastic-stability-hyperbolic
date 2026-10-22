module
public import LeanShared.Analysis.CompactC1Lipschitz
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! One fixed compact cutoff turns actual uniform C¹ coordinate controls
into global representatives with one Lipschitz constant for the entire
family. The bound is proved from values and genuine derivatives, not from
operator norm upper semicontinuity. -/
public noncomputable section
open Set Filter
open scoped ContDiff Topology BoundedContinuousFunction
namespace LeanShared.CompactC1UniformFamily
variable {E F A:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ρ:E→ℝ) (hρ:ContDiff ℝ 1 ρ) (compact:HasCompactSupport ρ)
  {U:Set E} (openU:IsOpen U) (inside:tsupport ρ⊆U)
  (g:A→E→F) (regular:∀a,ContDiffOn ℝ 1 (g a) U)
  {B D:ℝ} (hB:0≤B) (hD:0≤D)
  (control:∀a x,x∈tsupport ρ→‖g a x‖≤B ∧ ‖fderiv ℝ (g a) x‖≤D)

include hρ compact openU inside regular hB hD control in
theorem exists_uniform_lipschitz : ∃L:NNReal,∀a,LipschitzWith L (fun x=>ρ x • g a x) := by
  obtain ⟨Lρ,lipρ⟩ := CompactC1Lipschitz.exists_lipschitz ρ hρ compact
  let ρb:E→ᵇℝ := ofCompactSupport ρ hρ.continuous compact
  let C:ℝ := (Lρ:ℝ)*B+‖ρb‖*D
  have hC:0≤C := by dsimp [C];positivity
  refine ⟨⟨C,hC⟩,?_⟩
  intro a
  have smooth:ContDiff ℝ 1 (fun x=>ρ x • g a x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx:x∈tsupport ρ
    · exact hρ.contDiffAt.smul
        ((regular a x (inside hx)).contDiffAt (openU.mem_nhds (inside hx)))
    · apply (contDiffAt_const (c:=(0:F))).congr_of_eventuallyEq
      filter_upwards [isClosed_tsupport ρ |>.isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]
  apply lipschitzWith_of_nnnorm_fderiv_le (smooth.differentiable (by norm_num))
  intro x
  change ‖fderiv ℝ (fun x=>ρ x • g a x) x‖≤C
  by_cases hx:x∈tsupport ρ
  · have hdρ := (hρ.differentiable (by norm_num) x).hasFDerivAt
    have hdg := (((regular a x (inside hx)).contDiffAt
      (openU.mem_nhds (inside hx))).differentiableAt (by norm_num)).hasFDerivAt
    change ‖fderiv ℝ (ρ • g a) x‖≤C
    rw [(hdρ.smul hdg).fderiv]
    calc
      _ ≤ ‖ρ x • fderiv ℝ (g a) x‖+‖(fderiv ℝ ρ x).smulRight (g a x)‖ := norm_add_le _ _
      _ = ‖ρ x‖*‖fderiv ℝ (g a) x‖+‖fderiv ℝ ρ x‖*‖g a x‖ := by
        rw [norm_smul,ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ ‖ρb‖*D+(Lρ:ℝ)*B := add_le_add
        (mul_le_mul (ρb.norm_coe_le_norm x) (control a x hx).2 (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ lipρ) (control a x hx).1 (norm_nonneg _) Lρ.coe_nonneg)
      _ = C := by dsimp [C];ring
  · rw [fderiv_of_notMem_tsupport ℝ (fun hy=>hx (tsupport_smul_subset_left ρ (g a) hy)),norm_zero]
    exact hC
end LeanShared.CompactC1UniformFamily
