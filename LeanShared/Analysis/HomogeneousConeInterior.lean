module
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Analysis.Normed.Module.Basic

/-! The complement of the interior of a positively homogeneous cone is
itself invariant under positive dilation. -/
public noncomputable section
open Set
open scoped Pointwise
namespace LeanShared.HomogeneousConeInterior
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem outside_scale {C:Set E}
    (scale:∀r:ℝ,0≤r → ∀v∈C,r • v∈C)
    {r:ℝ} (positive:0<r) {v:E} (outside:v∉interior C):r • v∉interior C:=by
  intro inside
  have subset:r⁻¹ • C⊆C:=by
    rintro z ⟨y,hy,rfl⟩
    exact scale _ (inv_nonneg.mpr positive.le) _ hy
  have member:r⁻¹ • (r • v)∈r⁻¹ • interior C:=⟨r • v,inside,rfl⟩
  rw [←interior_smul₀ (inv_ne_zero positive.ne')] at member
  have result:=interior_mono subset member
  exact outside (by simpa only [inv_smul_smul₀ positive.ne'] using result)
end LeanShared.HomogeneousConeInterior
