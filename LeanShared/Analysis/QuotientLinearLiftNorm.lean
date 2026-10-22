module
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Analysis.Normed.Operator.Basic

/-! A bound before quotient descent is retained by the actual continuous
linear quotient lift. The quotient seminorm is the infimum over genuine
representatives; no norm comparison source is assumed. -/
public noncomputable section
set_option maxHeartbeats 800000
namespace LeanShared.QuotientLinearLiftNorm
variable {𝕜 E F:Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

 theorem bound (S:Submodule 𝕜 E) (f:E→L[𝕜]F) (h:S≤f.ker)
    {C:ℝ} (hC:0≤C) (estimate:∀x,‖f x‖≤C*‖x‖) : ‖S.liftQL f h‖≤C := by
  let hom:NormedAddGroupHom E F :=
    { toFun:=f
      map_add':=f.map_add
      bound':=⟨C,estimate⟩ }
  have homBound:‖hom‖≤C:=NormedAddGroupHom.opNorm_le_bound hom hC estimate
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have result:=QuotientAddGroup.norm_lift_apply_le hom (fun x hx=>h hx) v
  change ‖S.liftQL f h v‖≤‖hom‖*‖v‖ at result
  exact result.trans (mul_le_mul_of_nonneg_right homBound (norm_nonneg v))
end LeanShared.QuotientLinearLiftNorm
