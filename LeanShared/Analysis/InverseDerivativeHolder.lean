module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Quantitative inverse first-jet Holder control from actual local inverse
identities. The derivative inverse formula and spatial Lipschitz factor are
proved, not supplied as a fractional inverse calculus source. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.InverseDerivativeHolder

 theorem inverse_difference_le {R:Type*} [NormedRing R] (A B C D:R)
    (left:C*A=1) (right:B*D=1) : ‖C-D‖≤‖C‖*‖A-B‖*‖D‖ :=by
  have identity:C-D=C*(B-A)*D:=by
    calc
      _ = C*(B*D)-(C*A)*D:=by rw [left,right];simp
      _ = _:=by noncomm_ring
  rw [identity]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans_eq (by rw [norm_sub_rev])) (norm_nonneg _))

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem bound {f g:E→E} {K:Set E} (convex:Convex ℝ K)
    (df:∀y∈K,DifferentiableAt ℝ f (g y)) (dg:∀y∈K,DifferentiableAt ℝ g y)
    (left:∀y∈K,(g∘f)=ᶠ[𝓝 (g y)]id) (right:∀y∈K,(f∘g)=ᶠ[𝓝 y]id)
    {a M H:ℝ} (ha:0≤a) (hM:0≤M) (hH:0≤H)
    (value:∀y∈K,‖fderiv ℝ g y‖≤M)
    (holder:∀y∈K,∀z∈K,‖fderiv ℝ f (g y)-fderiv ℝ f (g z)‖≤H*‖g y-g z‖^a) :
    ∀y∈K,∀z∈K,‖fderiv ℝ g y-fderiv ℝ g z‖≤(M*H*M^a*M)*‖y-z‖^a :=by
  have first:∀y∈K,(fderiv ℝ g y).comp (fderiv ℝ f (g y))=ContinuousLinearMap.id ℝ E:=by
    intro y hy
    have same:f (g y)=y:=(right y hy).eq_of_nhds
    have dgy:DifferentiableAt ℝ g (f (g y)):=by rw [same];exact dg y hy
    have identity:=(left y hy).fderiv_eq (𝕜:=ℝ)
    rw [fderiv_comp (g y) dgy (df y hy),fderiv_id,same] at identity
    exact identity
  have second:∀y∈K,(fderiv ℝ f (g y)).comp (fderiv ℝ g y)=ContinuousLinearMap.id ℝ E:=by
    intro y hy
    have identity:=(right y hy).fderiv_eq (𝕜:=ℝ)
    rw [fderiv_comp y (df y hy) (dg y hy),fderiv_id] at identity
    exact identity
  intro y hy z hz
  have lip:‖g y-g z‖≤M*‖y-z‖:=
    Convex.norm_image_sub_le_of_norm_fderiv_le dg value convex hz hy
  have forward:‖fderiv ℝ f (g y)-fderiv ℝ f (g z)‖≤H*M^a*‖y-z‖^a:=by
    calc
      _ ≤ H*‖g y-g z‖^a:=holder y hy z hz
      _ ≤ H*(M*‖y-z‖)^a:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) lip ha) hH
      _ = _:=by rw [Real.mul_rpow hM (norm_nonneg _)];ring
  calc
    _ ≤ ‖fderiv ℝ g y‖*‖fderiv ℝ f (g y)-fderiv ℝ f (g z)‖*‖fderiv ℝ g z‖:=
      inverse_difference_le _ _ _ _ (first y hy) (second z hz)
    _ ≤ M*(H*M^a*‖y-z‖^a)*M:=
      mul_le_mul (mul_le_mul (value y hy) forward (norm_nonneg _) hM) (value z hz)
        (norm_nonneg _) (by positivity)
    _ = _:=by ring
end LeanShared.InverseDerivativeHolder
