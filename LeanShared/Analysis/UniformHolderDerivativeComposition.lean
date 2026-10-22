module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Explicit uniform one-jet composition bounds on valid domains. All
constants depend only on the displayed value and Holder controls; no
parameter topology or global differentiability is required. -/
public noncomputable section
namespace LeanShared.UniformHolderDerivativeComposition
variable {E F G:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bound {f:F→G} {g:E→F} {K:Set E} {V:Set F} (convex:Convex ℝ K)
    (maps:g '' K⊆V) (df:∀x∈V,DifferentiableAt ℝ f x)
    (dg:∀x∈K,DifferentiableAt ℝ g x)
    {a A B C D:ℝ} (ha:0≤a) (hA:0≤A) (hB:0≤B) (hC:0≤C) (_hD:0≤D)
    (vf:∀x∈V,‖fderiv ℝ f x‖≤A) (vg:∀x∈K,‖fderiv ℝ g x‖≤B)
    (hf:∀x∈V,∀y∈V,‖fderiv ℝ f x-fderiv ℝ f y‖≤C*‖x-y‖^a)
    (hg:∀x∈K,∀y∈K,‖fderiv ℝ g x-fderiv ℝ g y‖≤D*‖x-y‖^a) :
    (∀x∈K,‖fderiv ℝ (f∘g) x‖≤A*B) ∧
      ∀x∈K,∀y∈K,‖fderiv ℝ (f∘g) x-fderiv ℝ (f∘g) y‖≤
        (C*B^a*B+A*D)*‖x-y‖^a :=by
  have valid:∀x∈K,g x∈V:=fun x hx=>maps ⟨x,hx,rfl⟩
  constructor
  · intro x hx
    rw [fderiv_comp x (df _ (valid x hx)) (dg x hx)]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (vf _ (valid x hx)) (vg x hx) (norm_nonneg _) hA)
  · intro x hx y hy
    rw [fderiv_comp x (df _ (valid x hx)) (dg x hx),
      fderiv_comp y (df _ (valid y hy)) (dg y hy)]
    have lip:‖g x-g y‖≤B*‖x-y‖:=
      Convex.norm_image_sub_le_of_norm_fderiv_le dg vg convex hy hx
    have first:‖fderiv ℝ f (g x)-fderiv ℝ f (g y)‖≤C*B^a*‖x-y‖^a:=by
      calc
        _ ≤ C*‖g x-g y‖^a:=hf _ (valid x hx) _ (valid y hy)
        _ ≤ C*(B*‖x-y‖)^a:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) lip ha) hC
        _ = _:=by rw [Real.mul_rpow hB (norm_nonneg _)];ring
    have split:(fderiv ℝ f (g x)).comp (fderiv ℝ g x)-
        (fderiv ℝ f (g y)).comp (fderiv ℝ g y)=
      (fderiv ℝ f (g x)-fderiv ℝ f (g y)).comp (fderiv ℝ g x)+
        (fderiv ℝ f (g y)).comp (fderiv ℝ g x-fderiv ℝ g y):=by
      ext z
      simp only [sub_apply,add_apply,
        ContinuousLinearMap.comp_apply,map_sub]
      abel
    rw [split]
    calc
      _ ≤ _:=norm_add_le _ _
      _ ≤ ‖fderiv ℝ f (g x)-fderiv ℝ f (g y)‖*‖fderiv ℝ g x‖+
          ‖fderiv ℝ f (g y)‖*‖fderiv ℝ g x-fderiv ℝ g y‖:=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ (C*B^a*‖x-y‖^a)*B+A*(D*‖x-y‖^a):=
        add_le_add (mul_le_mul first (vg x hx) (norm_nonneg _) (by positivity))
          (mul_le_mul (vf _ (valid y hy)) (hg x hx y hy) (norm_nonneg _) hA)
      _ = _:=by ring
end LeanShared.UniformHolderDerivativeComposition
