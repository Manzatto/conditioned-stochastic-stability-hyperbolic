module
public import LeanShared.Analysis.LocalHolderBilinear
public import LeanShared.Analysis.LocalHolderComposition
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! Actual derivative Holder increments survive nonlinear composition.
The common coordinate neighborhood and bilinear composition constant are
produced, rather than supplied as a fractional chain-rule package. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace LeanShared.LocalHolderDerivativeCompositionOn
variable {E F G:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_bound {f:F→G} {g:E→F}
    {x:E} (gC1:ContDiffAt ℝ 1 g x) {a C D:ℝ} (ha:0≤a) (hC:0≤C) (hD:0≤D)
    {U:Set F} {V:Set E} (hU:U∈𝓝 (g x)) (hV:V∈𝓝 x)
    (df:∀y∈U,DifferentiableAt ℝ f y) (dg:∀y∈V,DifferentiableAt ℝ g y)
    (hf:∀y∈U,∀z∈U,‖fderiv ℝ f y-fderiv ℝ f z‖≤C*‖y-z‖^a)
    (hg:∀y∈V,∀z∈V,‖fderiv ℝ g y-fderiv ℝ g z‖≤D*‖y-z‖^a) :
    ∃W:Set E,IsOpen W ∧ x∈W ∧ W⊆V ∧ g '' W⊆U ∧∃A:ℝ,0≤A ∧
      ∀y∈W,∀z∈W,‖fderiv ℝ (f∘g) y-fderiv ℝ (f∘g) z‖≤A*‖y-z‖^a :=by
  obtain ⟨O,openO,inO,mapsO,A,hA,composed⟩:=
    LocalHolderComposition.exists_bound ha hC gC1 hU hf
  obtain ⟨W,openW,inW,inside,B,hB,bound⟩:=LocalHolderBilinear.exists_bound
    (ContinuousLinearMap.compL ℝ E F G) ha hA hD (openO.mem_nhds inO) hV composed hg
  refine ⟨W,openW,inW,(fun y hy=>(inside hy).2),?_,B,hB,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact mapsO ⟨y,(inside hy).1,rfl⟩
  · intro y hy z hz
    rw [fderiv_comp y (df (g y) (mapsO ⟨y,(inside hy).1,rfl⟩)) (dg y (inside hy).2),
      fderiv_comp z (df (g z) (mapsO ⟨z,(inside hz).1,rfl⟩)) (dg z (inside hz).2)]
    exact bound y hy z hz
end LeanShared.LocalHolderDerivativeCompositionOn
