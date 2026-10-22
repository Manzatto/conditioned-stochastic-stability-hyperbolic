module
public import LeanShared.Analysis.LocalHolderDerivativeCompositionOn
public import LeanShared.Analysis.LocalSmoothHolder
public import LeanShared.Geometry.FractionalDerivativePredecessor
public import LeanShared.Geometry.EuclideanFractionalHolder
public import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic

/-! Actual local C^(1+a) jets, with proved composition and germ transport.
This permits fractional chart calculus for partial coordinate maps
without pretending they are globally differentiable. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace LeanShared.LocalOneHolderJet
variable {E F G:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

@[expose] def At (a:ℝ) (f:E→F) (x:E) : Prop:=
  ContDiffAt ℝ 1 f x ∧∃U:Set E,IsOpen U ∧ x∈U ∧∃C:ℝ,0≤C ∧
    ∀y∈U,∀z∈U,‖fderiv ℝ f y-fderiv ℝ f z‖≤C*‖y-z‖^a

theorem comp {a:ℝ} (ha:0≤a) {f:F→G} {g:E→F} {x:E}
    (hf:At a f (g x)) (hg:At a g x) : At a (f∘g) x :=by
  obtain ⟨U,openU,inU,C,hC,boundF⟩:=hf.2
  obtain ⟨V,openV,inV,D,hD,boundG⟩:=hg.2
  obtain ⟨Of,subf,openf,inf⟩:=mem_nhds_iff.mp (hf.1.eventually (by norm_num))
  obtain ⟨Og,subg,openg,ing⟩:=mem_nhds_iff.mp (hg.1.eventually (by norm_num))
  have df:∀y∈U∩Of,DifferentiableAt ℝ f y:=by
    intro y hy
    have h : ContDiffAt ℝ 1 f y := subf hy.2
    exact h.differentiableAt (by norm_num)
  have dg:∀y∈V∩Og,DifferentiableAt ℝ g y:=by
    intro y hy
    have h : ContDiffAt ℝ 1 g y := subg hy.2
    exact h.differentiableAt (by norm_num)
  obtain ⟨W,openW,inW,_,_,B,hB,bound⟩:=LocalHolderDerivativeCompositionOn.exists_bound hg.1
    ha hC hD ((openU.inter openf).mem_nhds ⟨inU,inf⟩) ((openV.inter openg).mem_nhds ⟨inV,ing⟩)
    df dg (fun y hy z hz=>boundF y hy.1 z hz.1) (fun y hy z hz=>boundG y hy.1 z hz.1)
  exact ⟨hf.1.comp x hg.1,W,openW,inW,B,hB,bound⟩

theorem congr {a:ℝ} {f g:E→F} {x:E} (hf:At a f x) (eqn:g=ᶠ[𝓝 x]f) : At a g x :=by
  obtain ⟨U,openU,inU,C,hC,bound⟩:=hf.2
  obtain ⟨O,subO,openO,inO⟩:=mem_nhds_iff.mp (eqn.fderiv (𝕜:=ℝ))
  refine ⟨hf.1.congr_of_eventuallyEq eqn,U∩O,openU.inter openO,⟨inU,inO⟩,C,hC,?_⟩
  intro y hy z hz
  have ey : fderiv ℝ g y = fderiv ℝ f y := subO hy.2
  have ez : fderiv ℝ g z = fderiv ℝ f z := subO hz.2
  rw [ey,ez]
  exact bound y hy.1 z hz.1

theorem of_contDiffAt_two {a:ℝ} (ha1:a≤1) {f:E→F} {x:E}
    (smooth:ContDiffAt ℝ 2 f x) : At a f x :=by
  obtain ⟨U,openU,inU,_,C,hC,bound⟩:=LocalSmoothHolder.exists_holder_on
    (smooth.fderiv_right (m:=1) (by norm_num)) ha1 (Filter.univ_mem (α:=E))
  exact ⟨smooth.of_le (by norm_num),U,openU,inU,C,hC,bound⟩

theorem of_regular {a:ℝ} (ha:0<a) (ha1:a<1) {f:E→F}
    (regular:FractionalManifoldRegularity.Regular (E:=E) (F:=F) (a+1) f) (x:E) : At a f x :=by
  have floor:⌊a+1⌋₊=1:=by rw [Nat.floor_add_one ha.le,Nat.floor_eq_zero.mpr ha1]
  have smooth:ContDiff ℝ 1 f:=by simpa only [floor,Nat.cast_one] using regular.differentiable.contDiff
  obtain ⟨U,openU,inU,C,hC,bound⟩:=FractionalManifoldRegularity.local_holder_of_regular ha ha1
    (FractionalManifoldRegularity.regular_fderiv_of_regular ha.le regular) x
  exact ⟨smooth.contDiffAt,U,openU,inU,C,hC,bound⟩
end LeanShared.LocalOneHolderJet
