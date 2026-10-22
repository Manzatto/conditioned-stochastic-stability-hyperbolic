module
public import LeanShared.Geometry.FractionalNativeOneJet
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Tactic

/-! Actual nonlinear C^(1+a) composition between manifolds. Preferred
coordinate jets compose by a proved germ identity; no global coordinate
representative or fractional composition contract is assumed. -/
public noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F G M N P:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace P] [ChartedSpace G P]

private theorem of_native_jets {a:ℝ} (ha:0<a) (ha1:a<1) {f:M→N}
    (c1:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f)
    (jets:∀x,LocalOneHolderJet.At a (chartMap (E:=E) (F:=F) f x) (extChartAt (𝓘(ℝ,E)) x x)) :
    Regular (E:=E) (F:=F) (a+1) f :=by
  have floor:⌊a+1⌋₊=1:=by rw [Nat.floor_add_one ha.le,Nat.floor_eq_zero.mpr ha1]
  refine ⟨by positivity,?_,?_⟩
  · rw [floor]
    exact c1
  · intro _ x
    obtain ⟨_,U,openU,inU,C,hC,bound⟩:=jets x
    have targetNear:f ⁻¹' (extChartAt (𝓘(ℝ,F)) (f x)).source∈𝓝 x:=
      c1.continuous.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I:=𝓘(ℝ,F)) (f x)).mem_nhds (mem_extChartAt_source (I:=𝓘(ℝ,F)) (f x)))
    have targetNear':f ⁻¹' (extChartAt (𝓘(ℝ,F)) (f x)).source∈
        𝓝 ((extChartAt (𝓘(ℝ,E)) x).symm (extChartAt (𝓘(ℝ,E)) x x)):=by
      rw [extChartAt_to_inv]
      exact targetNear
    have domainNear:chartDomain (E:=E) (F:=F) f x∈𝓝 (extChartAt (𝓘(ℝ,E)) x x):=
      inter_mem ((isOpen_extChartAt_target (I:=𝓘(ℝ,E)) x).mem_nhds (mem_extChartAt_target (I:=𝓘(ℝ,E)) x))
        ((continuousAt_extChartAt_symm (I:=𝓘(ℝ,E)) x).preimage_mem_nhds targetNear')
    obtain ⟨D,subD,openD,inD⟩:=mem_nhds_iff.mp domainNear
    refine ⟨U∩D,openU.inter openD,⟨inU,inD⟩,(fun y hy=>subD hy.2),C,hC,?_⟩
    intro y hy z hz
    rw [floor]
    have identify:=norm_iterated_difference_succ (chartMap (E:=E) (F:=F) f x) 0 y z
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,
      LinearIsometryEquiv.norm_map] at identify
    rw [identify]
    simpa only [Nat.cast_one,add_sub_cancel_right] using bound y hy.1 z hz.1

theorem Regular.comp_one_add_manifold {a:ℝ} (ha:0<a) (ha1:a<1)
    {f:N→P} {g:M→N} (hf:Regular (E:=F) (F:=G) (a+1) f)
    (hg:Regular (E:=E) (F:=F) (a+1) g) :
    Regular (E:=E) (F:=G) (a+1) (f∘g) :=by
  have floor:⌊a+1⌋₊=1:=by rw [Nat.floor_add_one ha.le,Nat.floor_eq_zero.mpr ha1]
  have fc1:ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,G)) 1 f:=by simpa only [floor,Nat.cast_one] using hf.differentiable
  have gc1:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 g:=by simpa only [floor,Nat.cast_one] using hg.differentiable
  apply of_native_jets ha ha1 (fc1.comp gc1)
  intro x
  let e:=extChartAt (𝓘(ℝ,E)) x
  let e':=extChartAt (𝓘(ℝ,F)) (g x)
  let e'':=extChartAt (𝓘(ℝ,G)) (f (g x))
  let C:E→F:=chartMap (E:=E) (F:=F) g x
  let D:F→G:=chartMap (E:=F) (F:=G) f (g x)
  have value:C (e x)=e' (g x):=by
    change e' (g (e.symm (e x)))=e' (g x)
    rw [extChartAt_to_inv]
  have first:LocalOneHolderJet.At a C (e x):=hg.native_one_jet ha ha1 x
  have last:LocalOneHolderJet.At a D (C (e x)):=by
    rw [value]
    exact hf.native_one_jet ha ha1 (g x)
  have combined:LocalOneHolderJet.At a (D∘C) (e x):=
    LocalOneHolderJet.comp (f:=D) (g:=C) (x:=e x) ha.le last first
  apply LocalOneHolderJet.congr combined
  have targetNear:e'.source∈𝓝 (g (e.symm (e x))):=by
    rw [extChartAt_to_inv]
    exact (isOpen_extChartAt_source (I:=𝓘(ℝ,F)) (g x)).mem_nhds (mem_extChartAt_source (I:=𝓘(ℝ,F)) (g x))
  have near:(g∘e.symm) ⁻¹' e'.source∈𝓝 (e x):=
    (gc1.continuous.continuousAt.comp (continuousAt_extChartAt_symm (I:=𝓘(ℝ,E)) x)).preimage_mem_nhds targetNear
  filter_upwards [near] with y hy
  have inside:g (e.symm y)∈e'.source:=hy
  change e'' (f (g (e.symm y)))=e'' (f (e'.symm (e' (g (e.symm y)))))
  rw [e'.left_inv inside]
end LeanShared.FractionalManifoldRegularity
