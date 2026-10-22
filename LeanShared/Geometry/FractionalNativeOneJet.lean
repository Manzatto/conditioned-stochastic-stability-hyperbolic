module
public import LeanShared.Geometry.LocalOneHolderJet
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! Literal manifold C^(1+a) supplies an actual local derivative Holder
jet of its native chart expression. No chart norm source is assumed. -/
public noncomputable section
open Set
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F M N:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

theorem Regular.native_one_jet {a:ℝ} (ha:0<a) (ha1:a<1) {f:M→N}
    (regular:Regular (E:=E) (F:=F) (a+1) f) (x:M) :
    LocalOneHolderJet.At a (chartMap (E:=E) (F:=F) f x) (extChartAt (𝓘(ℝ,E)) x x) :=by
  have floor:⌊a+1⌋₊=1:=by rw [Nat.floor_add_one ha.le,Nat.floor_eq_zero.mpr ha1]
  have c1:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f:=by
    simpa only [floor,Nat.cast_one] using regular.differentiable
  have smooth:ContDiffAt ℝ 1 (chartMap (E:=E) (F:=F) f x) (extChartAt (𝓘(ℝ,E)) x x):=by
    have native:=(contMDiffAt_iff.mp (c1 x)).2
    change ContDiffWithinAt ℝ 1 (chartMap (E:=E) (F:=F) f x)
      (Set.range (𝓘(ℝ,E))) (extChartAt (𝓘(ℝ,E)) x x) at native
    simpa only [ModelWithCorners.range_eq_univ,contDiffWithinAt_univ] using native
  have unequal:a+1≠(⌊a+1⌋₊:ℝ):=by rw [floor];norm_num;exact ha.ne'
  obtain ⟨U,openU,inU,_,C,hC,bound⟩:=regular.holder unequal x
  refine ⟨smooth,U,openU,inU,C,hC,?_⟩
  intro y hy z hz
  have estimate:=bound y hy z hz
  rw [floor] at estimate
  have identify:=norm_iterated_difference_succ (chartMap (E:=E) (F:=F) f x) 0 y z
  simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,
    LinearIsometryEquiv.norm_map] at identify
  rw [identify] at estimate
  simpa only [Nat.cast_one,add_sub_cancel_right] using estimate
end LeanShared.FractionalManifoldRegularity
