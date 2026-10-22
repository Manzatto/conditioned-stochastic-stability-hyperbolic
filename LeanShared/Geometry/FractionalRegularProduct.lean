module
public import LeanShared.Geometry.FractionalHolderCharts
public import LeanShared.Analysis.LocalHolderProduct
public import LeanShared.Analysis.LocalSmoothHolder
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-! Actual scalar C^a times C¹ stays C^a for 0<a<1, in the literal
manifold chart definition. No fractional calculus package is assumed. -/
public noncomputable section
open Set Filter IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

 theorem mul_contMDiff_one {a:ℝ} (ha:0<a) (ha1:a<1) {f g:M→ℂ}
    (hf:Regular (E:=E) (F:=ℂ) a f)
    (hg:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) 1 g) :
    Regular (E:=E) (F:=ℂ) a (fun x=>f x*g x) := by
  have floor : ⌊a⌋₊=0 := Nat.floor_eq_zero.mpr ha1
  refine ⟨ha.le,?_,?_⟩
  · rw [floor]
    exact contMDiff_zero_iff.mpr (hf.differentiable.continuous.mul hg.continuous)
  · intro _ x
    let e := extChartAt (𝓘(ℝ,E)) x
    have ex : e x∈e.target := e.map_source (mem_extChartAt_source x)
    have unequal : a≠(⌊a⌋₊:ℝ) := by simpa only [floor,Nat.cast_zero] using ha.ne'
    obtain ⟨U,hU,hxU,hsub,C,hC,hF⟩ := hf.holder unequal x
    rw [floor] at hF
    simp only [Nat.cast_zero,sub_zero,iteratedFDeriv_zero_eq_comp,
      Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map,chartMap,
      extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] at hF
    have inverse : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 e.symm (e x) :=
      (contMDiffOn_extChartAt_symm (I:=𝓘(ℝ,E)) (n:=1) x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds ex)
    have smoothG : ContDiffAt ℝ 1 (fun y=>g (e.symm y)) (e x) :=
      (hg.contMDiffAt.comp (e x) inverse).contDiffAt
    obtain ⟨W,hW,hxW,_,D,hD,hG⟩ := LocalSmoothHolder.exists_holder_on smoothG ha1.le (hU.mem_nhds hxU)
    obtain ⟨O,hO,hxO,hOS,A,hA,bound⟩ := LocalHolderProduct.exists_bound ha.le hC hD
      (hU.mem_nhds hxU) (hW.mem_nhds hxW) hF hG
    refine ⟨O,hO,hxO,?_,A,hA,?_⟩
    · intro y hy
      change y∈e.target ∩ e.symm ⁻¹' ((fun x=>f x*g x) ⁻¹'
        (extChartAt (𝓘(ℝ,ℂ)) (f x*g x)).source)
      exact ⟨(hsub (hOS hy).1).1,by simp only [extChartAt_model_space_eq_id,PartialEquiv.refl_source,mem_univ,Set.mem_preimage]⟩
    · intro y hy z hz
      have h := bound y hy z hz
      change ‖iteratedFDeriv ℝ ⌊a⌋₊ _ y-iteratedFDeriv ℝ ⌊a⌋₊ _ z‖≤_
      rw [floor]
      simpa only [floor,Nat.cast_zero,sub_zero,iteratedFDeriv_zero_eq_comp,
        Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map,chartMap,
        extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using h
end LeanShared.FractionalManifoldRegularity
