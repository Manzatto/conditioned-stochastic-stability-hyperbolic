module
public import LeanShared.Geometry.FractionalNativeOneJet
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Tactic

/-! Actual C^(1+a) derivative Holder jets in every genuine smooth source
and target chart. The coordinate-change calculus and germ identity are
proved; arbitrary partial chart maps are never made globally smooth. -/
public noncomputable section
open Set Filter IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F M N:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem Regular.one_jet_in_charts {a:ℝ} (ha:0<a) (ha1:a<1) {f:M→N}
    (regular:Regular (E:=E) (F:=F) (a+1) f)
    (c:OpenPartialHomeomorph M E) (d:OpenPartialHomeomorph N F)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,F)) ∞ N)
    (y:E) (source:y∈c.target) (target:f (c.symm y)∈d.source) :
    LocalOneHolderJet.At a (d∘f∘c.symm) y :=by
  let x:=c.symm y
  let e:=extChartAt (𝓘(ℝ,E)) x
  let e':=extChartAt (𝓘(ℝ,F)) (f x)
  let A:E→E:=e∘c.symm
  let C:E→F:=chartMap (E:=E) (F:=F) f x
  let B:F→F:=d∘e'.symm
  have inverse:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ c.symm y:=
    contMDiffAt_symm_of_mem_maximalAtlas hc source
  have smoothA:ContDiffAt ℝ 2 A y:=by
    have forward:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ e x:=contMDiffAt_extChartAt
    exact (forward.comp y inverse).contDiffAt.of_le (by simp)
  have valueC:C (A y)=e' (f x):=by
    change e' (f (e.symm (e x)))=e' (f x)
    rw [extChartAt_to_inv]
  have smoothB:ContDiffAt ℝ 2 B (e' (f x)):=by
    have inv:ContMDiffAt (𝓘(ℝ,F)) (𝓘(ℝ,F)) ∞ e'.symm (e' (f x)):=
      (contMDiffWithinAt_extChartAt_symm_target_self (I:=𝓘(ℝ,F)) (n:=∞) (f x)).contMDiffAt
        ((isOpen_extChartAt_target (I:=𝓘(ℝ,F)) (f x)).mem_nhds (mem_extChartAt_target (I:=𝓘(ℝ,F)) (f x)))
    have final:ContMDiffAt (𝓘(ℝ,F)) (𝓘(ℝ,F)) ∞ d (e'.symm (e' (f x))):=by
      rw [extChartAt_to_inv]
      exact contMDiffAt_of_mem_maximalAtlas hd target
    exact (final.comp (e' (f x)) inv).contDiffAt.of_le (by simp)
  have native:LocalOneHolderJet.At a C (A y):=regular.native_one_jet ha ha1 x
  have first:=LocalOneHolderJet.comp ha.le native (LocalOneHolderJet.of_contDiffAt_two ha1.le smoothA)
  have last:LocalOneHolderJet.At a B (C (A y)):=by
    rw [valueC]
    exact LocalOneHolderJet.of_contDiffAt_two ha1.le smoothB
  have combined : LocalOneHolderJet.At a (B∘(C∘A)) y :=
    LocalOneHolderJet.comp (f:=B) (g:=C∘A) (x:=y) ha.le last first
  apply LocalOneHolderJet.congr combined
  have nearSource:c.symm ⁻¹' e.source∈𝓝 y:=inverse.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))
  have nearTarget:(f∘c.symm) ⁻¹' e'.source∈𝓝 y:=
    (regular.differentiable.continuous.continuousAt.comp inverse.continuousAt).preimage_mem_nhds
      ((isOpen_extChartAt_source (f x)).mem_nhds (mem_extChartAt_source (f x)))
  filter_upwards [nearSource,nearTarget] with z hz hz'
  change d (f (c.symm z))=d (e'.symm (e' (f (e.symm (e (c.symm z))))))
  have hzTarget : f (c.symm z) ∈ e'.source := hz'
  rw [e.left_inv hz,e'.left_inv hzTarget]
end LeanShared.FractionalManifoldRegularity
