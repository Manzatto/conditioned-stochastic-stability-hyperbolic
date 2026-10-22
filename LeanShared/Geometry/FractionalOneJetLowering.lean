module
public import LeanShared.Geometry.FractionalNativeOneJet
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Tactic

/-! Every actual C^r manifold map is C^(1+a) for 0<a<min(1,r−1).
Only the one-jet lowering needed by the canonical spectral parameters
is proved; no global chart seminorm is assumed. -/
public noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalOneJetLowering
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem jet_lower {a b:ℝ} (ha:0≤a) (lower:a≤b) {f:E→F} {x:E}
    (jet:LocalOneHolderJet.At b f x) : LocalOneHolderJet.At a f x :=by
  obtain ⟨U,openU,inU,C,hC,bound⟩:=jet.2
  let W:=U∩Metric.ball x (1/2)
  refine ⟨jet.1,W,openU.inter Metric.isOpen_ball,⟨inU,Metric.mem_ball_self (by norm_num)⟩,C,hC,?_⟩
  intro y hy z hz
  have small:‖y-z‖≤1:=by
    have triangle:=dist_triangle y x z
    have dy:dist y x<1/2:=hy.2
    have dz:dist x z<1/2:=by simpa only [Metric.mem_ball,dist_comm] using hz.2
    rw [←dist_eq_norm]
    linarith
  exact (bound y hy.1 z hz.1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) small ha lower) hC)

variable {M N:Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
open FractionalManifoldRegularity

private theorem native_contDiffAt {r:ℝ} {f:M→N} (regular:Regular (E:=E) (F:=F) r f)
    {n:ℕ} (hn:n≤⌊r⌋₊) (x:M) :
    ContDiffAt ℝ (n:ℕ∞ω) (chartMap (E:=E) (F:=F) f x) (extChartAt (𝓘(ℝ,E)) x x) :=by
  have c:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) (n:ℕ∞ω) f:=regular.differentiable.of_le (by exact_mod_cast hn)
  have native:=(contMDiffAt_iff.mp (c x)).2
  change ContDiffWithinAt ℝ (n:ℕ∞ω) (chartMap (E:=E) (F:=F) f x)
    (Set.range (𝓘(ℝ,E))) (extChartAt (𝓘(ℝ,E)) x x) at native
  simpa only [ModelWithCorners.range_eq_univ,contDiffWithinAt_univ] using native

theorem native_one_jet {a r:ℝ} (ha:0<a) (ha1:a<1) (lower:a+1<r) {f:M→N}
    (regular:Regular (E:=E) (F:=F) r f) (x:M) :
    LocalOneHolderJet.At a (chartMap (E:=E) (F:=F) f x) (extChartAt (𝓘(ℝ,E)) x x) :=by
  by_cases high:2≤⌊r⌋₊
  · exact LocalOneHolderJet.of_contDiffAt_two ha1.le (native_contDiffAt regular high x)
  have one:1≤⌊r⌋₊:=Nat.le_floor (by simpa only [Nat.cast_one] using (show (1:ℝ)≤r by linarith))
  have floor:⌊r⌋₊=1:=by omega
  have upper:r<2:=by
    have h:=Nat.lt_floor_add_one r
    rw [floor] at h
    norm_num at h
    exact h
  have beta:0<r-1:=by linarith
  have beta1:r-1<1:=by linarith
  have shifted:Regular (E:=E) (F:=F) ((r-1)+1) f:=by simpa only [sub_add_cancel] using regular
  exact jet_lower ha.le (by linarith) (shifted.native_one_jet beta beta1 x)

theorem regular_one_add {a r:ℝ} (ha:0<a) (ha1:a<1) (lower:a+1<r) {f:M→N}
    (regular:Regular (E:=E) (F:=F) r f) : Regular (E:=E) (F:=F) (a+1) f :=by
  have floor:⌊a+1⌋₊=1:=by rw [Nat.floor_add_one ha.le,Nat.floor_eq_zero.mpr ha1]
  have one:1≤⌊r⌋₊:=Nat.le_floor (by simpa only [Nat.cast_one] using (show (1:ℝ)≤r by linarith))
  refine ⟨by positivity,?_,?_⟩
  · rw [floor]
    exact regular.differentiable.of_le (by exact_mod_cast one)
  · intro _ x
    obtain ⟨_,U,openU,inU,C,hC,bound⟩:=native_one_jet ha ha1 lower regular x
    have targetNear:f ⁻¹' (extChartAt (𝓘(ℝ,F)) (f x)).source∈𝓝 x:=
      regular.differentiable.continuous.continuousAt.preimage_mem_nhds
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
end LeanShared.FractionalOneJetLowering
