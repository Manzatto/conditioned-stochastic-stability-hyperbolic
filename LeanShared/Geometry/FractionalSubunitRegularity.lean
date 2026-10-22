module
public import LeanShared.Geometry.FractionalRegularProduct
public import LeanShared.Geometry.SmoothFractionalRegularity

/-! Actual fractional regularity of any higher order implies every lower
strictly subunit order. This includes the r−1<1 weight regime and does not
replace finite C^r by smoothness. -/
public noncomputable section
open Set Filter IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

 theorem regular_subunit_of_contMDiff_one {a:ℝ} (ha:0<a) (ha1:a<1) {f:M→ℂ}
    (hf:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) 1 f) : Regular (E:=E) (F:=ℂ) a f := by
  have constant : Regular (E:=E) (F:=ℂ) a (fun _:M=>(1:ℂ)) :=
    regular_of_smooth contMDiff_const ha.le
  simpa only [one_mul] using mul_contMDiff_one ha ha1 constant hf

 theorem lower_subunit {a r:ℝ} (ha:0<a) (ha1:a<1) (har:a<r) {f:M→ℂ}
    (hf:Regular (E:=E) (F:=ℂ) r f) : Regular (E:=E) (F:=ℂ) a f := by
  by_cases large : 1≤r
  · apply regular_subunit_of_contMDiff_one ha ha1
    exact hf.differentiable.of_le (by exact_mod_cast ((Nat.one_le_floor_iff r).mpr large))
  have hr1:r<1 := lt_of_not_ge large
  have hr:0<r := ha.trans har
  have floorA:⌊a⌋₊=0 := Nat.floor_eq_zero.mpr ha1
  have floorR:⌊r⌋₊=0 := Nat.floor_eq_zero.mpr hr1
  refine ⟨ha.le,?_,?_⟩
  · simpa only [floorA,floorR] using hf.differentiable
  · intro _ x
    have neq:r≠(⌊r⌋₊:ℝ) := by simpa only [floorR,Nat.cast_zero] using hr.ne'
    obtain ⟨U,hU,hx,hsub,C,hC,bound⟩ := hf.holder neq x
    let p := extChartAt (𝓘(ℝ,E)) x x
    refine ⟨U∩Metric.ball p (1/2),hU.inter Metric.isOpen_ball,
      ⟨hx,Metric.mem_ball_self (by norm_num)⟩,fun _ hy=>hsub hy.1,C,hC,?_⟩
    intro y hy z hz
    have small:‖y-z‖≤1 := by
      have triangle := dist_triangle y p z
      have hyp:dist y p<1/2 := hy.2
      have hzp:dist p z<1/2 := by simpa only [Metric.mem_ball,dist_comm] using hz.2
      rw [←dist_eq_norm]
      linarith
    have power := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (y-z)) small ha.le har.le
    rw [floorR] at bound
    simp only [Nat.cast_zero,sub_zero] at bound
    have estimate := (bound y hy.1 z hz.1).trans (mul_le_mul_of_nonneg_left power hC)
    change ‖iteratedFDeriv ℝ ⌊a⌋₊ _ y-iteratedFDeriv ℝ ⌊a⌋₊ _ z‖≤_
    rw [floorA]
    simpa only [Nat.cast_zero,sub_zero] using estimate
end LeanShared.FractionalManifoldRegularity
