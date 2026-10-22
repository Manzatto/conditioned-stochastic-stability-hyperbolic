module
public import LeanShared.Geometry.LocalFractionalJet
public import LeanShared.Geometry.SmoothFractionalRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Tactic.Ring

/-! The actual real-order manifold class is characterized by local Holder
jets in its literal selected charts. This permits genuine all-order local
calculus without imposing artificial global extensions of chart maps. -/
public noncomputable section
namespace LeanShared.FractionalManifoldRegularity
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M]

theorem floor_fraction_add_nat {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    ⌊a+n⌋₊ = n := by
  rw [Nat.floor_add_natCast ha,Nat.floor_eq_zero.mpr ha1,zero_add]

theorem Regular.chart_jet {a : ℝ} {n : ℕ} (ha : 0 < a) (ha1 : a < 1) {f : M → F}
    (hf : Regular (E := E) (F := F) (a+n) f) (x : M) :
    JetAt n a (chartMap (E := E) (F := F) f x) (extChartAt (𝓘(ℝ,E)) x x) := by
  have floor := floor_fraction_add_nat ha.le ha1 n
  have coordinate : ContDiffAt ℝ n (chartMap (E := E) (F := F) f x) (extChartAt (𝓘(ℝ,E)) x x) := by
    have actual := (contMDiffAt_iff.mp (hf.differentiable.contMDiffAt (x := x))).2
    simpa only [chartMap,ModelWithCorners.range_eq_univ,contDiffWithinAt_univ,floor] using actual
  have unequal : a+n ≠ (⌊a+n⌋₊ : ℝ) := by rw [floor]; linarith
  obtain ⟨U,openU,inU,_inside,C,hC,bound⟩ := hf.holder unequal x
  refine ⟨coordinate,U,openU,inU,C,hC,?_⟩
  intro y hy z hz
  have actual := bound y hy z hz
  rw [floor] at actual
  simpa only [add_sub_cancel_right] using actual

theorem regular_of_chart_jets {a : ℝ} {n : ℕ} (ha : 0 < a) (ha1 : a < 1) {f : M → F}
    (jets : ∀ x : M, JetAt n a (chartMap (E := E) (F := F) f x)
      (extChartAt (𝓘(ℝ,E)) x x)) : Regular (E := E) (F := F) (a+n) f := by
  have floor := floor_fraction_add_nat ha.le ha1 n
  refine ⟨by positivity,?_,?_⟩
  · rw [floor]
    intro x
    apply contMDiffAt_iff.mpr
    constructor
    · have composite := (jets x).smooth.continuousAt.comp (continuousAt_extChartAt x)
      apply composite.congr_of_eventuallyEq
      filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ,E)) x] with y hy
      simp only [chartMap,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
        Function.comp_apply,id_eq,(extChartAt (𝓘(ℝ,E)) x).left_inv hy]
    · simpa only [chartMap,ModelWithCorners.range_eq_univ,contDiffWithinAt_univ] using (jets x).smooth
  · intro _ x
    obtain ⟨U,openU,inU,C,hC,bound⟩ := (jets x).holder
    let target := (extChartAt (𝓘(ℝ,E)) x).target
    refine ⟨U∩target,openU.inter (isOpen_extChartAt_target x),⟨inU,mem_extChartAt_target x⟩,
      ?_,C,hC,?_⟩
    · intro y hy
      exact ⟨hy.2,by simp [chartAt_self_eq]⟩
    · intro y hy z hz
      rw [floor]
      simpa only [add_sub_cancel_right] using bound y hy.1 z hz.1

end LeanShared.FractionalManifoldRegularity
