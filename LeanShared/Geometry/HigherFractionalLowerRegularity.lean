module
public import LeanShared.Geometry.FractionalJetCharacterization
import Mathlib.Tactic.Linarith

/-! Strict lowering to any positive noninteger order, including orders
above one. The proof retains the actual top derivative when the source
order lies in the same integer interval. -/
public noncomputable section
open Set Filter IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem Regular.lower_noninteger {a r : ℝ} {n : ℕ} (ha : 0 < a) (ha1 : a < 1)
    (lower : a+n < r) {f : M → F} (hf : Regular (E := E) (F := F) r f) :
    Regular (E := E) (F := F) (a+n) f := by
  apply regular_of_chart_jets ha ha1
  intro x
  by_cases large : (n : ℝ)+1 ≤ r
  · have ordinary : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) (n+1 : ℕ) f :=
      hf.differentiable.of_le (by exact_mod_cast (Nat.le_floor (by simpa using large)))
    have coordinate := (contMDiffAt_iff.mp (ordinary.contMDiffAt (x := x))).2
    apply JetAt.of_contDiff_succ ha1.le
    simpa only [chartMap,ModelWithCorners.range_eq_univ,contDiffWithinAt_univ,Nat.cast_add,Nat.cast_one] using coordinate
  · have upper : r < (n : ℝ)+1 := lt_of_not_ge large
    have floor : ⌊r⌋₊ = n := (Nat.floor_eq_iff hf.nonnegative).mpr ⟨by linarith,upper⟩
    have unequal : r ≠ (⌊r⌋₊ : ℝ) := by rw [floor]; linarith
    have coordinate := (contMDiffAt_iff.mp (hf.differentiable.contMDiffAt (x := x))).2
    obtain ⟨U,openU,inU,_inside,C,hC,bound⟩ := hf.holder unequal x
    let p := extChartAt (𝓘(ℝ,E)) x x
    refine ⟨?_,U∩Metric.ball p (1/2),openU.inter Metric.isOpen_ball,
      ⟨inU,Metric.mem_ball_self (by norm_num)⟩,C,hC,?_⟩
    · simpa only [chartMap,ModelWithCorners.range_eq_univ,contDiffWithinAt_univ,floor] using coordinate
    · intro y hy z hz
      have small : ‖y-z‖ ≤ 1 := by
        have triangle := dist_triangle y p z
        have hyp : dist y p < 1/2 := hy.2
        have hzp : dist p z < 1/2 := by simpa only [Metric.mem_ball,dist_comm] using hz.2
        rw [←dist_eq_norm]
        linarith
      have power := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (y-z)) small ha.le
        (show a ≤ r-(n : ℝ) by linarith)
      rw [floor] at bound
      exact (bound y hy.1 z hz.1).trans (mul_le_mul_of_nonneg_left power hC)

end LeanShared.FractionalManifoldRegularity
