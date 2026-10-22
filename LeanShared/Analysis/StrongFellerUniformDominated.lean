module

public import LeanShared.Analysis.StrongFellerUniformRows
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Uniform dominated convergence for compact setwise-continuous families
of subprobability measures. No common density or uniform density bound is
assumed. -/
public section
open Filter Topology Set MeasureTheory
namespace LeanShared.StrongFellerUniformRows
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace Y]

theorem uniform_dominated (κ : X → Measure Y) [∀ x, IsFiniteMeasure (κ x)]
    (continuous_rows : ∀ B, MeasurableSet B → Continuous (fun x => (κ x).real B))
    (mass : ∀ x, (κ x).real univ ≤ 1)
    (f : ℕ → Y → ℂ) (measurable : ∀ n, Measurable (f n))
    (B : ℝ) (hB : 0 ≤ B) (bounded : ∀ n y, ‖f n y‖ ≤ B)
    (pointwise : ∀ x, ∀ᵐ y ∂κ x, Tendsto (fun n => f n y) atTop (𝓝 0)) :
    TendstoUniformly (fun n x => ∫ y, f n y ∂κ x) (fun _ => 0) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let a := ε/2
  have ha : 0 < a := half_pos hε
  let U : ℕ → Set Y := fun n => ⋃ m ≥ n, {y | a ≤ ‖f m y‖}
  have measU (n : ℕ) : MeasurableSet (U n) :=
    MeasurableSet.iUnion (fun m => MeasurableSet.iUnion (fun _ =>
      measurableSet_le measurable_const (measurable m).norm))
  have decreasing : Antitone U := by
    intro n m hnm y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    obtain ⟨hmj,hyj⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hnm.trans hmj,hyj⟩⟩
  have null (x : X) : κ x (⋂ n, U n)=0 := by
    apply compl_mem_ae_iff.mp
    filter_upwards [pointwise x] with y hy
    intro member
    have hyNorm : Tendsto (fun n => ‖f n y‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hy.norm
    have small := hyNorm.eventually (gt_mem_nhds ha)
    obtain ⟨N,hN⟩ := eventually_atTop.mp small
    obtain ⟨m,hm⟩ := mem_iUnion.mp (mem_iInter.mp member N)
    obtain ⟨hNm,large⟩ := mem_iUnion.mp hm
    exact (not_lt_of_ge large) (by simpa only [norm_zero] using hN m hNm)
  have uniform := uniform_vanishing κ continuous_rows U measU decreasing null
  have small := (Metric.tendstoUniformly_iff.mp uniform) (a/(B+1))
    (div_pos ha (by linarith))
  filter_upwards [small] with n hn
  intro x
  have intf : Integrable (f n) (κ x) :=
    Integrable.of_bound (measurable n).aestronglyMeasurable B (ae_of_all _ (bounded n))
  have major : ∀ y, ‖f n y‖ ≤ a + (U n).indicator (fun _ => B) y := by
    intro y
    by_cases hy : y ∈ U n
    · rw [indicator_of_mem hy]
      exact (bounded n y).trans (le_add_of_nonneg_left ha.le)
    · rw [indicator_of_notMem hy,add_zero]
      apply le_of_lt
      apply lt_of_not_ge
      intro large
      exact hy (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨le_rfl,large⟩⟩)
  have integralBound : ‖∫ y, f n y ∂κ x‖ ≤ a+B*(κ x).real (U n) := by
    calc
      _ ≤ ∫ y, ‖f n y‖ ∂κ x := norm_integral_le_integral_norm _
      _ ≤ ∫ y, a+(U n).indicator (fun _ => B) y ∂κ x :=
        integral_mono_ae intf.norm ((integrable_const a).add
          ((integrable_const B).indicator (measU n))) (ae_of_all _ major)
      _ = a*(κ x).real univ+B*(κ x).real (U n) := by
        rw [integral_add (integrable_const a) ((integrable_const B).indicator (measU n)),
          integral_const, integral_indicator_const B (measU n)]
        simp only [smul_eq_mul,mul_comm]
      _ ≤ _ := add_le_add (mul_le_of_le_one_right ha.le (mass x)) le_rfl
  have hn' : (κ x).real (U n) < a/(B+1) := by
    simpa only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg measureReal_nonneg] using hn x
  have mult : B*(κ x).real (U n) < a := by
    have bound : (B+1)*(κ x).real (U n) < a :=
      by simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0 < B+1)).mp hn'
    nlinarith [measureReal_nonneg (μ := κ x) (s := U n)]
  rw [dist_zero_left]
  exact integralBound.trans_lt (by change a+B*(κ x).real (U n)<ε; dsimp [a] at *; linarith)

end LeanShared.StrongFellerUniformRows
