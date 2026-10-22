module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Analysis.Complex.Basic

/-! Local two-point Hölder bounds are closed under literal complex
multiplication. Bounds on function values are derived on a small ball;
neither a supplied multiplier operator nor a product regularity field is
used. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.LocalHolderProduct
variable {E : Type*} [NormedAddCommGroup E]

theorem exists_bound {f g : E → ℂ} {x : E} {a C D : ℝ} (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hD : 0 ≤ D) {U V : Set E} (hU : U ∈ 𝓝 x) (hV : V ∈ 𝓝 x)
    (hf : ∀ y ∈ U, ∀ z ∈ U, ‖f y-f z‖ ≤ C * ‖y-z‖ ^ a)
    (hg : ∀ y ∈ V, ∀ z ∈ V, ‖g y-g z‖ ≤ D * ‖y-z‖ ^ a) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∩ V ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ y ∈ W, ∀ z ∈ W, ‖f y*g y-f z*g z‖ ≤ A * ‖y-z‖ ^ a := by
  obtain ⟨O, subO, openO, inO⟩ := mem_nhds_iff.mp (inter_mem hU hV)
  let W := O ∩ Metric.ball x 1
  have inW : x ∈ W := ⟨inO, Metric.mem_ball_self zero_lt_one⟩
  have small (y : E) (hy : y ∈ W) : ‖y-x‖ ^ a ≤ 1 :=
    Real.rpow_le_one (norm_nonneg _) (by simpa only [Metric.mem_ball, dist_eq_norm] using (show dist y x < 1 from hy.2).le) ha
  have fvalue (y : E) (hy : y ∈ W) : ‖f y‖ ≤ ‖f x‖ + C := by
    have estimate := (hf y (subO hy.1).1 x (mem_of_mem_nhds hU)).trans
      (mul_le_mul_of_nonneg_left (small y hy) hC)
    have triangle : ‖f y‖ ≤ ‖f y-f x‖ + ‖f x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f y-f x) (f x)
    linarith
  have gvalue (y : E) (hy : y ∈ W) : ‖g y‖ ≤ ‖g x‖ + D := by
    have estimate := (hg y (subO hy.1).2 x (mem_of_mem_nhds hV)).trans
      (mul_le_mul_of_nonneg_left (small y hy) hD)
    have triangle : ‖g y‖ ≤ ‖g y-g x‖ + ‖g x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (g y-g x) (g x)
    linarith
  refine ⟨W, openO.inter Metric.isOpen_ball, inW, (fun y hy => subO hy.1),
    (‖f x‖+C)*D+C*(‖g x‖+D), by positivity, ?_⟩
  intro y hy z hz
  have algebra : f y*g y-f z*g z = f y*(g y-g z)+(f y-f z)*g z := by ring
  rw [algebra]
  calc
    _ ≤ ‖f y*(g y-g z)‖ + ‖(f y-f z)*g z‖ := norm_add_le _ _
    _ = ‖f y‖*‖g y-g z‖ + ‖f y-f z‖*‖g z‖ := by rw [norm_mul, norm_mul]
    _ ≤ (‖f x‖+C)*(D*‖y-z‖^a)+(C*‖y-z‖^a)*(‖g x‖+D) :=
      add_le_add
        (mul_le_mul (fvalue y hy) (hg y (subO hy.1).2 z (subO hz.1).2)
          (norm_nonneg _) (by positivity))
        (mul_le_mul (hf y (subO hy.1).1 z (subO hz.1).1) (gvalue z hz)
          (norm_nonneg _) (by positivity))
    _ = _ := by ring
end LeanShared.LocalHolderProduct
