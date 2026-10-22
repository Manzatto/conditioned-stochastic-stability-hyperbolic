module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # A genuine mixed-norm modulus from compact inclusion and core convergence

Uniformly bounded operators converging on a dense core converge uniformly
after a compact inclusion. This uses finite core nets, with no input-frequency
reconstruction or operator-norm continuity of the random family.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace LeanShared.CompactCorePerturbation

variable {E H W I Core : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem norm_comp_tendsto_zero_of_dense_core
    (i : E →L[ℂ] H) (hi : IsCompactOperator i)
    (B : I → H →L[ℂ] W) (l : Filter I)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᶠ p in l, ‖B p‖ ≤ M)
    (q : Core → H) (hq : DenseRange q)
    (hcore : ∀ f, Tendsto (fun p => B p (q f)) l (𝓝 0)) :
    Tendsto (fun p => ‖(B p).comp i‖) l (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (4 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδmul : (M + 1) * δ = ε / 4 := by
    dsimp [δ]
    field_simp
  obtain ⟨K, hK, hiK⟩ := hi.image_closedBall_subset_compact (r := 1)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun f : Core => ball (q f) δ)
    (fun _ => isOpen_ball) (by
      intro x _hx
      obtain ⟨f, hf⟩ := Metric.denseRange_iff.mp hq x δ hδ
      exact mem_iUnion.mpr ⟨f, hf⟩)
  have hsmall : ∀ᶠ p in l, ∀ f ∈ t, ‖B p (q f)‖ < ε / 4 := by
    apply t.eventually_all.mpr
    intro f _hf
    exact (hcore f).norm (gt_mem_nhds (by simpa using (show 0 < ε / 4 by positivity)))
  filter_upwards [hbound, hsmall] with p hp hsmallp
  have hn : ‖(B p).comp i‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have hxK : i x ∈ K := hiK ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩
    obtain ⟨f, hf, hnear⟩ := mem_iUnion₂.mp (ht hxK)
    have hdist : ‖i x - q f‖ < δ := by
      simpa only [mem_ball, dist_eq_norm] using hnear
    have hsplit : B p (i x) = B p (i x - q f) + B p (q f) := by
      rw [map_sub, sub_add_cancel]
    change ‖B p (i x)‖ ≤ ε / 2
    rw [hsplit]
    calc
      ‖B p (i x - q f) + B p (q f)‖ ≤ ‖B p (i x - q f)‖ + ‖B p (q f)‖ := norm_add_le _ _
      _ ≤ M * ‖i x - q f‖ + ‖B p (q f)‖ := by
        exact add_le_add (((B p).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hp (norm_nonneg _))) le_rfl
      _ ≤ M * δ + ‖B p (q f)‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_left hdist.le hM) le_rfl
      _ ≤ (M + 1) * δ + ‖B p (q f)‖ := by
        have hcoef : M * δ ≤ (M + 1) * δ :=
          mul_le_mul_of_nonneg_right (by linarith) hδ.le
        exact add_le_add hcoef le_rfl
      _ ≤ ε / 2 := by rw [hδmul]; linarith [hsmallp f hf]
  have hlt : ‖(B p).comp i‖ < ε := hn.trans_lt (by linarith)
  simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using hlt

theorem norm_difference_comp_tendsto_zero
    (i : E →L[ℂ] H) (hi : IsCompactOperator i)
    (A : I → H →L[ℂ] W) (A₀ : H →L[ℂ] W) (l : Filter I)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᶠ p in l, ‖A p‖ ≤ M)
    (q : Core → H) (hq : DenseRange q)
    (hcore : ∀ f, Tendsto (fun p => A p (q f)) l (𝓝 (A₀ (q f)))) :
    Tendsto (fun p => ‖(A p - A₀).comp i‖) l (𝓝 0) := by
  apply norm_comp_tendsto_zero_of_dense_core i hi (fun p => A p - A₀) l
    (M + ‖A₀‖) (add_nonneg hM (norm_nonneg _))
  · filter_upwards [hbound] with p hp
    exact (norm_sub_le _ _).trans (add_le_add hp le_rfl)
  · exact hq
  · intro f
    simpa only [sub_apply, sub_self] using (hcore f).sub
      (tendsto_const_nhds (x := A₀ (q f)))

/-- Two compatible realizations identify the compact-input norm with the
literal strong-to-weak output norm required by spectral perturbation. -/
theorem mixed_norm_tendsto_of_compatible_core
    (i : E →L[ℂ] H) (hi : IsCompactOperator i) (j : E →L[ℂ] W)
    (A : I → H →L[ℂ] W) (A₀ : H →L[ℂ] W)
    (P : I → E →L[ℂ] E) (P₀ : E →L[ℂ] E)
    (hcompat : ∀ p, (A p).comp i = j.comp (P p))
    (hcompat₀ : A₀.comp i = j.comp P₀) (l : Filter I)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᶠ p in l, ‖A p‖ ≤ M)
    (q : Core → H) (hq : DenseRange q)
    (hcore : ∀ f, Tendsto (fun p => A p (q f)) l (𝓝 (A₀ (q f)))) :
    Tendsto (fun p => ‖j.comp (P p - P₀)‖) l (𝓝 0) := by
  have heq (p : I) : (A p - A₀).comp i = j.comp (P p - P₀) := by
    rw [ContinuousLinearMap.sub_comp, hcompat, hcompat₀, ContinuousLinearMap.comp_sub]
  simpa only [heq] using norm_difference_comp_tendsto_zero i hi A A₀ l M hM hbound q hq hcore

end LeanShared.CompactCorePerturbation
