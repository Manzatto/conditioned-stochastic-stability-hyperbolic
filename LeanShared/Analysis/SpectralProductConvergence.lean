module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Intermediate-space convergence and spectral products

Uniformly bounded dual functionals converging on a dense core converge on
every test. They also converge when evaluated on norm-convergent moving
tests, hence on bounded multiplication operators applied to convergent
eigenvectors. Compact strong-to-intermediate maps upgrade convergence in an
injectively embedded weaker space to convergence in the intermediate norm.

These are conditional functional-analytic adapters. They construct neither
anisotropic spaces nor perturbative spectral projectors.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace LeanShared.SpectralProductConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} {L : Filter ι}

/-- A uniform dual bound extends convergence from a dense core to every test.
Only an eventual bound is required, as is natural for a small-noise limit. -/
theorem tendsto_apply_of_dense (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᶠ n in L, ‖μ n‖ ≤ C)
    (D : Set E) (hD : Dense D)
    (hcore : ∀ x ∈ D, Tendsto (fun n => μ n x) L (𝓝 (μ₀ x))) (x : E) :
    Tendsto (fun n => μ n x) L (𝓝 (μ₀ x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B : ℝ := C + ‖μ₀‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x (ε := ε / (3 * B))
    (div_pos hε (mul_pos (by positivity) hB))
  have hd : ‖x - y‖ * (3 * B) < ε :=
    (lt_div_iff₀ (mul_pos (by positivity) hB)).mp (by simpa only [dist_eq_norm] using hxy)
  have hsmall : B * ‖x - y‖ < ε / 3 := by nlinarith
  have hevent := (Metric.tendsto_nhds.mp (hcore y hyD)) (ε / 3) (by positivity)
  filter_upwards [hbound, hevent] with n hn hny
  rw [dist_eq_norm] at hny ⊢
  have he : μ n x - μ₀ x = μ n (x - y) + (μ n y - μ₀ y) - μ₀ (x - y) := by
    rw [map_sub, map_sub]
    ring
  have htotal : ‖μ n x - μ₀ x‖ ≤ B * ‖x - y‖ + ‖μ n y - μ₀ y‖ := by
    rw [he]
    calc
      ‖μ n (x - y) + (μ n y - μ₀ y) - μ₀ (x - y)‖ ≤
          ‖μ n (x - y)‖ + ‖μ n y - μ₀ y‖ + ‖μ₀ (x - y)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ C * ‖x - y‖ + ‖μ n y - μ₀ y‖ + ‖μ₀‖ * ‖x - y‖ :=
        add_le_add (add_le_add ((μ n).le_opNorm (x - y) |>.trans
          (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) le_rfl)
          (μ₀.le_opNorm (x - y))
      _ ≤ B * ‖x - y‖ + ‖μ n y - μ₀ y‖ := by
        dsimp [B]
        nlinarith [norm_nonneg (x - y)]
  nlinarith

/-- Uniformly bounded functionals may be paired with norm-convergent moving tests. -/
theorem tendsto_apply_moving (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ᶠ n in L, ‖μ n‖ ≤ C)
    (hμ : ∀ x, Tendsto (fun n => μ n x) L (𝓝 (μ₀ x)))
    (v : ι → E) (v₀ : E) (hv : Tendsto v L (𝓝 v₀)) :
    Tendsto (fun n => μ n (v n)) L (𝓝 (μ₀ v₀)) := by
  have hz : Tendsto (fun n => μ n (v n - v₀)) L (𝓝 (0 : ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [hbound] with n hn
      exact ((μ n).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
    · have hvz : Tendsto (fun n => ‖v n - v₀‖) L (𝓝 (0 : ℝ)) := by
        simpa only [sub_self, norm_zero] using
          (hv.sub (tendsto_const_nhds (x := v₀))).norm
      simpa only [mul_zero] using hvz.const_mul C
  have hs := hz.add (hμ v₀)
  simpa only [map_sub, sub_add_cancel, zero_add] using hs

/-- The spectral product converges for each bounded multiplication operator,
even when dual convergence was initially known only on a dense core. -/
theorem tendsto_spectral_product (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᶠ n in L, ‖μ n‖ ≤ C)
    (D : Set E) (hD : Dense D)
    (hcore : ∀ x ∈ D, Tendsto (fun n => μ n x) L (𝓝 (μ₀ x)))
    (g : ι → E) (g₀ : E) (hg : Tendsto g L (𝓝 g₀)) (M : E →L[ℝ] E) :
    Tendsto (fun n => μ n (M (g n))) L (𝓝 (μ₀ (M g₀))) := by
  exact tendsto_apply_moving μ μ₀ C hC hbound
    (tendsto_apply_of_dense μ μ₀ C hC hbound D hD hcore)
    (fun n => M (g n)) (M g₀) (M.continuous.continuousAt.tendsto.comp hg)

section CompactUpgrade

variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compactness in the intermediate space and uniqueness of the weaker
limit imply intermediate convergence, without selecting inconsistent subsequences. -/
theorem tendsto_intermediate_of_compact (i : E →L[ℝ] H) (hi : IsCompactOperator i)
    (j : H →L[ℝ] W) (hj : Function.Injective j)
    (g : ι → E) (R : ℝ) (hbound : ∀ᶠ n in L, ‖g n‖ ≤ R)
    (g₀ : H) (hweak : Tendsto (fun n => j (i (g n))) L (𝓝 (j g₀))) :
    Tendsto (fun n => i (g n)) L (𝓝 g₀) := by
  have hic : IsCompactOperator i.toLinearMap := hi
  have hK := hic.isCompact_closure_image_closedBall R
  apply hK.tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [hbound] with n hn
    apply subset_closure
    refine ⟨g n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  · intro y _ hy
    apply hj
    have hyw := hy.continuousAt_comp j.continuous.continuousAt
    exact eq_of_nhds_neBot (hyw.clusterPt.mono hweak)

end CompactUpgrade

end LeanShared.SpectralProductConvergence
