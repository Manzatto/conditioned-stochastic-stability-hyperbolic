module

public import LeanShared.Analysis.CompactCorePerturbation
public import LeanShared.Analysis.AnnealedOperatorBounds

/-! # Mixed-norm convergence of actual noise averages

A common small-noise neighborhood puts every sampled generator inside the
compact-core perturbation neighborhood. Pointwise Bochner averaging gives
the literal strong-to-weak norm convergence. No operator-valued Bochner
measurability or desired perturbation bound is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace LeanShared.CompactAnnealedPerturbation

open CompactCorePerturbation AnnealedOperatorBounds

/-- The literal uniform small-noise distance bound supplies every common
generator neighborhood used by the compact-input perturbation proof. -/
theorem common_neighborhood_of_uniform_distance
    {G Ω : Type*} [PseudoMetricSpace G] (T : G) (a : ℝ≥0 → Ω → G) (c : ℝ)
    (hclose : ∀ ε ω, dist (a ε ω) T ≤ c * (ε : ℝ)) :
    ∀ V ∈ 𝓝 T, ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ∀ ω, a ε ω ∈ V := by
  intro V hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hcoe : Tendsto (fun ε : ℝ≥0 => (ε : ℝ)) (𝓝 0) (𝓝 (0 : ℝ)) :=
    NNReal.continuous_coe.continuousAt
  have hlim : Tendsto (fun ε : ℝ≥0 => c * (ε : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := c)).mul hcoe
  filter_upwards [hlim (gt_mem_nhds hδ)] with ε hε
  intro ω
  exact hball ((hclose ε ω).trans_lt hε)

variable {E H W G I Ω Core : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [TopologicalSpace G] [MeasurableSpace Ω]

theorem mixed_norm_average_tendsto_zero
    (i : E →L[ℂ] H) (hi : IsCompactOperator i) (j : E →L[ℂ] W)
    (A : G → H →L[ℂ] W) (P : G → E →L[ℂ] E) (T : G)
    (hcompat : ∀ p, (A p).comp i = j.comp (P p))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᶠ p in 𝓝 T, ‖A p‖ ≤ M)
    (q : Core → H) (hq : DenseRange q)
    (hcore : ∀ f, Tendsto (fun p => A p (q f)) (𝓝 T) (𝓝 (A T (q f))))
    (a : I → Ω → G) (l : Filter I)
    (hnoise : ∀ V ∈ 𝓝 T, ∀ᶠ ε in l, ∀ ω, a ε ω ∈ V)
    (μ : I → Measure Ω) [∀ ε, IsProbabilityMeasure (μ ε)]
    (hmeas : ∀ ε x, AEStronglyMeasurable (fun ω => P (a ε ω) x) (μ ε))
    (L : I → ℝ) (hL : ∀ ε ω, ‖P (a ε ω)‖ ≤ L ε) :
    Tendsto (fun ε => ‖j.comp
      (pointwiseAnnealed (μ ε) (fun ω => P (a ε ω)) (hmeas ε) (L ε) (hL ε) - P T)‖)
      l (𝓝 0) := by
  have hlimit := mixed_norm_tendsto_of_compatible_core i hi j A (A T) P (P T)
    hcompat (hcompat T) (𝓝 T) M hM hbound q hq hcore
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hV : {p : G | ‖j.comp (P p - P T)‖ < η / 2} ∈ 𝓝 T :=
    hlimit (gt_mem_nhds (by simpa using (show 0 < η / 2 by positivity)))
  filter_upwards [hnoise _ hV] with ε hε
  have hb : ‖j.comp
      (pointwiseAnnealed (μ ε) (fun ω => P (a ε ω)) (hmeas ε) (L ε) (hL ε) - P T)‖ ≤ η / 2 := by
    apply pointwiseAnnealed_weak_perturbation (μ ε) (fun ω => P (a ε ω))
      (hmeas ε) (L ε) (hL ε) j (P T) (η / 2) (by positivity)
    intro ω x
    have he : j ((P (a ε ω) - P T) x) = (j.comp (P (a ε ω) - P T)) x := rfl
    rw [he]
    exact ((j.comp (P (a ε ω) - P T)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hε ω).le (norm_nonneg _))
  have hb' := hb.trans_lt (show η / 2 < η by linarith)
  simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using hb'

end LeanShared.CompactAnnealedPerturbation
