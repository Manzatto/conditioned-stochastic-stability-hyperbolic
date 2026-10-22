module

public import LeanShared.Analysis.ContinuousTangentJacobian
public import LeanShared.Analysis.RobustTwoNormBlock
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Uniform microlocal phase separation from actual derivative words

Continuity of the actual derivative word on a compact coordinate domain
produces one common generator neighborhood. The transpose/adjoint phase
gradient loses at most derivative error times input frequency magnitude.
Hence a strict deterministic frequency separation remains uniformly
positive for every nearby finite word. This produces the common denominator
control needed by the cited fractional nonstationary-phase estimate.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace LeanShared.RobustFrequencySeparation

open CylinderPrincipalCoefficient FiniteDerivativeWord ContinuousTangentJacobian

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem adjoint_error_apply_le (A D : E →L[ℝ] E) (ε : ℝ) (hε : ‖A - D‖ ≤ ε) (η : E) :
    ‖ContinuousLinearMap.adjoint A η - ContinuousLinearMap.adjoint D η‖ ≤ ε * ‖η‖ := by
  calc
    _ = ‖ContinuousLinearMap.adjoint (A - D) η‖ := by simp only [map_sub, sub_apply]
    _ ≤ ‖ContinuousLinearMap.adjoint (A - D)‖ * ‖η‖ :=
      (ContinuousLinearMap.adjoint (A - D)).le_opNorm η
    _ = ‖A - D‖ * ‖η‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_right hε (norm_nonneg η)

theorem phase_separation_of_derivative_bound (A D : E →L[ℝ] E)
    (ξ η : E) (ε B σ Λ : ℝ) (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ)
    (herror : ‖A - D‖ ≤ ε) (hfreq : ‖η‖ ≤ B * Λ)
    (hgap : σ * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint D η‖)
    (hsmall : ε * B ≤ σ / 2) :
    (σ / 2) * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint A η‖ := by
  have he : ‖ContinuousLinearMap.adjoint A η - ContinuousLinearMap.adjoint D η‖ ≤
      (ε * B) * Λ :=
    (adjoint_error_apply_le A D ε herror η).trans
      ((mul_le_mul_of_nonneg_left hfreq hε).trans_eq (mul_assoc ε B Λ).symm)
  have htriangle : ‖ξ - ContinuousLinearMap.adjoint D η‖ ≤
      ‖ξ - ContinuousLinearMap.adjoint A η‖ + (ε * B) * Λ := by
    calc
      _ = ‖(ξ - ContinuousLinearMap.adjoint A η) +
          (ContinuousLinearMap.adjoint A η - ContinuousLinearMap.adjoint D η)‖ := by
        congr 1
        abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl he)
  have hsmallΛ := mul_le_mul_of_nonneg_right hsmall hΛ
  linarith

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NormedSpace ℝ P] in
/-- A compact coordinate domain gives one uniform threshold for a continuous
finite-word field. The actual derivative field is instantiated below. -/
theorem exists_uniform_field_neighborhood {N : ℕ} {Q : Type*} [NormedAddCommGroup Q]
    (D : ((Fin N → P) × E) → Q) (hD : Continuous D)
    (p₀ : P) (K : Set E) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧
      ∀ word : Fin N → P, (∀ i, word i ∈ W) → ∀ x ∈ K,
        ‖D (word, x) - D ((fun _ : Fin N => p₀), x)‖ < ε := by
  have hbase : Continuous (fun z : (Fin N → P) × E => D ((fun _ => p₀), z.2)) :=
    hD.comp (continuous_const.prodMk continuous_snd)
  let O := {z : (Fin N → P) × E | ‖D z - D ((fun _ => p₀), z.2)‖ < ε}
  have hO : IsOpen O := isOpen_lt ((hD.sub hbase).norm) continuous_const
  have hsub : ({fun _ : Fin N => p₀} : Set (Fin N → P)) ×ˢ K ⊆ O := by
    rintro ⟨word, x⟩ ⟨hw, _⟩
    have heq : word = fun _ => p₀ := mem_singleton_iff.mp hw
    subst word
    simpa only [O, mem_ofPred_eq, sub_self, norm_zero] using hε
  obtain ⟨V, U, hV, _, hpV, hKU, hVU⟩ :=
    generalized_tube_lemma isCompact_singleton hK hO hsub
  obtain ⟨W, hW, hpW, hbox⟩ := LeanShared.RobustTwoNormBlock.exists_open_box_of_mem_nhds N p₀ V
    (hV.mem_nhds (singleton_subset_iff.mp hpV))
  refine ⟨W, hW, hpW, ?_⟩
  intro word hw x hx
  exact hVU (mk_mem_prod (hbox word hw) (hKU hx))

omit [CompleteSpace E] in
/-- One compact-domain threshold works for all actual finite-word
 derivatives, with no supplied word operator-norm continuity. -/
theorem exists_uniform_derivative_neighborhood (F : E × P → E) (hF : ContDiff ℝ 1 F)
    (p₀ : P) (K : Set E) (hK : IsCompact K) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧
      ∀ word : Fin N → P, (∀ i, word i ∈ W) → ∀ x ∈ K,
        ‖prefixDerivative (fun a x => F (x, a)) word x N -
          prefixDerivative (fun a x => F (x, a)) (fun _ : Fin N => p₀) x N‖ < ε :=
  exists_uniform_field_neighborhood
    (fun z : (Fin N → P) × E => prefixDerivative (fun a x => F (x, a)) z.1 z.2 N)
    (continuous_prefixDerivative F hF N N) p₀ K hK ε hε

/-- The actual compact-domain derivative producer and transpose estimate
give a common positive phase gap for all nearby words. The radial support
bound `2*Lambda` is the one used by the dyadic cutoff symbols. -/
theorem exists_uniform_phase_neighborhood (F : E × P → E) (hF : ContDiff ℝ 1 F)
    (p₀ : P) (K : Set E) (hK : IsCompact K) (N : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ W : Set P, IsOpen W ∧ p₀ ∈ W ∧
      ∀ word : Fin N → P, (∀ i, word i ∈ W) → ∀ x ∈ K,
        ∀ (ξ η : E) (Λ : ℝ), 0 ≤ Λ → ‖η‖ ≤ 2 * Λ →
        σ * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint
          (prefixDerivative (fun a x => F (x, a)) (fun _ : Fin N => p₀) x N) η‖ →
        (σ / 2) * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint
          (prefixDerivative (fun a x => F (x, a)) word x N) η‖ := by
  obtain ⟨W, hW, hpW, hD⟩ := exists_uniform_derivative_neighborhood F hF p₀ K hK N
    (σ / 4) (div_pos hσ (by norm_num))
  refine ⟨W, hW, hpW, ?_⟩
  intro word hw x hx ξ η Λ hΛ hfreq hgap
  exact phase_separation_of_derivative_bound _ _ ξ η (σ / 4) 2 σ Λ
    (div_nonneg hσ.le (by norm_num)) hΛ (hD word hw x hx).le hfreq hgap (by linarith)

end LeanShared.RobustFrequencySeparation
