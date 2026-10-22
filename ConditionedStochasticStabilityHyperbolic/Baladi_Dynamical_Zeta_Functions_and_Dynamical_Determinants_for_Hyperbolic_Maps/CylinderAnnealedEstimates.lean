module

public import LeanShared.Analysis.CylinderPrincipalCoefficient
public import LeanShared.Analysis.FiniteBlockAnnealedEstimates
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.LeftRight

/-!
# Pressure coefficients to actual annealed two-norm estimates

The scalar pressure input is the finite-cylinder coefficient root asymptotic
(Baladi--Tsujii 2008, Section 3, especially Lemma 3.5). It does not assert a
strict block estimate. Moving cylinder suprema supply semicontinuity, pressure
selects a sufficiently long block, and robust block iteration and actual
pointwise averaging supply the final all-power inequality.

The microlocal finite-block estimate remains an explicit cited local input. Its weak remainder is not inferred from compactness of the remainder alone. The varying-word uniform bound and the annealed inequality are proved here.

Source: https://arxiv.org/pdf/math/0606434 . The source's equation (5.7)
uses separate suprema; equation (5.8) uses a positive majorant and bounded
distortion to compare with a joint supremum; equation (5.9) bounds a bounded
part with a compact remainder. Its compact remainder does not itself imply
the `hlocal` weak-norm bound below.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ConditionedStochasticStabilityHyperbolic.CylinderAnnealedEstimates

open LeanShared.CylinderPrincipalCoefficient
open LeanShared.FiniteBlockAnnealedEstimates

/-- For the paper's nonnegative weights, adding a positive constant gives
the positive envelope required for cylinder distortion. Classical pressure
continuity selects it below the prescribed slack. It need not be a supported
transfer weight: it is only a dominating pressure coefficient. -/
theorem exists_positive_envelope {X : Type*} [TopologicalSpace X]
    (g : X → ℝ) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (pressure : (X → ℝ) → ℝ) (Q ρ : ℝ) (hQρ : Q < ρ)
    (hpressure : Tendsto (fun δ : ℝ => pressure (fun x => g x + δ))
      (𝓝 0) (𝓝 Q)) :
    ∃ δ : ℝ, 0 < δ ∧ Continuous (fun x => g x + δ) ∧
      (∀ x, |g x| < g x + δ) ∧ (∀ x, 0 < g x + δ) ∧
      pressure (fun x => g x + δ) < ρ := by
  obtain ⟨δ, hδ, hP⟩ := ((frequently_gt_nhds (0 : ℝ)).and_eventually
    (hpressure.eventually (gt_mem_nhds hQρ))).exists
  refine ⟨δ, hδ, hg.add continuous_const, ?_, ?_, hP⟩
  · intro x
    rw [abs_of_nonneg (hg0 x)]
    exact lt_add_of_pos_right _ hδ
  · intro x
    exact add_pos_of_nonneg_of_pos (hg0 x) hδ

/-- A scalar root asymptotic selects a strict block despite a fixed
microlocal prefactor. Zero coefficients and zero prefactors are allowed. -/
theorem exists_strict_block (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (Q C ρ : ℝ) (hC : 0 ≤ C) (hQρ : Q < ρ)
    (hpressure : Tendsto (fun n => q n ^ ((n : ℝ)⁻¹)) atTop (𝓝 Q)) :
    ∃ N : ℕ, 0 < N ∧ C * q N < ρ ^ N := by
  have hCp : 0 < C + 1 := add_pos_of_nonneg_of_pos hC zero_lt_one
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun n : ℕ => (C + 1) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.rpow hinv (Or.inl hCp.ne'))
  have hprod : Tendsto (fun n : ℕ =>
      (C + 1) ^ ((n : ℝ)⁻¹) * q n ^ ((n : ℝ)⁻¹)) atTop (𝓝 Q) := by
    simpa using hroot.mul hpressure
  obtain ⟨N, hrootN, hN⟩ :=
    ((hprod.eventually (gt_mem_nhds hQρ)).and (eventually_gt_atTop 0)).exists
  have hpow := pow_lt_pow_left₀ hrootN
    (mul_nonneg (Real.rpow_nonneg hCp.le _) (Real.rpow_nonneg (hq N) _)) hN.ne'
  rw [mul_pow, Real.rpow_inv_natCast_pow hCp.le hN.ne',
    Real.rpow_inv_natCast_pow (hq N) hN.ne'] at hpow
  exact ⟨N, hN, (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (hq N)).trans_lt hpow⟩

variable {G X E F : Type*} [TopologicalSpace G] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Actual moving-cylinder coefficients and their pressure root limit
produce the final annealed Lasota--Yorke estimate. The fixed selected inner
cover is proved to persist, while closed outer cylinders control the suprema.

`hlocal` is only the finite-word microlocal estimate on a cone-valid tuple,
with its identified coefficient and local remainder. Neither coefficient
semicontinuity, a deterministic strict block, arbitrary-word estimates nor
the final annealed conclusion are inputs. -/
theorem exists_cylinder_annealed_estimate
    (T : G) (A : G → E →L[ℂ] E) (ι : E →L[ℂ] F)
    (K : Set X) (hK : IsCompact K) {I : ℕ → Type*}
    (cover : (N : ℕ) → Finset (I N))
    (R : (N : ℕ) → I N → Set ((Fin N → G) × X))
    (density : (N : ℕ) → I N → (Fin N → G) × X → ℝ)
    (hR : ∀ N, ∀ i ∈ cover N, IsClosed (R N i))
    (hdensity : ∀ N, ∀ i ∈ cover N, Continuous (density N i))
    (surviving innerCover : (N : ℕ) → Set ((Fin N → G) × X))
    (hsurviving : ∀ N, IsClosed (surviving N))
    (hinner : ∀ N, IsOpen (innerCover N))
    (hcovers : ∀ N x, x ∈ fiber K (surviving N) (fun _ => T) →
      ((fun _ => T), x) ∈ innerCover N)
    (Q Cmic ρ C₀ M L : ℝ) (hCmic : 0 ≤ Cmic)
    (hQρ : Q < ρ) (hρ : 0 < ρ) (hρC₀ : ρ < C₀)
    (hM : 0 ≤ M) (hMC₀ : M ≤ C₀) (hL : 0 ≤ L)
    (hpressure : Tendsto (fun N =>
      (∑ i ∈ cover N, coefficient K (R N i) (density N i) (fun _ => T)) ^
        ((N : ℝ)⁻¹)) atTop (𝓝 Q))
    (U : Set G) (hU : IsOpen U) (hTU : T ∈ U)
    (hstrong : ∀ a ∈ U, ‖A a‖ ≤ L)
    (hweak : ∀ a ∈ U, ∀ x, ‖ι (A a x)‖ ≤ M * ‖ι x‖)
    (coneValid : (N : ℕ) → Set (Fin N → G))
    (hcone : ∀ N, coneValid N ∈ 𝓝 (fun _ => T))
    (remainder : (N : ℕ) → (Fin N → G) → ℝ)
    (hrem : ∀ N, ContinuousAt (remainder N) (fun _ => T))
    (hlocal : ∀ N word, word ∈ coneValid N →
      (∀ x ∈ fiber K (surviving N) word, (word, x) ∈ innerCover N) → ∀ x,
      ‖listWord A (List.ofFn word) x‖ ≤
        (Cmic * ∑ i ∈ cover N, coefficient K (R N i) (density N i) word) * ‖x‖ +
          remainder N word * ‖ι x‖) :
    ∃ W : Set G, IsOpen W ∧ T ∈ W ∧ W ⊆ U ∧
      ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ζ : Ω → G), (∀ ω, ζ ω ∈ W) →
        (∀ x, AEStronglyMeasurable (fun ω => A (ζ ω) x) μ) →
        ∀ P : E →L[ℂ] E, (∀ x, P x = ∫ ω, A (ζ ω) x ∂μ) →
        ∀ n x, ‖(P ^ n) x‖ ≤ C * ρ ^ n * ‖x‖ + D * C₀ ^ n * ‖ι x‖ := by
  classical
  let q : ℕ → ℝ := fun N =>
    ∑ i ∈ cover N, coefficient K (R N i) (density N i) (fun _ => T)
  have hq : ∀ N, 0 ≤ q N := fun N => Finset.sum_nonneg fun i hi =>
    coefficient_nonneg hK (hR N i hi) (hdensity N i hi) _
  obtain ⟨N, hN, hstrict⟩ := exists_strict_block q hq Q Cmic ρ hCmic hQρ hpressure
  obtain ⟨V, hV, hTV, hcoverV⟩ := exists_robust_subcover hK (hsurviving N)
    (innerCover N) (hinner N) (fun _ => T) (hcovers N)
  have hsum := upperSemicontinuous_coverSum (cover N) (R N) (density N)
    hK (hR N) (hdensity N)
  have ha : UpperSemicontinuousAt
      (fun word => Cmic * ∑ i ∈ cover N, coefficient K (R N i) (density N i) word)
      (fun _ => T) :=
    ((continuous_const.mul continuous_id).comp_upperSemicontinuous hsum
      (fun _ _ h => mul_le_mul_of_nonneg_left h hCmic)) _
  exact exists_robust_annealed_twoNorm_bound T A ι N hN ρ C₀ M L
    hρ hρC₀ hM hMC₀ hL U hU hTU hstrong hweak _ (remainder N)
    ha (hrem N).upperSemicontinuousAt hstrict (coneValid N ∩ V)
    (inter_mem (hcone N) (hV.mem_nhds hTV))
    (fun word hw => hlocal N word hw.1 (hcoverV word hw.2))

end ConditionedStochasticStabilityHyperbolic.CylinderAnnealedEstimates
