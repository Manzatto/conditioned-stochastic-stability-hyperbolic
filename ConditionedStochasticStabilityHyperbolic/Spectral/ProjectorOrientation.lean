module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure
import Mathlib.Tactic.Linarith

/-! # Canonical orientation of positive rank-one spectral projections

No sign for the supplied left functional is assumed. Positivity of the
actual operator and its normalized power limit prove that its projection of
one is nonzero. Choosing that projection as right vector normalizes the left
functional to have mass one, and constructs the rank-one data consumed by the
actual-process QEM arguments.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ProjectorOrientation

variable {X : Type*} [TopologicalSpace X]

/-- A nonzero positive rank-one projection on bounded continuous functions
cannot annihilate the constant function one. -/
theorem mean_one_ne_zero_of_projection_positive
    (g : X →ᵇ ℝ) (μ : (X →ᵇ ℝ) →L[ℝ] ℝ) (hpair : μ g = 1)
    (hpositive : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ μ f * g x) : μ 1 ≠ 0 := by
  intro hz
  have hplus : ∀ x, 0 ≤ (‖g‖ • (1 : X →ᵇ ℝ) + g) x := by
    intro x
    have hn := g.norm_coe_le_norm x
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.coe_one, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Real.norm_eq_abs] at hn
    linarith [neg_abs_le (g x)]
  have hminus : ∀ x, 0 ≤ (‖g‖ • (1 : X →ᵇ ℝ) - g) x := by
    intro x
    have hn := g.norm_coe_le_norm x
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.coe_one, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Real.norm_eq_abs] at hn
    linarith [le_abs_self (g x)]
  have hmgp : μ (‖g‖ • (1 : X →ᵇ ℝ) + g) = 1 := by simp [map_add, map_smul, hz, hpair]
  have hmgm : μ (‖g‖ • (1 : X →ᵇ ℝ) - g) = -1 := by simp [map_sub, map_smul, hz, hpair]
  have hgzero : g = 0 := by
    ext x
    have hp := hpositive _ hplus x
    have hm := hpositive _ hminus x
    rw [hmgp, one_mul] at hp
    rw [hmgm, neg_one_mul] at hm
    exact le_antisymm (neg_nonneg.mp hm) hp
  rw [hgzero, map_zero] at hpair
  exact zero_ne_one hpair

variable (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (r : ℝ) (hr : 0 < r)
    (g : X →ᵇ ℝ) (μ : (X →ᵇ ℝ) →L[ℝ] ℝ)

include hr

/-- A positive actual transfer has a positive rank-one power limit, without
assuming a sign for the supplied eigenvector or eigenfunctional. -/
theorem projection_positive_of_power_gap
    (hP : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (θ C : ℝ) (hθ : 0 ≤ θ) (hθone : θ < 1)
    (hgap : ∀ n : ℕ, ‖(r⁻¹ • P) ^ n - μ.smulRight g‖ ≤ C * θ ^ n) :
    ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ μ f * g x := by
  have hlim := LeanShared.ConditionedOperators.tendsto_powers_of_geometric_gap
    (r⁻¹ • P) (μ.smulRight g) hθ hθone hgap
  intro f hf x
  have hp (n : ℕ) : ∀ x, 0 ≤ (((r⁻¹ • P) ^ n) f) x := by
    induction n with
    | zero => intro y; simpa using hf y
    | succ n ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp]
      change 0 ≤ r⁻¹ * (P (((r⁻¹ • P) ^ n) f)) y
      exact mul_nonneg (inv_nonneg.mpr hr.le) (hP _ ih y)
  let ev := (BoundedContinuousFunction.evalCLM ℝ x).comp
    (ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) f)
  have he := ev.continuous.continuousAt.tendsto.comp hlim
  have hh : ev (μ.smulRight g) = μ f * g x := rfl
  change Tendsto (fun n => (((r⁻¹ • P) ^ n) f) x) atTop (𝓝 (ev (μ.smulRight g))) at he
  rw [hh] at he
  exact ge_of_tendsto he (Eventually.of_forall fun n => hp n x)

/-- Canonically orient the projection of a positive operator. The new
right vector is the projection of one, and the left functional has mass one.
The eigenvalue and entire projection are unchanged. -/
theorem exists_canonicalRankOne_of_power_gap
    (hP : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (hpair : μ g = 1) (hright : P g = r • g)
    (θ C : ℝ) (hθ : 0 ≤ θ) (hθone : θ < 1) (hC : 0 ≤ C)
    (hgap : ∀ n : ℕ, ‖(r⁻¹ • P) ^ n - μ.smulRight g‖ ≤ C * θ ^ n) :
    μ 1 ≠ 0 ∧ ∃ d : RankOneSpectralData P (1 : X →ᵇ ℝ),
      d.rate = r ∧ d.mean = (μ 1)⁻¹ • μ ∧ d.eigenvector = μ 1 • g ∧
      d.mean 1 = 1 ∧ (∀ x, 0 ≤ d.eigenvector x) := by
  have hpositive := projection_positive_of_power_gap P r hr g μ hP θ C hθ hθone hgap
  have hα := mean_one_ne_zero_of_projection_positive g μ hpair hpositive
  let α := μ 1
  have hα' : α ≠ 0 := hα
  have hmeanone : (α⁻¹ • μ) (1 : X →ᵇ ℝ) = 1 := by
    change α⁻¹ * α = 1
    exact inv_mul_cancel₀ hα'
  have hmeang : (α⁻¹ • μ) (α • g) = 1 := by
    simp only [smul_apply, map_smul, smul_eq_mul, hpair, mul_one]
    exact mul_inv_cancel₀ hα'
  have hright' : P (α • g) = r • (α • g) := by
    rw [map_smul, hright, smul_comm α r]
  have hproj : (α⁻¹ • μ).smulRight (α • g) = μ.smulRight g := by
    ext f
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, smul_smul]
    rw [mul_assoc, mul_comm (μ f) α, ← mul_assoc, inv_mul_cancel₀ hα', one_mul]
  have hgap' (n : ℕ) : ‖(r⁻¹ • P) ^ n - (α⁻¹ • μ).smulRight (α • g)‖ ≤ C * θ ^ n := by
    rw [hproj]
    exact hgap n
  let d : RankOneSpectralData P (1 : X →ᵇ ℝ) :=
    ⟨r, hr, α⁻¹ • μ, α • g, hmeang, hmeanone ▸ zero_lt_one,
      hright', C, hC, θ, hθ, hθone, hgap'⟩
  refine ⟨hα, d, rfl, rfl, rfl, hmeanone, ?_⟩
  intro x
  exact hpositive 1 (fun _ => zero_le_one) x

/-- Complementary complex spectral radius yields the canonically oriented
actual real gap. No sign or nonzero mass assumption on the supplied left
functional is required. -/
theorem exists_canonicalRankOne_of_complexRadius
    (Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (hcomm : ∀ f, Q (AbsorbingMarkovChains.ComplexKernel.ofReal f) =
      AbsorbingMarkovChains.ComplexKernel.ofReal (P f))
    (hP : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x)
    (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (μ f : ℂ))
    (hpair : μ g = 1)
    (hright : Q (AbsorbingMarkovChains.ComplexKernel.ofReal g) =
      (r : ℂ) • AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hleft : ∀ f, ℓ (Q f) = (r : ℂ) * ℓ f)
    (hspec : spectralRadius ℂ (AbsorbingMarkovChains.CompactRankOneGap.remainder Q r
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) ℓ) < ENNReal.ofReal r) :
    μ 1 ≠ 0 ∧ ∃ d : RankOneSpectralData P (1 : X →ᵇ ℝ),
      d.rate = r ∧ d.mean = (μ 1)⁻¹ • μ ∧ d.eigenvector = μ 1 • g ∧
      d.mean 1 = 1 ∧ (∀ x, 0 ≤ d.eigenvector x) := by
  have hpairC : ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal g) = 1 := by
    rw [hreal, hpair]
    rfl
  have hrightR : P g = r • g := by
    have he : AbsorbingMarkovChains.ComplexKernel.ofReal (P g - r • g) = 0 := by
      rw [map_sub, map_smul, ← hcomm, hright]
      ext x
      simp
    have hn : ‖P g - r • g‖ = 0 := by
      rw [← AbsorbingMarkovChains.ComplexKernel.norm_ofReal, he, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  obtain ⟨θ, hθ, hθone, C, hC, hgap⟩ :=
    AbsorbingMarkovChains.CompactRankOneGap.normalized_power_gap Q hr
      (AbsorbingMarkovChains.ComplexKernel.ofReal g) ℓ hpairC hright hleft hspec
  have hgapR (n : ℕ) (hn : 1 ≤ n) :
      ‖(r⁻¹ • P) ^ n - μ.smulRight g‖ ≤ C * θ ^ n := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hθ.le n))
    intro f
    have he : AbsorbingMarkovChains.ComplexKernel.ofReal
        (((r⁻¹ • P) ^ n - μ.smulRight g) f) =
        ((((r : ℂ)⁻¹ • Q) ^ n - ℓ.smulRight
          (AbsorbingMarkovChains.ComplexKernel.ofReal g))
            (AbsorbingMarkovChains.ComplexKernel.ofReal f)) := by
      rw [sub_apply, sub_apply, map_sub,
        ← ComplexGap.normalized_power_intertwines P Q
          AbsorbingMarkovChains.ComplexKernel.ofReal hcomm]
      congr 1
      ext x
      simp only [ContinuousLinearMap.smulRight_apply, map_smul,
        AbsorbingMarkovChains.ComplexKernel.ofReal_apply, hreal,
        BoundedContinuousFunction.smul_apply, smul_eq_mul, Complex.real_smul]
    rw [← AbsorbingMarkovChains.ComplexKernel.norm_ofReal, he]
    exact ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hgap n hn) (norm_nonneg _))).trans_eq
        (by rw [AbsorbingMarkovChains.ComplexKernel.norm_ofReal])
  let B := max C ‖1 - μ.smulRight g‖
  have hB : 0 ≤ B := hC.trans (le_max_left _ _)
  have hb (n : ℕ) : ‖(r⁻¹ • P) ^ n - μ.smulRight g‖ ≤ B * θ ^ n := by
    by_cases hn : n = 0
    · subst n
      simpa only [pow_zero, mul_one] using le_max_right C ‖1 - μ.smulRight g‖
    · exact (hgapR n (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le n))
  exact exists_canonicalRankOne_of_power_gap P r hr g μ hP hpair hrightR θ B
    hθ.le hθone hB hb

end ConditionedStochasticStabilityHyperbolic.ProjectorOrientation
