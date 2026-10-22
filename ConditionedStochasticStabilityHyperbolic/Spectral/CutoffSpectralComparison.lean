module

public import ConditionedStochasticStabilityHyperbolic.Restriction.WeightAgreement
public import ConditionedStochasticStabilityHyperbolic.Restriction.RawGeometricSeparator
public import Mathlib.Analysis.Normed.Operator.Basic
public import ConditionedStochasticStabilityHyperbolic.Spectral.GeneralizedSpectralComparison

/-! # Same-cutoff cited comparison to physical retained-region comparison

The classical comparison is applied to the same cutoff operator on two
functional spaces. Actual kernel restriction/lifting then transports it to
the different physical weight, matching only the retained region.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.CutoffSpectralComparison

open Restriction

variable {X : Type*} [TopologicalSpace X]

private theorem scaled_power (P : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) (s : ℂ) (n : ℕ) :
    (s • P) ^ n = s ^ n • P ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      ext f
      simp only [pow_succ', mul_apply_eq_comp, ih, smul_apply, map_smul, smul_smul]
      rw [mul_comm (s ^ n) s]

def Matching (P Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) (V : Set X) : Prop :=
  ∀ z : ℂ, z ≠ 0 → ∀ k : ℕ, ∀ f : X →ᵇ ℂ, f ≠ 0 →
    ((P - z • 1) ^ k) f = 0 → ∃ g : X →ᵇ ℂ,
      g ≠ 0 ∧ restrictObservable V g = restrictObservable V f ∧
      ((Q - z • 1) ^ k) g = 0

theorem matching_of_actual_kernel_certificates
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (C D : AbsorbingMarkovChains.CanonicalChain X)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (V BC BD : Set X) (hV : MeasurableSet V)
    (heq : LeanShared.SubtypeKernel.restrict C.killedTransition V hV =
      LeanShared.SubtypeKernel.restrict D.killedTransition V hV)
    (hreturnC : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ BC)
    (hextC : ∀ x ∈ BC, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (hreturnD : ∀ x : V, ∀ᵐ y ∂D.killedTransition x.val, y ∉ V → y ∈ BD)
    (hextD : ∀ x ∈ BD, ∃ n : ℕ,
      D.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (NC ND : ℕ)
    (hcompC : ∀ x : ↥(Vᶜ),
      ((LeanShared.SubtypeKernel.restrict C.killedTransition Vᶜ hV.compl) ^ NC) x univ = 0)
    (hcompD : ∀ x : ↥(Vᶜ),
      ((LeanShared.SubtypeKernel.restrict D.killedTransition Vᶜ hV.compl) ^ ND) x univ = 0)
    (s : ℂ) (hs : s ≠ 0) : Matching
      (s • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      (s • ComplexStrongFeller.transferOperator (𝕜 := ℂ) D hD) V := by
  intro z hz k f hf hgen
  have hnz : s⁻¹ * z ≠ 0 := mul_ne_zero (inv_ne_zero hs) hz
  have hscale (P : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) :
      s • P - z • 1 = s • (P - (s⁻¹ * z) • 1) := by
    rw [smul_sub, smul_smul, mul_inv_cancel_left₀ hs]
  rw [hscale, scaled_power, smul_apply] at hgen
  have hnorm : ((ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC -
      (s⁻¹ * z) • 1) ^ k) f = 0 :=
    (smul_eq_zero.mp hgen).resolve_left (pow_ne_zero _ hs)
  obtain ⟨g, hg, hRg, hnormg⟩ := exists_matching_nonzero_generalized_eigenfunction
    C D hC hD V BC BD hV heq hreturnC hextC hreturnD hextD NC ND hcompC hcompD
    hnz k f hf hnorm
  refine ⟨g, hg, hRg, ?_⟩
  rw [hscale, scaled_power, smul_apply, hnormg, smul_zero]

variable {A W Z : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem eigenvector_comparison_of_same_cutoff
    (P : A →L[ℂ] A) (QC QD : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) (V : Set X)
    (hmatch : Matching QC QD V)
    (a : A →L[ℂ] W) (bD : (X →ᵇ ℂ) →L[ℂ] W)
    (r : W →L[ℂ] Z) (c : (V →ᵇ ℂ) →L[ℂ] Z)
    (hrestriction : r.comp bD = c.comp (restrictObservable V))
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hsource : ComparedSpectralGap.EigenvectorComparison P QD a bD ρ) :
    ComparedSpectralGap.EigenvectorComparison P QC (r.comp a)
      (c.comp (restrictObservable V)) ρ := by
  intro f hf z he hz
  have hz0 : z ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero] at hz
    exact (not_lt_of_ge hρ) hz
  have hgen : ((QC - z • 1) ^ (1 : ℕ)) f = 0 := by
    simp only [pow_one, sub_apply, smul_apply, one_apply_eq_self, he, sub_self]
  obtain ⟨g, hg, hRg, hgg⟩ := hmatch z hz0 1 f hf hgen
  have hge : QD g = z • g := by
    simpa only [pow_one, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using hgg
  obtain ⟨v, hv, hPv, hbg⟩ := hsource g hg z hge hz
  refine ⟨v, hv, hPv, ?_⟩
  change c (restrictObservable V f) = r (a v)
  rw [← hRg]
  have hr := congrArg (fun L : (X →ᵇ ℂ) →L[ℂ] Z => L g) hrestriction
  change r (bD g) = c (restrictObservable V g) at hr
  rw [← hr, hbg]

theorem generalized_comparison_of_same_cutoff
    (P : A →L[ℂ] A) (QC QD : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) (V : Set X)
    (hmatch : Matching QC QD V)
    (a : A →L[ℂ] W) (bD : (X →ᵇ ℂ) →L[ℂ] W)
    (r : W →L[ℂ] Z) (c : (V →ᵇ ℂ) →L[ℂ] Z)
    (hrestriction : r.comp bD = c.comp (restrictObservable V))
    (z : ℂ) (hz : z ≠ 0)
    (hsource : GeneralizedSpectralComparison.Comparison P QD a bD z) :
    GeneralizedSpectralComparison.Comparison P QC (r.comp a)
      (c.comp (restrictObservable V)) z := by
  intro k f hf hgen
  obtain ⟨g, hg, hRg, hgg⟩ := hmatch z hz k f hf hgen
  obtain ⟨v, hv, hbg⟩ := hsource k g hg hgg
  refine ⟨v, hv, ?_⟩
  change c (restrictObservable V f) = r (a v)
  rw [← hRg]
  have hr := congrArg (fun L : (X →ᵇ ℂ) →L[ℂ] Z => L g) hrestriction
  change r (bD g) = c (restrictObservable V g) at hr
  rw [← hr, hbg]

end ConditionedStochasticStabilityHyperbolic.CutoffSpectralComparison
