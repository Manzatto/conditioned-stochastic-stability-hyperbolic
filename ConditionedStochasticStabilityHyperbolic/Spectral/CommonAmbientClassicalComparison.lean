module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ClassicalCommonCoreSources
public import LeanShared.Analysis.ClosedCoreSpectralReduction

/-! The precise classical common-ambient comparison is applied on the closed
supported regular core. Nonzero generalized vectors of the full cutoff
operator lie in that core, so the resulting comparison extends to full C0.
The classical contract below is Hennion's essential-radius bound combined
with Baladi, Positive Transfer Operators, Appendix A.2; it contains only
ordinary bounded operators, dense invariant common cores and power bounds. -/

@[expose] public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
open LeanShared
variable {A F Z : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

structure Facts (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] Z) (b : F →L[ℂ] Z) (ρ : ℝ) : Prop where
  ordinary : ComparedSpectralGap.EigenvectorComparison P Q a b ρ
  generalized : ∀ z : ℂ, ρ < ‖z‖ → GeneralizedSpectralComparison.Comparison P Q a b z
  reverse : ∀ γ, γ ≠ 0 → ∀ z : ℂ, P γ = z • γ → ρ < ‖z‖ →
    ∃ f : F, f ≠ 0 ∧ Q f = z • f ∧ b f = a γ

section Classical
variable {Reg W : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A deferred ordinary functional-analysis theorem, quantified before all
noise and projector choices. Compact weak inclusion and actual power bounds
supply the essential-radius premise; square compactness supplies it on F.
The dense common core is the range of Reg in both realizations. -/
def ClassicalContract [CompleteSpace A] [CompleteSpace F] [CompleteSpace W] : Prop :=
  ∀ (P : A →L[ℂ] A) (Q : F →L[ℂ] F) (L : Z →L[ℂ] Z)
    (a : A →L[ℂ] Z) (b : F →L[ℂ] Z),
    Function.Injective a → Function.Injective b →
    a.comp P = L.comp a → b.comp Q = L.comp b →
    ∀ (cA : Reg →L[ℂ] A) (cF : Reg →L[ℂ] F) (U : Reg →L[ℂ] Reg),
    DenseRange cA → DenseRange cF → a.comp cA = b.comp cF →
    P.comp cA = cA.comp U → Q.comp cF = cF.comp U →
    ∀ i : A →L[ℂ] W, Function.Injective i → IsCompactOperator i →
    ∀ α R C D K : ℝ, 0 < α → α < R → 0 ≤ C → 0 ≤ D → 0 ≤ K →
    (∀ n x, ‖i ((P ^ n) x)‖ ≤ K * R ^ n * ‖i x‖) →
    (∀ n x, ‖(P ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) →
    IsCompactOperator (Q ^ 2 : F →L[ℂ] F) →
    ∀ ρ : ℝ, α < ρ → Facts P Q a b ρ
end Classical

/-- The comparison theorem is used on a genuine closed Banach core, then
extended to all continuous functions by the cutoff range property. -/
theorem Facts.of_closed_range
    (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (a : A →L[ℂ] Z) (b : F →L[ℂ] Z) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Submodule ℂ F) (hQ : ∀ f, Q f ∈ V)
    (facts : Facts P (ClosedCoreSpectralReduction.operator V Q hQ)
      a (b.comp V.subtypeL) ρ) : Facts P Q a b ρ where
  ordinary := by
    intro f hf z he hz
    have hz0 : z ≠ 0 := by intro h; simpa [h] using hρ.trans hz
    have hm : f ∈ V := ClosedCoreSpectralReduction.generalized_mem V Q hQ z hz0 1 f (by
      simp only [pow_one, sub_apply, smul_apply, one_apply_eq_self, he, sub_self])
    let fv : V := ⟨f, hm⟩
    have hfv : fv ≠ 0 := fun h => hf (congrArg Subtype.val h)
    have heV : ClosedCoreSpectralReduction.operator V Q hQ fv = z • fv := by
      apply Subtype.ext
      exact he
    exact facts.ordinary fv hfv z heV hz
  generalized := by
    intro z hz k f hf he
    have hz0 : z ≠ 0 := by intro h; simpa [h] using hρ.trans hz
    have hm := ClosedCoreSpectralReduction.generalized_mem V Q hQ z hz0 k f he
    let fv : V := ⟨f, hm⟩
    have hfv : fv ≠ 0 := fun h => hf (congrArg Subtype.val h)
    exact facts.generalized z hz k fv hfv
      (ClosedCoreSpectralReduction.restricted_generalized V Q hQ z k fv he)
  reverse := by
    intro γ hγ z he hz
    obtain ⟨f, hf, heQ, hmatch⟩ := facts.reverse γ hγ z he hz
    refine ⟨f.val, (fun h => hf (Subtype.ext h)), ?_, hmatch⟩
    exact congrArg Subtype.val heQ

/-- Final adapter to the already checked same-cutoff source consumer. -/
theorem Facts.to_same_cutoff {Y : Type*} [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (P : A →L[ℂ] A) (C : AbsorbingMarkovChains.CanonicalChain Y)
    (hC : HasStrongFellerKernel C) (R ρ : ℝ)
    (a : A →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z)
    (facts : Facts P ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC) a b ρ) :
    KellerLiverani1999.CommonCoreSpectralFacts P C hC R ρ a b :=
  ⟨facts.ordinary, facts.generalized, facts.reverse⟩

end ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
