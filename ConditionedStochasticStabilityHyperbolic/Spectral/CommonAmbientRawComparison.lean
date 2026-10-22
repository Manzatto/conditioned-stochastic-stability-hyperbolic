module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonAmbientRawBounds
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCommonAmbientComparison

/-! Apply the cited common-ambient comparison to the actual raw cutoff
operators. All analytic power estimates are produced from normalized KL
hypotheses, rather than supplied as raw comparison premises. -/
@[expose] public noncomputable section
open Set
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
open LeanShared
variable {A F Reg Test C W : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  [AddCommGroup C] [Module ℂ C]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

theorem facts_of_actual_core_and_normalized_KL
    (qa : C →ₗ[ℂ] A) (denseA : DenseRange qa)
    (qr : C →ₗ[ℂ] Reg) (denseReg : DenseRange qr)
    (realize : Reg →L[ℂ] A) (realize_core : ∀ c, realize (qr c) = qa c)
    (physical : Reg →L[ℂ] F)
    (a : A →L[ℂ] (Test →L[ℂ] ℂ)) (b : F →L[ℂ] (Test →L[ℂ] ℂ))
    (common : ∀ c, a (qa c) = b (physical (qr c)))
    (P : ℝ≥0 → A →L[ℂ] A) (i : A →L[ℂ] W)
    (h : KellerLiverani1999.Hypotheses P i) (hic : IsCompactOperator i)
    (ε : ℝ≥0) (hε : ε ≤ h.window) (scale : ℝ) (hscale : 0 < scale)
    (Q : F →L[ℂ] F)
    (forward : Reg →L[ℂ] Reg) (inverse : Test →L[ℂ] Test)
    (analytic_core : ∀ c, ((scale : ℂ) • P ε) (qa c) = realize (forward (qr c)))
    (physical_forward : ∀ v, physical (forward v) = Q (physical v))
    (physical_duality : b.comp Q = (AdjointAnnealedOperator.transpose inverse).comp b)
    (hQ : ∀ f, Q f ∈ DyadicCompletion.closedCore physical.toLinearMap)
    (ha : Function.Injective a)
    (hb : Function.Injective (b.comp (DyadicCompletion.closedCore physical.toLinearMap).subtypeL))
    (compactQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F))
    (cutoff : ℝ) (hcutoff : h.alpha < cutoff)
    (classical : ClassicalContract (A := A)
      (F := DyadicCompletion.closedCore physical.toLinearMap)
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    Facts ((scale : ℂ) • P ε) Q a b (scale * cutoff) := by
  exact facts_of_actual_core qa denseA qr denseReg realize realize_core physical a b common
    ((scale : ℂ) • P ε) Q forward inverse analytic_core physical_forward physical_duality
    hQ ha hb i h.weak_injective hic
    (scale * h.alpha) (scale * h.weakRate) h.strongConstant h.errorConstant h.weakConstant
    (scale * cutoff) (mul_pos hscale h.alpha_pos)
    (mul_lt_mul_of_pos_left h.alpha_lt_weakRate hscale)
    h.strongConstant_pos.le h.errorConstant_pos.le h.weakConstant_pos.le
    (CommonAmbientRawBounds.weak_growth h ε hε scale hscale)
    (CommonAmbientRawBounds.twoNorm_growth h ε hε scale hscale)
    compactQ (mul_lt_mul_of_pos_left hcutoff hscale) classical

end ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
