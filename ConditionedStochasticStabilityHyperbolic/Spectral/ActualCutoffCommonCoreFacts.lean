module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonAmbientRawComparison
public import ConditionedStochasticStabilityHyperbolic.Spectral.CutoffClosedCoreRange
public import LeanShared.Geometry.GlobalTestPairing

/-! Actual supported cutoff kernels supply common-core spectral comparison.
Faithfulness and range in the supported Banach core are derived; the full
global test dual sees boundary distributions. The only spectral source is
the universal classical Banach comparison, before any noise choice. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.ActualCutoffCommonCoreFacts
open LeanShared SmoothSupportedManifoldCore
variable {E M Reg A W Test D Ω : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  [AddCommGroup D] [Module ℂ D] [MeasurableSpace Ω]
  {V K : Set M} [CompactSpace K]

theorem from_actual_cutoff_and_KL
    (hK : IsClosed K) (hV : IsOpen V)
    (qr : core (E := E) V →ₗ[ℂ] Reg) (denseReg : DenseRange qr)
    (qa : core (E := E) V →ₗ[ℂ] A) (denseA : DenseRange qa)
    (realize : Reg →L[ℂ] A) (realize_core : ∀ c, realize (qr c) = qa c)
    (physical : Reg →L[ℂ] (K →ᵇ ℂ))
    (hphysical : ∀ c, physical (qr c) = physicalCore V K c)
    (σ : Measure K) [IsFiniteMeasure σ]
    (hpositive : {x : K | x.val ∈ V} ⊆ σ.support)
    (globalPhysical : Test →L[ℂ] (K →ᵇ ℂ))
    (j : Reg →L[ℂ] Test) (hj : ∀ v, globalPhysical (j v) = physical v)
    (qt : D →ₗ[ℂ] Test) (denseTest : DenseRange qt)
    (aFull : A →L[ℂ] (Test →L[ℂ] ℂ)) (haFull : Function.Injective aFull)
    (smoothPairing : ∀ c d, aFull (qa c) (qt d) =
      ∫ x, physicalCore V K c x * globalPhysical (qt d) x ∂σ)
    (P : ℝ≥0 → A →L[ℂ] A) (i : A →L[ℂ] W)
    (h : KellerLiverani1999.Hypotheses P i) (hic : IsCompactOperator i)
    (ε : ℝ≥0) (hε : ε ≤ h.window) (scale : ℝ) (hscale : 0 < scale)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : M × Ω → M) (hF : Measurable F)
    (wc : K → ℝ) (hwc : Measurable wc) (hwcBound : ∀ x, wc x ≤ scale)
    (sf : HasStrongFellerKernel
      (RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc scale hscale hwcBound))
    (hwSupport : tsupport wc ⊆ {x : K | x.val ∈ V})
    (forward : Reg →L[ℂ] Reg) (inverse : Test →L[ℂ] Test)
    (analytic_core : ∀ c, ((scale : ℂ) • P ε) (qa c) = realize (forward (qr c)))
    (physical_forward : ∀ v, physical (forward v) =
      ((scale : ℂ) • ComplexStrongFeller.transferOperator
        (RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc scale hscale hwcBound) sf)
        (physical v))
    (physical_duality : (SupportedRegularPairing.embedding σ globalPhysical).comp
      ((scale : ℂ) • ComplexStrongFeller.transferOperator
        (RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc scale hscale hwcBound) sf) =
      (AdjointAnnealedOperator.transpose inverse).comp
        (SupportedRegularPairing.embedding σ globalPhysical))
    (cutoff : ℝ) (hcutoff : h.alpha < cutoff)
    (ultra : StrongFellerSquareCompact.UltraFellerContract (X := K))
    (classical : CommonAmbientClassicalComparison.ClassicalContract (A := A)
      (F := SupportedPairingClosedCore.space physical) (Z := Test →L[ℂ] ℂ)
      (Reg := Reg) (W := W)) :
    KellerLiverani1999.CommonCoreSpectralFacts ((scale : ℂ) • P ε)
      (RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc scale hscale hwcBound)
      sf scale (scale * cutoff) aFull (SupportedRegularPairing.embedding σ globalPhysical) := by
  let C := RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc scale hscale hwcBound
  let Q := (scale : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf
  have common (c : core (E := E) V) :
      aFull (qa c) = SupportedRegularPairing.embedding σ globalPhysical (physical (qr c)) := by
    rw [hphysical]
    exact GlobalTestPairing.common_identity_from_global_smooth_tests σ qa qt denseTest
      aFull (physicalCore V K) globalPhysical smoothPairing c
  have hb := GlobalTestPairing.full_pairing_injective_of_restriction σ physical
    globalPhysical j hj (SupportedPairingClosedCore.space physical)
    (physical_closedCore_pairing_injective qr denseReg physical hphysical σ hpositive)
  have rangeQ : ∀ f, Q f ∈ SupportedPairingClosedCore.space physical := fun f =>
    CutoffClosedCoreRange.raw_transfer_mem_closedCore ρ F hF K hK.measurableSet wc hwc
      scale hscale hwcBound sf qr physical hphysical hK hV hwSupport (scale : ℂ) f
  have compactQ : IsCompactOperator (Q ^ 2 : (K →ᵇ ℂ) →L[ℂ] (K →ᵇ ℂ)) := by
    have heq : (Q ^ 2 : (K →ᵇ ℂ) →L[ℂ] (K →ᵇ ℂ)) =
        ((scale : ℂ) * (scale : ℂ)) •
          (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf ^ 2) := by
      ext f x
      simp only [Q, pow_two, mul_apply_eq_comp, smul_apply, map_smul,
        smul_smul]
    rw [heq]
    change IsCompactOperator (((scale : ℂ) * (scale : ℂ)) •
      (fun f => (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf ^ 2) f))
    exact (StrongFellerSquareCompact.square_compact ultra C sf).smul _
  exact CommonAmbientClassicalComparison.Facts.to_same_cutoff _ C sf scale (scale * cutoff)
    aFull (SupportedRegularPairing.embedding σ globalPhysical)
    (CommonAmbientClassicalComparison.facts_of_actual_core_and_normalized_KL qa denseA qr
      denseReg realize realize_core physical aFull (SupportedRegularPairing.embedding σ globalPhysical)
      common P i h hic ε hε scale hscale Q forward inverse analytic_core physical_forward
      physical_duality rangeQ haFull hb compactQ cutoff hcutoff classical)

end ConditionedStochasticStabilityHyperbolic.ActualCutoffCommonCoreFacts
