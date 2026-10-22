module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonAmbientRestriction
public import LeanShared.Geometry.GlobalTestPairing

/-! The full global-test comparison descends to the supported regular test
dual used by local/global probability consumers. Restriction identities are
proved on actual dense smooth cores; supported tests need not separate all
analytic boundary distributions. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared
variable {A Reg Test Core Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  [AddCommGroup Core] [Module ℂ Core]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem CommonCoreSpectralFacts.restrict_global_tests
    (P : A →L[ℂ] A) (C : AbsorbingMarkovChains.CanonicalChain Y)
    (hC : HasStrongFellerKernel C) (R ρ : ℝ)
    (σ : Measure Y) [IsFiniteMeasure σ]
    (qa : Core →ₗ[ℂ] A) (denseA : DenseRange qa)
    (qr : Core →ₗ[ℂ] Reg) (denseReg : DenseRange qr)
    (j : Reg →L[ℂ] Test)
    (physical : Reg →L[ℂ] (Y →ᵇ ℂ)) (globalPhysical : Test →L[ℂ] (Y →ᵇ ℂ))
    (hphysical : ∀ v, globalPhysical (j v) = physical v)
    (aFull : A →L[ℂ] (Test →L[ℂ] ℂ)) (a : A →L[ℂ] (Reg →L[ℂ] ℂ))
    (smoothPairing : ∀ c d, aFull (qa c) (j (qr d)) = a (qa c) (qr d))
    (facts : CommonCoreSpectralFacts P C hC R ρ aFull
      (SupportedRegularPairing.embedding σ globalPhysical)) :
    CommonCoreSpectralFacts P C hC R ρ a (SupportedRegularPairing.embedding σ physical) := by
  have ha := CommonAmbientGlobalTests.restriction_identity_of_core qa denseA qr denseReg j
    aFull a smoothPairing
  have hb := GlobalTestPairing.restriction_embedding σ physical globalPhysical j hphysical
  have f : CommonAmbientClassicalComparison.Facts P
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC) aFull
      (SupportedRegularPairing.embedding σ globalPhysical) ρ :=
    ⟨facts.ordinary, facts.generalized, facts.reverse⟩
  have fr := f.map_ambient (CommonAmbientGlobalTests.restriction j)
  rw [ha, hb] at fr
  exact fr.to_same_cutoff P C hC R ρ a (SupportedRegularPairing.embedding σ physical)

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
