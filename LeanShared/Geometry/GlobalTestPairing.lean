module

public import LeanShared.Geometry.SupportedRegularPairing
public import LeanShared.Analysis.CommonAmbientGlobalTests

/-! The full global regular test dual is faithful to distributions on the
closed domain. Its restriction recovers the supported regular pairing used
in probability weak limits, with no new compatibility assumption. -/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace LeanShared.GlobalTestPairing
variable {X Reg Test A C D : Type*}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]

variable (σ : Measure X) [IsFiniteMeasure σ]

theorem restriction_embedding
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (globalPhysical : Test →L[ℂ] (X →ᵇ ℂ))
    (j : Reg →L[ℂ] Test) (hphysical : ∀ v, globalPhysical (j v) = physical v) :
    (CommonAmbientGlobalTests.restriction j).comp
        (SupportedRegularPairing.embedding σ globalPhysical) =
      SupportedRegularPairing.embedding σ physical := by
  ext f v
  change (∫ x, f x * globalPhysical (j v) x ∂σ) = ∫ x, f x * physical v x ∂σ
  rw [hphysical]

/-- Faithfulness on the actual supported core transfers to the larger
full test dual by restricting tests, without reference support on all X. -/
theorem full_pairing_injective_of_restriction
    (physical : Reg →L[ℂ] (X →ᵇ ℂ)) (globalPhysical : Test →L[ℂ] (X →ᵇ ℂ))
    (j : Reg →L[ℂ] Test) (hphysical : ∀ v, globalPhysical (j v) = physical v)
    (V : Submodule ℂ (X →ᵇ ℂ))
    (hinj : Function.Injective ((SupportedRegularPairing.embedding σ physical).comp V.subtypeL)) :
    Function.Injective ((SupportedRegularPairing.embedding σ globalPhysical).comp V.subtypeL) := by
  intro f g hfg
  apply hinj
  have hrestrict (x : X →ᵇ ℂ) :
      CommonAmbientGlobalTests.restriction j
        (SupportedRegularPairing.embedding σ globalPhysical x) =
        SupportedRegularPairing.embedding σ physical x :=
    congrArg (fun L : (X →ᵇ ℂ) →L[ℂ] (Reg →L[ℂ] ℂ) => L x)
      (restriction_embedding σ physical globalPhysical j hphysical)
  exact (hrestrict f.val).symm.trans
    ((congrArg (CommonAmbientGlobalTests.restriction j) hfg).trans (hrestrict g.val))

/-- Pairing against genuine global smooth tests determines equality in the
full test dual by density. Only the smooth integral identity is input. -/
theorem common_identity_from_global_smooth_tests
    (qa : C →ₗ[ℂ] A) (qt : D →ₗ[ℂ] Test) (denseTest : DenseRange qt)
    (a : A →L[ℂ] (Test →L[ℂ] ℂ))
    (physicalCore : C →ₗ[ℂ] (X →ᵇ ℂ)) (globalPhysical : Test →L[ℂ] (X →ᵇ ℂ))
    (smoothPairing : ∀ c d, a (qa c) (qt d) =
      ∫ x, physicalCore c x * globalPhysical (qt d) x ∂σ) (c : C) :
    a (qa c) = SupportedRegularPairing.embedding σ globalPhysical (physicalCore c) := by
  apply ContinuousLinearMap.ext
  intro v
  apply denseTest.induction_on
    (p := fun v => a (qa c) v =
      SupportedRegularPairing.embedding σ globalPhysical (physicalCore c) v) v
    (isClosed_eq (a (qa c)).continuous
      (SupportedRegularPairing.embedding σ globalPhysical (physicalCore c)).continuous)
  exact smoothPairing c

end LeanShared.GlobalTestPairing
