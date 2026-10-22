module

public import LeanShared.Analysis.AdjointAnnealedOperator

/-! The invariant common regular core and the full global regular test space
are distinct. Full tests see boundary distributions; restricting their dual
after spectral comparison recovers the supported pairing used for limits. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.CommonAmbientGlobalTests
variable {Reg Test F A C : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [AddCommGroup C] [Module ℂ C]

def restriction (j : Reg →L[ℂ] Test) :
    (Test →L[ℂ] ℂ) →L[ℂ] (Reg →L[ℂ] ℂ) :=
  (ContinuousLinearMap.compL ℂ Reg Test ℂ).flip j

@[simp] theorem restriction_apply (j : Reg →L[ℂ] Test) (d : Test →L[ℂ] ℂ) (v : Reg) :
    restriction j d v = d (j v) := rfl

theorem analytic_intertwining_of_core
    (qa : C →ₗ[ℂ] A) (denseA : DenseRange qa)
    (qr : C →ₗ[ℂ] Reg) (denseReg : DenseRange qr)
    (realize : Reg →L[ℂ] A) (realize_core : ∀ c, realize (qr c) = qa c)
    (physical : Reg →L[ℂ] F)
    (a : A →L[ℂ] (Test →L[ℂ] ℂ)) (b : F →L[ℂ] (Test →L[ℂ] ℂ))
    (common : ∀ c, a (qa c) = b (physical (qr c)))
    (P : A →L[ℂ] A) (Q : F →L[ℂ] F)
    (forward : Reg →L[ℂ] Reg) (inverse : Test →L[ℂ] Test)
    (analytic_core : ∀ c, P (qa c) = realize (forward (qr c)))
    (physical_forward : ∀ v, physical (forward v) = Q (physical v))
    (physical_duality : b.comp Q = (AdjointAnnealedOperator.transpose inverse).comp b) :
    a.comp P = (AdjointAnnealedOperator.transpose inverse).comp a := by
  have hcommon (v : Reg) : a (realize v) = b (physical v) := by
    apply denseReg.induction_on (p := fun v => a (realize v) = b (physical v)) v
      (isClosed_eq (a.continuous.comp realize.continuous) (b.continuous.comp physical.continuous))
    intro c
    rw [realize_core, common]
  apply ContinuousLinearMap.ext
  intro x
  apply denseA.induction_on
    (p := fun x => a (P x) = AdjointAnnealedOperator.transpose inverse (a x)) x
    (isClosed_eq (a.continuous.comp P.continuous)
      ((AdjointAnnealedOperator.transpose inverse).continuous.comp a.continuous))
  intro c
  rw [analytic_core, hcommon, physical_forward, common]
  exact congrArg (fun L : F →L[ℂ] (Test →L[ℂ] ℂ) => L (physical (qr c))) physical_duality

/-- The restriction identity is proved from ordinary pairings of smooth
functions, with density in both actual completed spaces. -/
theorem restriction_identity_of_core
    (qa : C →ₗ[ℂ] A) (denseA : DenseRange qa)
    (qr : C →ₗ[ℂ] Reg) (denseReg : DenseRange qr)
    (j : Reg →L[ℂ] Test)
    (aFull : A →L[ℂ] (Test →L[ℂ] ℂ)) (a : A →L[ℂ] (Reg →L[ℂ] ℂ))
    (pairing : ∀ c d, aFull (qa c) (j (qr d)) = a (qa c) (qr d)) :
    (restriction j).comp aFull = a := by
  apply ContinuousLinearMap.ext
  intro x
  apply denseA.induction_on (p := fun x => restriction j (aFull x) = a x) x
    (isClosed_eq ((restriction j).continuous.comp aFull.continuous) a.continuous)
  intro c
  apply ContinuousLinearMap.ext
  intro v
  apply denseReg.induction_on (p := fun v => aFull (qa c) (j v) = a (qa c) v) v
    (isClosed_eq ((aFull (qa c)).continuous.comp j.continuous) (a (qa c)).continuous)
  exact pairing c

end LeanShared.CommonAmbientGlobalTests
