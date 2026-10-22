module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonAmbientClassicalComparison
public import LeanShared.Analysis.CommonAmbientGlobalTests

/-! Actual dense core actions and the inverse global-test transpose fill
the classical comparison hypotheses on a genuine closed physical core.
No cross-space eigenvector comparison is an application-specific input. -/

@[expose] public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
open LeanShared
variable {A F Reg Test C W : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  [AddCommGroup C] [Module ℂ C]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

theorem facts_of_actual_core
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
    (physical_duality : b.comp Q = (AdjointAnnealedOperator.transpose inverse).comp b)
    (hQ : ∀ f, Q f ∈ DyadicCompletion.closedCore physical.toLinearMap)
    (ha : Function.Injective a)
    (hb : Function.Injective (b.comp (DyadicCompletion.closedCore physical.toLinearMap).subtypeL))
    (i : A →L[ℂ] W) (hi : Function.Injective i) (hic : IsCompactOperator i)
    (α R C₀ D K ρ : ℝ) (hα : 0 < α) (hαR : α < R)
    (hC : 0 ≤ C₀) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (weak : ∀ n x, ‖i ((P ^ n) x)‖ ≤ K * R ^ n * ‖i x‖)
    (strong : ∀ n x, ‖(P ^ n) x‖ ≤ C₀ * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (compactQ : IsCompactOperator (Q ^ 2 : F →L[ℂ] F)) (hαρ : α < ρ)
    (classical : ClassicalContract (A := A)
      (F := DyadicCompletion.closedCore physical.toLinearMap)
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    Facts P Q a b ρ := by
  let V := DyadicCompletion.closedCore physical.toLinearMap
  let cF : Reg →L[ℂ] V := physical.codRestrict V
    (fun v => physical.toLinearMap.range.le_topologicalClosure ⟨v, rfl⟩)
  let Q0 := ClosedCoreSpectralReduction.operator V Q hQ
  let b0 := b.comp V.subtypeL
  let L := AdjointAnnealedOperator.transpose inverse
  have denseRealize : DenseRange realize := by
    intro x
    apply closure_mono (s := range qa) (t := range realize) ?_ (denseA x)
    rintro _ ⟨c, rfl⟩
    exact ⟨qr c, realize_core c⟩
  have densePhysical : DenseRange cF := DyadicCompletion.coreLift_dense physical.toLinearMap
  have hcommon (v : Reg) : a (realize v) = b (physical v) := by
    apply denseReg.induction_on (p := fun v => a (realize v) = b (physical v)) v
      (isClosed_eq (a.continuous.comp realize.continuous) (b.continuous.comp physical.continuous))
    intro c
    rw [realize_core, common]
  have hanalytic : a.comp P = L.comp a := CommonAmbientGlobalTests.analytic_intertwining_of_core
    qa denseA qr denseReg realize realize_core physical a b common P Q forward inverse
    analytic_core physical_forward physical_duality
  have hphysical : b0.comp Q0 = L.comp b0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun M : F →L[ℂ] (Test →L[ℂ] ℂ) => M f.val) physical_duality
  have hcore : a.comp realize = b0.comp cF := by
    apply ContinuousLinearMap.ext
    intro v
    exact hcommon v
  have haCore : P.comp realize = realize.comp forward := by
    apply ContinuousLinearMap.ext
    intro v
    apply denseReg.induction_on (p := fun v => P (realize v) = realize (forward v)) v
      (isClosed_eq (P.continuous.comp realize.continuous) (realize.continuous.comp forward.continuous))
    intro c
    rw [realize_core, analytic_core]
  have hbCore : Q0.comp cF = cF.comp forward := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    exact (physical_forward v).symm
  have hcompact0 : IsCompactOperator (Q0 ^ 2 : V →L[ℂ] V) :=
    ClosedCoreSpectralReduction.square_compact V Q hQ physical.toLinearMap.range.isClosed_topologicalClosure compactQ
  have facts0 := classical P Q0 L a b0 ha hb hanalytic hphysical
    realize cF forward denseRealize densePhysical hcore haCore hbCore
    i hi hic α R C₀ D K hα hαR hC hD hK weak strong hcompact0 ρ hαρ
  exact Facts.of_closed_range P Q a b ρ (hα.trans hαρ) V hQ facts0

end ConditionedStochasticStabilityHyperbolic.CommonAmbientClassicalComparison
