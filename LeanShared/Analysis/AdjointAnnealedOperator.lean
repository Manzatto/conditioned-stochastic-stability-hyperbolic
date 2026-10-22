module

public import LeanShared.Analysis.AnnealedOperatorBounds

/-! An inverse regular-function average constructs the continuous common
ambient distribution operator. Its intertwining follows from the individual
Jacobian pairing identity; analytic intertwining is derived on the dense core. -/

@[expose] public noncomputable section
open MeasureTheory Set
namespace LeanShared.AdjointAnnealedOperator
variable {Reg F S C Ω : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [AddCommGroup C] [Module ℂ C]

def transpose (J : Reg →L[ℂ] Reg) : (Reg →L[ℂ] ℂ) →L[ℂ] (Reg →L[ℂ] ℂ) :=
  (ContinuousLinearMap.compL ℂ Reg Reg ℂ).flip J

@[simp] theorem transpose_apply (J : Reg →L[ℂ] Reg) (d : Reg →L[ℂ] ℂ) (v : Reg) :
    transpose J d v = d (J v) := rfl

section Average
variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  [CompleteSpace F] [CompleteSpace Reg]
  (T : Ω → F →L[ℂ] F) (J : Ω → Reg →L[ℂ] Reg)
  (hT : ∀ f, AEStronglyMeasurable (fun ω => T ω f) μ)
  (hJ : ∀ v, AEStronglyMeasurable (fun ω => J ω v) μ)
  (MT MJ : ℝ) (boundT : ∀ ω, ‖T ω‖ ≤ MT) (boundJ : ∀ ω, ‖J ω‖ ≤ MJ)
  (b : F →L[ℂ] (Reg →L[ℂ] ℂ))

/-- This is the per-map ordinary change-of-variables identity averaged by
Bochner integration, not an assumed identity between completed operators. -/
theorem averaged_pairing
    (individual : ∀ ω f v, b (T ω f) v = b f (J ω v)) :
    b.comp (AnnealedOperatorBounds.pointwiseAnnealed μ T hT MT boundT) =
      (transpose (AnnealedOperatorBounds.pointwiseAnnealed μ J hJ MJ boundJ)).comp b := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro v
  change (b.flip v) (∫ ω, T ω f ∂μ) = b f (∫ ω, J ω v ∂μ)
  rw [← (b.flip v).integral_comp_comm
      (AnnealedOperatorBounds.random_apply_integrable μ T hT MT boundT f),
    ← (b f).integral_comp_comm
      (AnnealedOperatorBounds.random_apply_integrable μ J hJ MJ boundJ v)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => individual ω f v)
end Average

/-- A common smooth pairing and the actual regular action suffice to prove
analytic intertwining with the produced ambient operator by density. -/
theorem analytic_intertwining_of_core
    (qa : C →ₗ[ℂ] S) (denseS : DenseRange qa)
    (qr : C →ₗ[ℂ] Reg) (denseReg : DenseRange qr)
    (realize : Reg →L[ℂ] S) (realize_core : ∀ c, realize (qr c) = qa c)
    (physical : Reg →L[ℂ] F)
    (a : S →L[ℂ] (Reg →L[ℂ] ℂ)) (b : F →L[ℂ] (Reg →L[ℂ] ℂ))
    (common : ∀ c, a (qa c) = b (physical (qr c)))
    (P : S →L[ℂ] S) (Q : F →L[ℂ] F) (forward inverse : Reg →L[ℂ] Reg)
    (analytic_core : ∀ c, P (qa c) = realize (forward (qr c)))
    (physical_forward : ∀ v, physical (forward v) = Q (physical v))
    (physical_duality : b.comp Q = (transpose inverse).comp b) :
    a.comp P = (transpose inverse).comp a := by
  have hcommon (v : Reg) : a (realize v) = b (physical v) := by
    apply denseReg.induction_on (p := fun v => a (realize v) = b (physical v)) v
      (isClosed_eq (a.continuous.comp realize.continuous) (b.continuous.comp physical.continuous))
    intro c
    rw [realize_core, common]
  apply ContinuousLinearMap.ext
  intro x
  apply denseS.induction_on
    (p := fun x => a (P x) = transpose inverse (a x)) x
    (isClosed_eq (a.continuous.comp P.continuous) ((transpose inverse).continuous.comp a.continuous))
  intro c
  rw [analytic_core, hcommon, physical_forward, common]
  exact congrArg (fun L : F →L[ℂ] (Reg →L[ℂ] ℂ) => L (physical (qr c))) physical_duality

end LeanShared.AdjointAnnealedOperator
