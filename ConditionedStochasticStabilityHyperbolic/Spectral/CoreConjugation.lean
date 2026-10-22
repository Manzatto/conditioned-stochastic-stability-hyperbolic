module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniApplication
public import Mathlib.Analysis.Normed.Operator.Extend

/-! A literal core conjugation preserving the physical norm constructs the
conjugation on its completion. Completed real-operator structure is a conclusion. -/

public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.CoreConjugation
open KellerLiverani1999

variable {C S Reg : Type*} [AddCommGroup C] [Module ℂ C]
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]

structure CoreData (q : C →ₗ[ℂ] S) where
  conjugate : C →ₗ[ℝ] C
  involutive : Function.Involutive conjugate
  smul : ∀ (z : ℂ) c, conjugate (z • c) = star z • conjugate c
  norm : ∀ c, ‖q (conjugate c)‖ = ‖q c‖

variable (q : C →ₗ[ℂ] S) (dense : DenseRange q) (d : CoreData q)

@[expose] def extension : S →L[ℝ] S :=
  ((q.restrictScalars ℝ).comp d.conjugate).extendOfNorm (q.restrictScalars ℝ)

include dense

@[simp] theorem extension_core (c : C) : extension q d (q c) = q (d.conjugate c) := by
  exact LinearMap.extendOfNorm_eq (f := (q.restrictScalars ℝ).comp d.conjugate)
    (e := q.restrictScalars ℝ) dense
    ⟨1, fun c => by simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, one_mul] using (d.norm c).le⟩ c

theorem extension_involutive : Function.Involutive (extension q d) := by
  intro x
  apply dense.induction_on (p := fun x => extension q d (extension q d x) = x) x
    (isClosed_eq ((extension q d).continuous.comp (extension q d).continuous) continuous_id)
  intro c
  rw [extension_core q dense, extension_core q dense, d.involutive]

theorem extension_smul (z : ℂ) (x : S) :
    extension q d (z • x) = star z • extension q d x := by
  apply dense.induction_on
    (p := fun x => extension q d (z • x) = star z • extension q d x) x
    (isClosed_eq ((extension q d).continuous.comp (continuous_const.smul continuous_id))
      (continuous_const.smul (extension q d).continuous))
  intro c
  rw [← q.map_smul, extension_core q dense, d.smul, q.map_smul, extension_core q dense]

theorem extension_realize (qReg : C →ₗ[ℂ] Reg) (denseReg : DenseRange qReg)
    (realize : Reg →L[ℂ] S) (hrealize : ∀ c, realize (qReg c) = q c)
    (J : Reg →L[ℝ] Reg) (hJ : ∀ c, J (qReg c) = qReg (d.conjugate c)) (v : Reg) :
    extension q d (realize v) = realize (J v) := by
  apply denseReg.induction_on
    (p := fun v => extension q d (realize v) = realize (J v)) v
    (isClosed_eq ((extension q d).continuous.comp realize.continuous)
      (realize.continuous.comp J.continuous))
  intro c
  rw [hrealize, extension_core q dense, hJ, hrealize]

@[expose] def operator (P : S →L[ℂ] S)
    (qReg : C →ₗ[ℂ] Reg) (denseReg : DenseRange qReg)
    (realize : Reg →L[ℂ] S) (hrealize : ∀ c, realize (qReg c) = q c)
    (J : Reg →L[ℝ] Reg) (hJ : ∀ c, J (qReg c) = qReg (d.conjugate c))
    (action : C →ₗ[ℂ] Reg) (hP : ∀ c, P (q c) = realize (action c))
    (haction : ∀ c, action (d.conjugate c) = J (action c)) :
    RealOperatorConjugation P where
  conjugate := extension q d
  involutive := extension_involutive q dense d
  zero := map_zero _
  smul := extension_smul q dense d
  commute := by
    intro x
    apply dense.induction_on
      (p := fun x => P (extension q d x) = extension q d (P x)) x
      (isClosed_eq (P.continuous.comp (extension q d).continuous)
        ((extension q d).continuous.comp P.continuous))
    intro c
    rw [extension_core q dense, hP, hP, haction,
      extension_realize q dense d qReg denseReg realize hrealize J hJ]

end ConditionedStochasticStabilityHyperbolic.CoreConjugation
