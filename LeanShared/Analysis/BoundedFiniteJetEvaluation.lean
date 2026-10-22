module
public import LeanShared.Analysis.BoundedFiniteJetSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Genuine derivative evaluations on the complete finite jet graph are
bounded linear maps. Consequently Bochner regularization in the graph
commutes with every retained actual frequency derivative. -/
public noncomputable section
open scoped ContDiff
namespace LeanShared.BoundedFiniteJetSpace
universe u
variable {E:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative_le : ∀n:ℕ,∀{F:Type u},∀[NormedAddCommGroup F],∀[NormedSpace ℝ F],
    ∀[NormedSpace ℂ F],∀[IsScalarTower ℝ ℂ F],∀[SMulCommClass ℝ ℂ F],∀[CompleteSpace F],
    ∀v:(construct (E:=E) n (F:=F)).carrier,∀j≤n,∀x,
      ‖iteratedFDeriv ℝ j ((construct n (F:=F)).physical v) x‖≤‖v‖:=by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ _ _ _ v j hj x
    have :j=0:=by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    exact v.norm_coe_le_norm x
  | succ n ih =>
    intro F _ _ _ _ _ _ v j hj x
    let d:=construct (E:=E) n (F:=E→L[ℝ]F)
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (v.val.1.norm_coe_le_norm x).trans (norm_fst_le v.val)
    | succ j =>
      have derivative:fderiv ℝ (BoundedDerivativeGraph.physical d.physical v)=d.physical v.val.2:=by
        funext y
        exact (BoundedDerivativeGraph.derivative d.physical v y).fderiv
      rw [←norm_iteratedFDeriv_fderiv]
      change ‖iteratedFDeriv ℝ j (fderiv ℝ (BoundedDerivativeGraph.physical d.physical v)) x‖≤‖v‖
      rw [derivative]
      exact (ih v.val.2 j (by omega) x).trans (norm_snd_le v.val)

variable {F:Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]

@[expose] def evaluation (n j:ℕ) (hj:j≤n) (x:E):
    (construct (E:=E) n (F:=F)).carrier→L[ℂ]
      ContinuousMultilinearMap ℝ (fun _ : Fin j=>E) F:=
  LinearMap.mkContinuous
    { toFun:=fun v=>iteratedFDeriv ℝ j ((construct n (F:=F)).physical v) x
      map_add':=by
        intro v w
        have identity:((construct n (F:=F)).physical (v+w):E→F)=
            ((construct n (F:=F)).physical v)+((construct n (F:=F)).physical w):=by
          ext y
          simp only [map_add,BoundedContinuousFunction.add_apply,Pi.add_apply]
        rw [identity]
        exact iteratedFDeriv_add_apply
          (((construct n (F:=F)).regular v).of_le (by exact_mod_cast hj)).contDiffAt
          (((construct n (F:=F)).regular w).of_le (by exact_mod_cast hj)).contDiffAt
      map_smul':=by
        intro c v
        have identity:((construct n (F:=F)).physical (c • v):E→F)=
            c • ((construct n (F:=F)).physical v):=by
          ext y
          simp only [map_smul,BoundedContinuousFunction.smul_apply,Pi.smul_apply]
        rw [identity]
        exact iteratedFDeriv_const_smul_apply
          (((construct n (F:=F)).regular v).of_le (by exact_mod_cast hj)).contDiffAt }
    1 (fun v=>by
      change ‖iteratedFDeriv ℝ j ((construct n (F:=F)).physical v) x‖≤1*‖v‖
      rw [one_mul]
      exact derivative_le n v j hj x)
end LeanShared.BoundedFiniteJetSpace
