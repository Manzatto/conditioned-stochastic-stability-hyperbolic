module
public import LeanShared.Geometry.HigherDerivativeHolderSpace
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! The actual iterated derivatives of the constructed Banach graphs satisfy
the defining uniform Holder bounds with the graph norm itself. -/
public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.HigherDerivativeHolderSpace
universe u
variable {E:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F:Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] [CompleteSpace F]

omit [IsScalarTower ℝ ℂ F] [SMulCommClass ℝ ℂ F] in
theorem base_increment {a:ℝ} (ha:0<a) (ha1:a<1)
    (v:(base (E:=E) (F:=F) ha ha1).carrier) (x y:E) :
    ‖iteratedFDeriv ℝ 0 ((base ha ha1).physical v) x-
      iteratedFDeriv ℝ 0 ((base ha ha1).physical v) y‖≤‖v‖*‖x-y‖^a := by
  rw [iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map]
  change ‖BanachValuedHolderGraph.physical E F a v x-
    BanachValuedHolderGraph.physical E F a v y‖≤_
  convert! BanachValuedHolderGraph.increment_bound E F a v x y using 1
  rw [dist_eq_norm]
  rfl

omit [IsScalarTower ℝ ℂ F] in
theorem successor_increment {a r:ℝ} (n:ℕ) (d:Model E (E→L[ℝ]F) r)
    (previous:∀v:d.carrier,∀x y:E,
      ‖iteratedFDeriv ℝ n (d.physical v) x-iteratedFDeriv ℝ n (d.physical v) y‖≤‖v‖*‖x-y‖^a)
    (v:(successor d).carrier) (x y:E) :
    ‖iteratedFDeriv ℝ (n+1) ((successor d).physical v) x-
      iteratedFDeriv ℝ (n+1) ((successor d).physical v) y‖≤‖v‖*‖x-y‖^a := by
  change ‖iteratedFDeriv ℝ (n+1) (BoundedDerivativeGraph.physical d.physical v) x-
    iteratedFDeriv ℝ (n+1) (BoundedDerivativeGraph.physical d.physical v) y‖≤_
  have derivative:fderiv ℝ (BoundedDerivativeGraph.physical d.physical v)=d.physical v.val.2 := by
    funext z
    exact (BoundedDerivativeGraph.derivative d.physical v z).fderiv
  rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [←dist_eq_norm,LinearIsometryEquiv.dist_map,dist_eq_norm,derivative]
  exact (previous v.val.2 x y).trans
    (mul_le_mul_of_nonneg_right (norm_snd_le v.val) (Real.rpow_nonneg (norm_nonneg _) _))
end LeanShared.HigherDerivativeHolderSpace
