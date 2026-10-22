module
public import LeanShared.Geometry.HigherHolderDerivativeBounds
public import LeanShared.Geometry.HigherDerivativeHolderRegular

/-! Uniform bounds on the genuine top derivative of every recursively
constructed higher Holder graph, directly in its Banach graph norm. -/
public noncomputable section
namespace LeanShared.HigherDerivativeHolderSpace
universe u
variable {E:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem constructed_increment {a:ℝ} (ha:0<a) (ha1:a<1) :
    ∀n:ℕ,∀{F:Type u},∀[NormedAddCommGroup F],∀[NormedSpace ℝ F],∀[NormedSpace ℂ F],
      ∀[IsScalarTower ℝ ℂ F],∀[SMulCommClass ℝ ℂ F],∀[CompleteSpace F],
      ∀v:(construct (E:=E) ha ha1 n (F:=F)).carrier,∀x y:E,
        ‖iteratedFDeriv ℝ n ((construct ha ha1 n (F:=F)).physical v) x-
          iteratedFDeriv ℝ n ((construct ha ha1 n (F:=F)).physical v) y‖≤‖v‖*‖x-y‖^a := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ _ _ _ v x y
    exact base_increment ha ha1 v x y
  | succ n ih =>
    intro F _ _ _ _ _ _ v x y
    exact successor_increment n (construct ha ha1 n (F:=E→L[ℝ]F)) ih v x y

variable [FiniteDimensional ℝ E]
theorem constructed_full_increment {a:ℝ} (ha:0<a) (ha1:a<1) :
    ∀n:ℕ,∀{F:Type u},∀[NormedAddCommGroup F],∀[NormedSpace ℝ F],∀[NormedSpace ℂ F],
      ∀[IsScalarTower ℝ ℂ F],∀[SMulCommClass ℝ ℂ F],∀[CompleteSpace F],
      ∀v:(constructFull (E:=E) ha ha1 n (F:=F)).carrier,∀x y:E,
        ‖iteratedFDeriv ℝ n ((constructFull ha ha1 n (F:=F)).physical v) x-
          iteratedFDeriv ℝ n ((constructFull ha ha1 n (F:=F)).physical v) y‖≤‖v‖*‖x-y‖^a := by
  intro n
  induction n with
  | zero =>
    intro F _ _ _ _ _ _ v x y
    exact base_increment ha ha1 v x y
  | succ n ih =>
    intro F _ _ _ _ _ _ v x y
    exact successor_increment n (constructFull ha ha1 n (F:=E→L[ℝ]F)).toModel ih v x y
end LeanShared.HigherDerivativeHolderSpace
