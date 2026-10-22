module

public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Tactic.Linarith

/-! A small perturbation of a hyperbolic diagonal block acts on every
bounded unstable graph with a uniformly small unstable error and stable
component. These are estimates for the actual block, not invariant planes
supplied separately. -/
public noncomputable section
namespace LeanShared.GraphBlockPerturbation
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

@[expose] def graph (G : U →L[ℝ] S) : U →L[ℝ] U × S :=
  (ContinuousLinearMap.id ℝ U).prod G

@[expose] def upper (L : U × S →L[ℝ] U × S) (G : U →L[ℝ] S) : U →L[ℝ] U :=
  (ContinuousLinearMap.fst ℝ U S).comp (L.comp (graph G))

@[expose] def lower (L : U × S →L[ℝ] U × S) (G : U →L[ℝ] S) : U →L[ℝ] S :=
  (ContinuousLinearMap.snd ℝ U S).comp (L.comp (graph G))

theorem graph_norm_le (G : U →L[ℝ] S) (bound : ‖G‖ ≤ 1) : ‖graph G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change max ‖v‖ ‖G v‖ ≤ 1 * ‖v‖
  rw [one_mul]
  exact max_le le_rfl ((G.le_opNorm v).trans (by nlinarith [norm_nonneg v]))

theorem upper_error (A : U →L[ℝ] U) (B : S →L[ℝ] S)
    (L : U × S →L[ℝ] U × S) (G : U →L[ℝ] S)
    (hG : ‖G‖ ≤ 1) (η : ℝ) (close : ‖L - A.prodMap B‖ ≤ η) :
    ‖upper L G - A‖ ≤ η := by
  have nonnegative : 0 ≤ η := (norm_nonneg _).trans close
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro v
  have point := (L - A.prodMap B).le_opNorm (graph G v)
  have projected := norm_fst_le ((L - A.prodMap B) (graph G v))
  have graphBound := (graph G).le_opNorm v
  have graphBound' : ‖graph G v‖ ≤ ‖v‖ := graphBound.trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (graph_norm_le G hG) (norm_nonneg v))
  change ‖(L (v, G v)).1 - A v‖ ≤ η * ‖v‖
  calc
    _ ≤ ‖(L - A.prodMap B) (graph G v)‖ := projected
    _ ≤ η * ‖graph G v‖ := point.trans (mul_le_mul_of_nonneg_right close (norm_nonneg _))
    _ ≤ _ := mul_le_mul_of_nonneg_left graphBound' nonnegative

end LeanShared.GraphBlockPerturbation
