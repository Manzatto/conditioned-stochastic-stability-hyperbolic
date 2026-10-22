module
public import LeanShared.Dynamics.HyperbolicBackwardGraph
public import LeanShared.Analysis.ContractionObservableContinuity

/-! Coordinatewise continuity of the constructed nonlinear backward graph.
The coefficients need only depend continuously on the parameter at each time.
Uniform convergence of finite Lyapunov--Perron iterates proves the result, so
product-topology noise paths do not need to vary continuously in sup norm. -/
public noncomputable section
namespace LeanShared.HyperbolicBackwardGraph
open Filter
open scoped Topology NNReal BoundedContinuousFunction

theorem continuous_iterate_coordinate {P U S : Type*} [TopologicalSpace P]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S]
    (d : P → Data U S)
    (inverse : ∀ n, Continuous (fun z : P × U => ((d z.1).expanding n).symm z.2))
    (stable : ∀ n, Continuous (fun z : P × S => (d z.1).contracting n z.2))
    (nonlinear : ∀ n, Continuous (fun z : P × (U × S) => (d z.1).nonlinear n z.2))
    (u : U) (m n : ℕ) :
    Continuous (fun p => (((d p).transform u)^[m] 0) n) := by
  induction m generalizing n with
  | zero => exact continuous_const
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    cases n with
    | zero =>
      change Continuous (fun p => (u,
        (d p).contracting 0 ((((d p).transform u)^[m] 0) 1).2 +
          ((d p).nonlinear 0 ((((d p).transform u)^[m] 0) 1)).2))
      exact continuous_const.prodMk
        (((stable 0).comp (continuous_id.prodMk (ih 1).snd)).add
          (((nonlinear 0).comp (continuous_id.prodMk (ih 1))).snd))
    | succ n =>
      change Continuous (fun p =>
        (((d p).expanding n).symm
          (((((d p).transform u)^[m] 0) n).1 -
            ((d p).nonlinear n ((((d p).transform u)^[m] 0) (n + 1))).1),
          (d p).contracting (n + 1) ((((d p).transform u)^[m] 0) (n + 2)).2 +
            ((d p).nonlinear (n + 1) ((((d p).transform u)^[m] 0) (n + 2))).2))
      exact ((inverse n).comp (continuous_id.prodMk
        ((ih n).fst.sub (((nonlinear n).comp (continuous_id.prodMk (ih (n + 1)))).fst)))).prodMk
        (((stable (n + 1)).comp (continuous_id.prodMk (ih (n + 2)).snd)).add
          (((nonlinear (n + 1)).comp (continuous_id.prodMk (ih (n + 2)))).snd))

theorem continuous_orbit_coordinate {P U S : Type*} [TopologicalSpace P]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : P → Data U S) (K : ℝ≥0) (small : K < 1)
    (uniform : ∀ p, (d p).k + (d p).δ ≤ K)
    (C : ℝ) (bounded : ∀ p, (d p).zero_bound ≤ C)
    (inverse : ∀ n, Continuous (fun z : P × U => ((d z.1).expanding n).symm z.2))
    (stable : ∀ n, Continuous (fun z : P × S => (d z.1).contracting n z.2))
    (nonlinear : ∀ n, Continuous (fun z : P × (U × S) => (d z.1).nonlinear n z.2))
    (u : U) (n : ℕ) : Continuous (fun p => (d p).orbit u n) := by
  let T : P → (ℕ →ᵇ U × S) → (ℕ →ᵇ U × S) := fun p => (d p).transform u
  have contract (p : P) : ContractingWith K (T p) :=
    ⟨small, ((d p).transform_contracting u).2.weaken (uniform p)⟩
  let M : ℝ := max ‖u‖ (((K : ℝ) + 1) * C)
  have displacement (p : P) : dist 0 (T p 0) ≤ M := by
    rw [dist_zero_left]
    apply (BoundedContinuousFunction.norm_le ((norm_nonneg u).trans (le_max_left _ _))).mpr
    intro i
    have zeroBound (j : ℕ) : ‖(d p).nonlinear j 0‖ ≤ C :=
      ((d p).nonlinear_zero j).trans (bounded p)
    have estimate := HyperbolicBackwardTransform.raw_zero_bound
      (fun j => ((d p).expanding j).symm) (fun j => (d p).contracting j)
      (d p).nonlinear (d p).k (d p).inverse_bound
      (fun j => ((d p).expanding j).symm.map_zero)
      (fun j => ((d p).contracting j).map_zero) C zeroBound u i
    apply estimate.trans
    apply max_le_max le_rfl
    have hC : 0 ≤ C := (norm_nonneg _).trans (zeroBound 0)
    have hk : (d p).k ≤ K := (le_add_of_nonneg_right
      (show (0 : ℝ≥0) ≤ (d p).δ from zero_le)).trans (uniform p)
    exact mul_le_mul_of_nonneg_right (add_le_add (show ((d p).k : ℝ) ≤ K from hk) (show (1 : ℝ) ≤ 1 from le_rfl)) hC
  have result := ParameterizedContraction.continuous_observation T K small contract
    0 M displacement (fun z : ℕ →ᵇ U × S => z n)
    (BoundedContinuousFunction.lipschitz_eval_const n)
    (fun m => continuous_iterate_coordinate d inverse stable nonlinear u m n)
  have point_eq (p : P) : ParameterizedContraction.point T K contract p = (d p).orbit u :=
    ((d p).transform_contracting u).fixedPoint_unique
      (ParameterizedContraction.point_fixed T K contract p)
  simpa only [point_eq] using result

theorem continuous_graph {P U S : Type*} [TopologicalSpace P]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : P → Data U S) (K : ℝ≥0) (small : K < 1)
    (uniform : ∀ p, (d p).k + (d p).δ ≤ K)
    (C : ℝ) (bounded : ∀ p, (d p).zero_bound ≤ C)
    (inverse : ∀ n, Continuous (fun z : P × U => ((d z.1).expanding n).symm z.2))
    (stable : ∀ n, Continuous (fun z : P × S => (d z.1).contracting n z.2))
    (nonlinear : ∀ n, Continuous (fun z : P × (U × S) => (d z.1).nonlinear n z.2))
    (u : U) : Continuous (fun p => (d p).graph u) :=
  (continuous_orbit_coordinate d K small uniform C bounded inverse stable nonlinear u 0).snd

end LeanShared.HyperbolicBackwardGraph
