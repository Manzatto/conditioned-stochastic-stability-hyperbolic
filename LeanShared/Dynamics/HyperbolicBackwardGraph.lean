module
public import LeanShared.Dynamics.HyperbolicBackwardTransform

/-! Actual global unstable graphs for uniformly small nonautonomous nonlinear
perturbations of hyperbolic split maps. The graph and its bounded backward
orbits are constructed by the preceding Lyapunov--Perron contraction. The exact
bounded-orbit characterization is proved, not included among source fields.
This global-coordinate theorem is a primitive for a local random stable-manifold
theorem; a chart/cutoff reduction and noise-path dependence are separate steps. -/
public noncomputable section
namespace LeanShared.HyperbolicBackwardGraph
open scoped NNReal BoundedContinuousFunction

structure Data (U S : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] where
  expanding : ℕ → U ≃L[ℝ] U
  contracting : ℕ → S →L[ℝ] S
  nonlinear : ℕ → U × S → U × S
  k : ℝ≥0
  δ : ℝ≥0
  small : k + δ < 1
  inverse_bound : ∀ n, LipschitzWith k (expanding n).symm
  stable_bound : ∀ n, LipschitzWith k (contracting n)
  nonlinear_bound : ∀ n, LipschitzWith δ (nonlinear n)
  zero_bound : ℝ
  nonlinear_zero : ∀ n, ‖nonlinear n 0‖ ≤ zero_bound

namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem k_le_one (d : Data U S) : d.k ≤ 1 :=
  (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ d.δ from zero_le)).trans d.small.le

@[expose] def transform (d : Data U S) (u : U) : (ℕ →ᵇ U × S) → (ℕ →ᵇ U × S) :=
  HyperbolicBackwardTransform.transform (fun n => (d.expanding n).symm)
    (fun n => d.contracting n) d.nonlinear d.k d.δ d.k_le_one d.inverse_bound d.stable_bound
    d.nonlinear_bound (fun n => (d.expanding n).symm.map_zero)
    (fun n => (d.contracting n).map_zero) d.zero_bound d.nonlinear_zero u

theorem transform_contracting (d : Data U S) (u : U) :
    ContractingWith (d.k + d.δ) (d.transform u) :=
  ⟨d.small, HyperbolicBackwardTransform.transform_lipschitz _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

@[expose] def orbit [CompleteSpace U] [CompleteSpace S] (d : Data U S) (u : U) : ℕ →ᵇ U × S :=
  (d.transform_contracting u).fixedPoint (d.transform u)

theorem orbit_raw [CompleteSpace U] [CompleteSpace S] (d : Data U S) (u : U) (n : ℕ) :
    HyperbolicBackwardTransform.raw (fun n => (d.expanding n).symm)
      (fun n => d.contracting n) d.nonlinear u (d.orbit u) n = d.orbit u n := by
  exact congrArg (fun z : ℕ →ᵇ U × S => z n) (d.transform_contracting u).fixedPoint_isFixedPt

@[expose] def graph [CompleteSpace U] [CompleteSpace S] (d : Data U S) (u : U) : S :=
  (d.orbit u 0).2

theorem orbit_initial [CompleteSpace U] [CompleteSpace S] (d : Data U S) (u : U) :
    d.orbit u 0 = (u, d.graph u) := by
  refine Prod.ext ?_ rfl
  exact (congrArg Prod.fst (d.orbit_raw u 0)).symm

@[expose] def forward (d : Data U S) (n : ℕ) (z : U × S) : U × S :=
  ((d.expanding n) z.1 + (d.nonlinear n z).1,
    (d.contracting n) z.2 + (d.nonlinear n z).2)

theorem orbit_step [CompleteSpace U] [CompleteSpace S] (d : Data U S) (u : U) (n : ℕ) :
    d.forward n (d.orbit u (n + 1)) = d.orbit u n := by
  have unstable := congrArg (d.expanding n) (congrArg Prod.fst (d.orbit_raw u (n + 1)))
  have stable := congrArg Prod.snd (d.orbit_raw u n)
  apply Prod.ext
  · change (d.expanding n) (d.orbit u (n + 1)).1 +
      (d.nonlinear n (d.orbit u (n + 1))).1 = (d.orbit u n).1
    change (d.expanding n) ((d.expanding n).symm _) = _ at unstable
    rw [(d.expanding n).apply_symm_apply] at unstable
    rw [← unstable, sub_add_cancel]
  · cases n <;> exact stable

theorem orbit_unique [CompleteSpace U] [CompleteSpace S] (d : Data U S) (u : U)
    (z : ℕ →ᵇ U × S) (initial : (z 0).1 = u)
    (step : ∀ n, d.forward n (z (n + 1)) = z n) : z = d.orbit u := by
  apply (d.transform_contracting u).fixedPoint_unique
  apply BoundedContinuousFunction.ext
  intro n
  cases n with
  | zero =>
    change (u, d.contracting 0 (z 1).2 + (d.nonlinear 0 (z 1)).2) = z 0
    have stable := congrArg Prod.snd (step 0)
    exact Prod.ext initial.symm stable
  | succ n =>
    change ((d.expanding n).symm ((z n).1 - (d.nonlinear n (z (n + 1))).1),
      d.contracting (n + 1) (z (n + 2)).2 + (d.nonlinear (n + 1) (z (n + 2))).2) = _
    apply Prod.ext
    · have unstable := congrArg Prod.fst (step n)
      change (d.expanding n) (z (n + 1)).1 +
        (d.nonlinear n (z (n + 1))).1 = (z n).1 at unstable
      have rearranged := congrArg (d.expanding n).symm (eq_sub_of_add_eq unstable)
      simpa only [(d.expanding n).symm_apply_apply] using rearranged.symm
    · have stable := congrArg Prod.snd (step (n + 1))
      exact stable

theorem graph_iff_bounded_backward [CompleteSpace U] [CompleteSpace S] (d : Data U S)
    (z : U × S) : z.2 = d.graph z.1 ↔
      ∃ b : ℕ →ᵇ U × S, b 0 = z ∧ ∀ n, d.forward n (b (n + 1)) = b n := by
  constructor
  · intro member
    refine ⟨d.orbit z.1, ?_, d.orbit_step z.1⟩
    rw [d.orbit_initial]
    exact Prod.ext rfl member.symm
  · rintro ⟨b, initial, step⟩
    have unique := d.orbit_unique z.1 b (by rw [initial]) step
    rw [unique, d.orbit_initial] at initial
    exact (congrArg Prod.snd initial).symm

end Data
end LeanShared.HyperbolicBackwardGraph
