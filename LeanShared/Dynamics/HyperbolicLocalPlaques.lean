module
public import LeanShared.Dynamics.HyperbolicBackwardGraphContinuity
public import LeanShared.Dynamics.HyperbolicBackwardGraphBounds

/-! Local random unstable plaques constructed from the actual hyperbolic
Lyapunov--Perron graphs. Lower semicontinuity, complete backward orbits in the
open local collar, and the local backward-orbit characterization are all
conclusions. Only ordinary split-map Lipschitz bounds, coefficient continuity,
and an explicit small-forcing margin enter the construction. -/
public noncomputable section
namespace LeanShared.HyperbolicBackwardGraph
open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

@[expose] def plaque {U S : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : Data U S) (R : ℝ) : Set (U × S) :=
  {z | ‖z.1‖ < R ∧ z.2 = d.graph z.1}

theorem plaque_backward {U S : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : Data U S) (R : ℝ)
    (forcing : ((d.k : ℝ) + 1) * d.zero_bound <
      (1 - (d.k + d.δ : ℝ≥0)) * R) (z : U × S) (member : z ∈ plaque d R) :
    ∃ b : ℕ → U × S, b 0 = z ∧ (∀ n, ‖b n‖ < R) ∧
      ∀ n, d.forward n (b (n + 1)) = b n := by
  refine ⟨d.orbit z.1, ?_, ?_, d.orbit_step z.1⟩
  · rw [d.orbit_initial]
    exact Prod.ext rfl member.2.symm
  · intro n
    exact ((d.orbit z.1).norm_coe_le_norm n).trans_lt
      (d.orbit_norm_lt z.1 R member.1 forcing)

theorem plaque_local_backward {U S : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : Data U S) (R : ℝ) (b : ℕ → U × S) (inside : ∀ n, ‖b n‖ < R)
    (step : ∀ n, d.forward n (b (n + 1)) = b n) : b 0 ∈ plaque d R := by
  refine ⟨(norm_fst_le (b 0)).trans_lt (inside 0), ?_⟩
  apply (d.graph_iff_bounded_backward (b 0)).mpr
  let bounded : ℕ →ᵇ U × S := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    b R (fun n => (inside n).le)
  exact ⟨bounded, rfl, step⟩

theorem plaque_lower {P U S : Type*} [TopologicalSpace P]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : P → Data U S) (K : ℝ≥0) (small : K < 1)
    (uniform : ∀ p, (d p).k + (d p).δ ≤ K)
    (C : ℝ) (bounded : ∀ p, (d p).zero_bound ≤ C)
    (inverse : ∀ n, Continuous (fun z : P × U => ((d z.1).expanding n).symm z.2))
    (stable : ∀ n, Continuous (fun z : P × S => (d z.1).contracting n z.2))
    (nonlinear : ∀ n, Continuous (fun z : P × (U × S) => (d z.1).nonlinear n z.2))
    (R : ℝ) (p : P) (paths : ℕ → P) (converges : Tendsto paths atTop (𝓝 p))
    (z : U × S) (member : z ∈ plaque (d p) R) :
    ∃ zn : ℕ → U × S, Tendsto zn atTop (𝓝 z) ∧ ∀ n, zn n ∈ plaque (d (paths n)) R := by
  refine ⟨fun n => (z.1, (d (paths n)).graph z.1), ?_, fun _ => ⟨member.1, rfl⟩⟩
  have continuous := continuous_graph d K small uniform C bounded inverse stable nonlinear z.1
  have limit := (tendsto_const_nhds : Tendsto (fun _ : ℕ => z.1) atTop (𝓝 z.1)).prodMk_nhds (continuous.continuousAt.tendsto.comp converges)
  simpa only [← member.2, Prod.eta, Function.comp_def] using limit

end LeanShared.HyperbolicBackwardGraph
