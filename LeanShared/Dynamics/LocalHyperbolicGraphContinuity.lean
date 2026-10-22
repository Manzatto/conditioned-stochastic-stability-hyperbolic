module
public import LeanShared.Dynamics.LocalHyperbolicGraph

/-! Lower semicontinuity of local unstable plaques constructed from literal
local nonlinear maps. The extensions used by the fixed point argument are
constructed by radial retraction, so their joint continuity follows from the
original maps on the local ball rather than being an extra source premise. -/
public noncomputable section
namespace LeanShared.LocalHyperbolicGraph
open Set Filter
open scoped Topology NNReal

theorem continuous_extension_nonlinear {P U S : Type*} [TopologicalSpace P]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S]
    (d : P → Data U S) (R : ℝ) (positive : 0 < R) (radius : ∀ p, (d p).radius = R)
    (expanding : ∀ n, Continuous (fun z : P × U => (d z.1).expanding n z.2))
    (stable : ∀ n, Continuous (fun z : P × S => (d z.1).contracting n z.2))
    (maps : ∀ n, ContinuousOn (fun z : P × (U × S) => (d z.1).map n z.2)
      (univ ×ˢ Metric.closedBall 0 R)) (n : ℕ) :
    Continuous (fun z : P × (U × S) => (d z.1).extension.nonlinear n z.2) := by
  have block : Continuous (fun z : P × (U × S) => (d z.1).block n z.2) :=
    ((expanding n).comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      ((stable n).comp (continuous_fst.prodMk continuous_snd.snd))
  have remainder : ContinuousOn (fun z : P × (U × S) => (d z.1).remainder n z.2)
      (univ ×ˢ Metric.closedBall 0 R) := (maps n).sub block.continuousOn
  have result := RadialBallRetraction.continuous_extend_family R positive
    (fun z : P × (U × S) => (d z.1).remainder n z.2) remainder
  simpa only [Data.extension, radius] using result

theorem plaque_lower {P U S : Type*} [TopologicalSpace P]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : P → Data U S) (R : ℝ) (positive : 0 < R) (radius : ∀ p, (d p).radius = R)
    (K : ℝ≥0) (small : K < 1) (uniform : ∀ p, (d p).k + (d p).δ * 2 ≤ K)
    (C : ℝ) (bounded : ∀ p, (d p).zero_bound ≤ C)
    (expanding : ∀ n, Continuous (fun z : P × U => (d z.1).expanding n z.2))
    (inverse : ∀ n, Continuous (fun z : P × U => ((d z.1).expanding n).symm z.2))
    (stable : ∀ n, Continuous (fun z : P × S => (d z.1).contracting n z.2))
    (maps : ∀ n, ContinuousOn (fun z : P × (U × S) => (d z.1).map n z.2)
      (univ ×ˢ Metric.closedBall 0 R))
    (p : P) (paths : ℕ → P) (converges : Tendsto paths atTop (𝓝 p))
    (z : U × S) (member : z ∈ (d p).plaque) :
    ∃ zn : ℕ → U × S, Tendsto zn atTop (𝓝 z) ∧ ∀ n, zn n ∈ (d (paths n)).plaque := by
  have graphMember : z ∈ HyperbolicBackwardGraph.plaque (d p).extension R := by
    simpa only [Data.plaque, radius] using member
  obtain ⟨zn, limit, belongs⟩ := HyperbolicBackwardGraph.plaque_lower
    (fun p => (d p).extension) K small uniform C bounded inverse stable
    (continuous_extension_nonlinear d R positive radius expanding stable maps)
    R p paths converges z graphMember
  refine ⟨zn, limit, fun n => ?_⟩
  simpa only [Data.plaque, radius] using belongs n

end LeanShared.LocalHyperbolicGraph
