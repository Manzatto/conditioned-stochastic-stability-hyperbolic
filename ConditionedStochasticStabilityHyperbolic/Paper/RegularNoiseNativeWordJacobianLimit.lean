module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualWordJets
public import LeanShared.Dynamics.HyperbolicNativeJacobianCoordinateJets
import all LeanShared.Analysis.FiniteJetComposition

/-! Literal Whitney convergence of finite noisy words implies convergence
of their actual native unstable determinants at moving points. No joint
continuity in noise scale and no Jacobian limit source are assumed. -/
@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff NNReal
open LeanShared LeanShared.FiniteJetComposition HyperbolicBasicSet
variable {E M ι A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {r : ℝ} {Λ : Set M}

theorem Maps.moving_word_nativeJacobian_tendsto
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ i, cube (ι := ι) (ε i)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ i in l, 0 < ε i)
    (chart : ℕ → Fin F.atlas.count) (N : ℕ) (y₀ : E)
    (inside : y₀ ∈ F.atlas.actualWordDomain chart N)
    (collar : (F.atlas.source (chart 0)).symm y₀ ∈ a.collar)
    (y : A → E) (moving : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i =>
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E))
        (word (fun n => F.family (ε i) (controls n i).val) N)
        ((F.atlas.source (chart 0)).symm (y i))).toLinearMap.domRestrict
          (a.unstable ((F.atlas.source (chart 0)).symm (y i)))).normDet) l
      (𝓝 ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[N])
        ((F.atlas.source (chart 0)).symm y₀)).toLinearMap.domRestrict
          (a.unstable ((F.atlas.source (chart 0)).symm y₀))).normDet) := by
  let c := F.atlas.source (chart 0)
  let d := F.atlas.source (chart N)
  let noisy (i : A) := word (fun n => F.family (ε i) (controls n i).val) N
  let x₀ := c.symm y₀
  have source₀ : x₀ ∈ c.source := c.map_target inside.2.1
  have target₀ : (T : M → M)^[N] x₀ ∈ d.source := inside.2.2 N le_rfl
  have sourceNear : ∀ᶠ i in l, y i ∈ c.target :=
    moving.eventually (c.open_target.mem_nhds inside.2.1)
  have inputLimit : Tendsto (fun i => c.symm (y i)) l (𝓝 x₀) :=
    (c.continuousAt_symm inside.2.1).tendsto.comp moving
  have outputLimit := F.moving_word_tendsto ε controls l limit positive _ _ inputLimit N
  have targetNear : ∀ᶠ i in l, noisy i (c.symm (y i)) ∈ d.source :=
    outputLimit.eventually (d.open_source.mem_nhds target₀)
  have window : ∀ᶠ i in l, ε i ≤ F.window :=
    (limit.eventually (gt_mem_nhds F.window_positive)).mono (fun _ hi => hi.le)
  have noisySmooth (i : A) (hi : 0 < ε i) (hw : ε i ≤ F.window) :
      MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) (noisy i) := by
    have each (n : ℕ) : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E))
        (F.family (ε i) (controls n i).val) :=
      (F.map_regular (ε i) hi hw (controls n i)).mdifferentiable regularity
    have allN (k : ℕ) : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E))
        (word (fun n => F.family (ε i) (controls n i).val) k) := by
      induction k with
      | zero => exact mdifferentiable_id
      | succ n ih => exact (each n).comp ih
    exact allN N
  have valid : ∀ᶠ i in l, c.symm (y i) ∈ c.source ∧ noisy i (c.symm (y i)) ∈ d.source ∧
      MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) (noisy i) (c.symm (y i)) := by
    filter_upwards [sourceNear,targetNear,positive,window] with i hs ht hp hw
    exact ⟨c.map_target hs,ht,noisySmooth i hp hw _⟩
  have jets := ((F.actual_word_jetConvergesOn regularity deterministic ε controls l limit positive
    chart N) y₀ inside).2 y moving
  have jetLimit := moving.prodMk_nhds (jets.1.prodMk_nhds jets.2.1)
  have actualJets : Tendsto (fun i =>
      (c (c.symm (y i)),d (noisy i (c.symm (y i))),
        fderiv ℝ (d ∘ noisy i ∘ c.symm) (c (c.symm (y i))))) l
      (𝓝 (c x₀,d ((T : M → M)^[N] x₀),
        fderiv ℝ (d ∘ (T : M → M)^[N] ∘ c.symm) (c x₀))) := by
    dsimp only [x₀]
    simp only [c.right_inv inside.2.1]
    apply jetLimit.congr'
    filter_upwards [sourceNear] with i hi
    simp only [c.right_inv hi]
    rfl
  exact a.tendsto_nativeJacobian_of_coordinateJets c d
    (F.atlas.source_smooth (chart 0)) (F.atlas.source_smooth (chart N))
    noisy (fun i => c.symm (y i)) ((T : M → M)^[N]) x₀ source₀ target₀ collar
    ((deterministic.iterate N).mdifferentiable one_ne_zero x₀) valid actualJets

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
