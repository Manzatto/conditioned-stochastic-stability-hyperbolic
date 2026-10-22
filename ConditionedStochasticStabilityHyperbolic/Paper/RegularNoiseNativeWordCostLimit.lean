module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseNativeWordJacobianLimit
public import LeanShared.Dynamics.HyperbolicExtendedNativeJacobianContinuity
public import LeanShared.Geometry.FiniteCaptureWordCutoffs
public import LeanShared.Geometry.DiffeomorphismIterates

/-! The literal localized finite-word cost has its deterministic moving-point
limit, uniformly over arbitrary driving controls. -/
@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff NNReal BigOperators
open LeanShared LeanShared.FiniteJetComposition HyperbolicBasicSet FiniteSmoothCapturePartition
variable {E M ι I A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {v : I → Set M}

def nativeWordCost {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) (g : M → ℝ) (maps : ℕ → M → M)
    (N : ℕ) (labels : Fin (N+1) → I) (x : M) : ℝ :=
  wordCutoff d (fun j => word maps j.val x) labels *
    |∏ j ∈ Finset.range N, g (word maps j x)| /
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (word maps N) x).toLinearMap.domRestrict
        (a.unstable x)).normDet

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem nativeWordCost_deterministic_eq
    {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) (g : M → ℝ)
    (N : ℕ) (labels : Fin (N+1) → I) (x : M) :
    nativeWordCost a d g (fun _ => T) N labels x =
      wordCutoff d (fun j => (T : M → M)^[j.val] x) labels *
        |∏ j ∈ Finset.range N, g ((T : M → M)^[j] x)| /
          ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[N]) x).toLinearMap.domRestrict
            (a.unstable x)).normDet := by
  have constantWord (n : ℕ) : word (fun _ => (T : M → M)) n = (T : M → M)^[n] := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [word,ih,Function.iterate_succ']
  have determinantWord := congrArg (fun f : M → M =>
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (a.unstable x)).normDet)
      (constantWord N)
  unfold nativeWordCost
  rw [determinantWord]
  simp only [constantWord]

theorem Maps.moving_word_nativeCost_tendsto
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (N : ℕ) (labels : Fin (N+1) → I)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ i, cube (ι := ι) (ε i)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ i in l, 0 < ε i)
    (chart : ℕ → Fin F.atlas.count) (y₀ : E)
    (inside : y₀ ∈ F.atlas.actualWordDomain chart N)
    (collar : (F.atlas.source (chart 0)).symm y₀ ∈ a.collar)
    (y : A → E) (moving : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i => nativeWordCost a d g
      (fun n => F.family (ε i) (controls n i).val) N labels
      ((F.atlas.source (chart 0)).symm (y i))) l
      (𝓝 (nativeWordCost a d g (fun _ => T) N labels
        ((F.atlas.source (chart 0)).symm y₀))) := by
  let c := F.atlas.source (chart 0)
  let x₀ := c.symm y₀
  have inputLimit : Tendsto (fun i => c.symm (y i)) l (𝓝 x₀) :=
    (c.continuousAt_symm inside.2.1).tendsto.comp moving
  have prefixes (j : ℕ) := F.moving_word_tendsto ε controls l limit positive _ _ inputLimit j
  have cutoff : Tendsto (fun i => wordCutoff d
      (fun j : Fin (N+1) => word (fun n => F.family (ε i) (controls n i).val) j.val
        (c.symm (y i))) labels) l
      (𝓝 (wordCutoff d (fun j : Fin (N+1) => (T : M → M)^[j.val] x₀) labels)) := by
    exact tendsto_finsetProd _ (fun j _ =>
      ((d.smooth (labels j)).continuous.tendsto _).comp (prefixes j.val))
  have weights : Tendsto (fun i => ∏ j ∈ Finset.range N,
      g (word (fun n => F.family (ε i) (controls n i).val) j (c.symm (y i)))) l
      (𝓝 (∏ j ∈ Finset.range N, g ((T : M → M)^[j] x₀))) :=
    tendsto_finsetProd _ (fun j _ => (weight.tendsto _).comp (prefixes j))
  have jacobian := F.moving_word_nativeJacobian_tendsto regularity deterministic a ε
    controls l limit positive chart N y₀ inside collar y moving
  have nonzero := (a.nativeJacobian_pos (T^N)
    (DiffeomorphismIterates.mdifferentiable_pow T (deterministic.mdifferentiable one_ne_zero) N)
    (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse N) x₀).ne'
  rw [DiffeomorphismIterates.coe_pow] at nonzero
  have result := (cutoff.mul weights.abs).div jacobian nonzero
  rw [nativeWordCost_deterministic_eq]
  exact result

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
