module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualDiffeomorphisms
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCompactManifold
public import LeanShared.Geometry.FiniteDiffeomorphismWords
public import LeanShared.Geometry.DiffeomorphismDifferential

/-! Every literal finite physical noise word is an actual global C1
diffeomorphism, with its actual intrinsic differential constructed. Ambient
compactness is derived from the given finite Whitney atlas. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared CylinderPrincipalCoefficient

theorem Maps.finite_diffeomorphism_words
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    ∃ cutoff : ℝ≥0, 0 < cutoff ∧ cutoff ≤ F.window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ cutoff → ∀ N : ℕ, ∀ control : Fin N → cube (ι := ι) ε,
      ∃ W : M ≃ₜ M,
        (W : M → M) = prefixOrbit (fun k : Fin N => F.family ε (control k).val) (fun k => k) N ∧
        ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 W ∧ ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 W.symm ∧
        ∀ x : M, ∃ D : TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ,E)) (W x),
          D.toContinuousLinearMap = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) W x := by
  let : CompactSpace M := F.atlas.compactSpace
  obtain ⟨cutoff,positiveCutoff,cap,homeos⟩ := F.exists_actual_diffeomorphisms regularity deterministic inverse
  refine ⟨cutoff,positiveCutoff,cap,?_⟩
  intro ε hp hw N control
  obtain ⟨H,identity,smooth,_continuousInverse⟩ := homeos ε hp hw
  let W := DiffeomorphismWords.homeomorph (FiniteDiffeomorphismWords.extend (fun k : Fin N => H (control k))) N
  have forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 W :=
    FiniteDiffeomorphismWords.forward (fun k : Fin N => H (control k)) (fun k => (smooth (control k)).1) N
  have backward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 W.symm :=
    FiniteDiffeomorphismWords.backward (fun k : Fin N => H (control k)) (fun k => (smooth (control k)).2) N
  refine ⟨W,?_,forward,backward,?_⟩
  · change (DiffeomorphismWords.homeomorph
      (FiniteDiffeomorphismWords.extend (fun k : Fin N => H (control k))) N : M → M) = _
    rw [FiniteDiffeomorphismWords.coe_word]
    have mapsEq : (fun k : Fin N => (H (control k) : M → M)) =
        (fun k : Fin N => F.family ε (control k).val) := by
      funext k x
      exact identity (control k) x
    rw [mapsEq]
  · intro x
    exact ⟨DiffeomorphismDifferential.differential W
      (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero) x,rfl⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
