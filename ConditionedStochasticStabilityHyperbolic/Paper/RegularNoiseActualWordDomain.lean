module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualWordJets

/-! The actual finite itinerary domain is open. This is proved from the
ordinary smooth atlas and C¹ deterministic map, so the uniform compact-word
estimate may be applied on compact subsets of actual chart itineraries. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
open LeanShared.FiniteJetComposition

theorem WhitneyAtlas.stepCoordinate_smooth
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    {T : M → M} (A : WhitneyAtlas (E := E) T)
    (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (i j : Fin A.count) (x : E) (hx : x ∈ A.stepDomain i j) :
    ContDiffAt ℝ 1 (A.stepCoordinate T i j) x := by
  have first : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (A.source i).symm x :=
    (contMDiffAt_symm_of_mem_maximalAtlas (A.source_smooth i) hx.1.1).of_le (by simp)
  have last : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (A.source j)
      (T ((A.source i).symm x)) :=
    (contMDiffAt_of_mem_maximalAtlas (A.source_smooth j) hx.2).of_le (by simp)
  exact (last.comp x (smooth.contMDiffAt.comp x first)).contDiffAt

theorem WhitneyAtlas.actualWordDomain_open
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    {T : M → M} (A : WhitneyAtlas (E := E) T)
    (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (chart : ℕ → Fin A.count) (N : ℕ) : IsOpen (A.actualWordDomain chart N) := by
  have prefixOpen := (prefixDomain_open_and_continuous
    (fun n => A.stepCoordinate T (chart n) (chart (n + 1)))
    (fun n => A.stepDomain (chart n) (chart (n + 1)))
    (fun n => A.stepDomain_open smooth.continuous (chart n) (chart (n + 1)))
    (fun n x hx => (A.stepCoordinate_smooth smooth _ _ x hx).continuousAt.continuousWithinAt)
    N).1
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have near : ∀ᶠ y in 𝓝 x, ∀ n : Fin (N + 1),
      T^[n.val] ((A.source (chart 0)).symm y) ∈ (A.source (chart n.val)).source := by
    rw [eventually_all]
    intro n
    exact ((smooth.continuous.iterate n.val).continuousAt.comp
      ((A.source (chart 0)).continuousAt_symm hx.2.1)).eventually
      ((A.source (chart n.val)).open_source.mem_nhds
        (hx.2.2 n.val (Nat.le_of_lt_succ n.isLt)))
  filter_upwards [prefixOpen.mem_nhds hx.1,
    (A.source (chart 0)).open_target.mem_nhds hx.2.1, near] with y hp hi hn
  exact ⟨hp, hi, fun n hn' => hn ⟨n, Nat.lt_succ_of_le hn'⟩⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
