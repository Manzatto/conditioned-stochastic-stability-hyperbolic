module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualWordDomain
import all ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualWordJets

/-! Every actual deterministic point admits a valid finite Whitney chart
itinerary. Thus the computed domain used by uniform noisy-word estimates
contains a genuine neighborhood of the chosen point. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
open LeanShared.FiniteJetComposition

set_option maxHeartbeats 1600000 in
theorem WhitneyAtlas.mem_actualWordDomain_of_patch_itinerary
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] {T : M → M}
    (A : WhitneyAtlas (E := E) T) (chart : ℕ → Fin A.count) (x : M)
    (patches : ∀ n, T^[n] x ∈ A.patch (chart n)) (N : ℕ) :
    A.source (chart 0) x ∈ A.actualWordDomain chart N := by
  have sources (n : ℕ) : T^[n] x ∈ (A.source (chart n)).source :=
    A.patch_source (chart n) (subset_closure (patches n))
  have coordinate (n : ℕ) :
      word (fun k => A.stepCoordinate T (chart k) (chart (k + 1))) n
        (A.source (chart 0) x) = A.source (chart n) (T^[n] x) := by
    simpa only [WhitneyAtlas.stepCoordinate, constant_word] using
      coordinate_word_apply (fun k => A.source (chart k)) (fun _ => T) x n
        (fun k _ => by simpa only [constant_word] using sources k)
  have validPrefix (n : ℕ) : A.source (chart 0) x ∈
      prefixDomain (fun k => A.stepCoordinate T (chart k) (chart (k + 1)))
        (fun k => A.stepDomain (chart k) (chart (k + 1))) n := by
    induction n with
    | zero => exact mem_univ _
    | succ n ih =>
      refine ⟨ih, ?_⟩
      change word (fun k => A.stepCoordinate T (chart k) (chart (k + 1))) n
        (A.source (chart 0) x) ∈ A.stepDomain (chart n) (chart (n + 1))
      rw [coordinate n]
      change (A.source (chart n) (T^[n] x) ∈ (A.source (chart n)).target ∧
        (A.source (chart n)).symm (A.source (chart n) (T^[n] x)) ∈ A.patch (chart n)) ∧
        T ((A.source (chart n)).symm (A.source (chart n) (T^[n] x))) ∈
          (A.source (chart (n + 1))).source
      rw [(A.source (chart n)).left_inv (sources n)]
      exact ⟨⟨(A.source (chart n)).map_source (sources n), patches n⟩,
        by simpa only [Function.iterate_succ_apply'] using sources (n + 1)⟩
  have initialSource : x ∈ (A.source (chart 0)).source := sources 0
  refine ⟨validPrefix N, (A.source (chart 0)).map_source (sources 0), ?_⟩
  intro n _
  rw [(A.source (chart 0)).left_inv initialSource]
  exact sources n

theorem WhitneyAtlas.exists_valid_itinerary
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] {T : M → M}
    (A : WhitneyAtlas (E := E) T) (x : M) (N : ℕ) :
    ∃ chart : ℕ → Fin A.count, A.source (chart 0) x ∈ A.actualWordDomain chart N := by
  have cover (n : ℕ) : ∃ i, T^[n] x ∈ A.patch i := by
    have inside : T^[n] x ∈ ⋃ i, A.patch i := A.patch_cover.symm ▸ mem_univ _
    exact mem_iUnion.mp inside
  choose chart patches using cover
  exact ⟨chart, A.mem_actualWordDomain_of_patch_itinerary chart x patches N⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
