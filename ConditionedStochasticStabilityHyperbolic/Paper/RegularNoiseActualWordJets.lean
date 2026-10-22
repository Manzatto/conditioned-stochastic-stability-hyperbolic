module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFiniteItinerary
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMovingWords
public import LeanShared.Analysis.CoordinateWordGerms
public import LeanShared.Analysis.MovingJetGerms
public import LeanShared.Analysis.LocalJetCoordinateChanges
import all LeanShared.Analysis.FiniteJetComposition

/-! The finite Whitney coordinate word is identified with the coordinate
expression of the ACTUAL manifold noisy word. Validity is a computed open
itinerary condition, and local equality is derived separately at every noise
and moving point. No deterministic killed operator or noise-scale continuity
is introduced. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

private theorem constant_word {M : Type*} (T : M → M) (n : ℕ) :
    word (fun _ => T) n = T^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    simp only [word, Function.comp_apply, ih, Function.iterate_succ_apply']

@[expose] def WhitneyAtlas.actualWordDomain
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] {T : M → M}
    (A : WhitneyAtlas (E := E) T) (chart : ℕ → Fin A.count) (N : ℕ) : Set E :=
  prefixDomain (fun n => A.stepCoordinate T (chart n) (chart (n + 1)))
    (fun n => A.stepDomain (chart n) (chart (n + 1))) N ∩
    {x | x ∈ (A.source (chart 0)).target ∧ ∀ n ≤ N,
      T^[n] ((A.source (chart 0)).symm x) ∈ (A.source (chart n)).source}

set_option maxHeartbeats 1600000 in
theorem Maps.actual_word_jetConvergesOn
    {E M ι A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (chart : ℕ → Fin F.atlas.count) (N : ℕ) :
    JetConvergesOn
      (fun a => F.atlas.source (chart N) ∘
        word (fun n => F.family (ε a) (controls n a).val) N ∘
          (F.atlas.source (chart 0)).symm)
      (F.atlas.source (chart N) ∘ (T : M → M)^[N] ∘
        (F.atlas.source (chart 0)).symm) l (F.atlas.actualWordDomain chart N) := by
  have coordinate := (F.finite_itinerary_jetConvergesOn regularity deterministic
    ε controls l limit positive chart N).mono
      (V := F.atlas.actualWordDomain chart N) inter_subset_left
  apply coordinate.congr_moving_germs
  · intro x hx
    have result := coordinate_word_germ (fun n => F.atlas.source (chart n))
      (fun _ => (T : M → M)) (fun _ => T.continuous) x N hx.2.1
      (fun n hn => by simpa only [constant_word] using hx.2.2 n hn)
    simpa only [constant_word, WhitneyAtlas.stepCoordinate] using result
  · intro x hx v moving
    have initial := moving.eventually ((F.atlas.source (chart 0)).open_target.mem_nhds hx.2.1)
    have input := ((F.atlas.source (chart 0)).continuousAt_symm hx.2.1).tendsto.comp moving
    have allInside : ∀ᶠ a in l, ∀ n : Fin (N + 1),
        word (fun j => F.family (ε a) (controls j a).val) n.val
          ((F.atlas.source (chart 0)).symm (v a)) ∈ (F.atlas.source (chart n.val)).source := by
      rw [eventually_all]
      intro n
      exact (F.moving_word_tendsto ε controls l limit positive _ _ input n.val).eventually
        ((F.atlas.source (chart n.val)).open_source.mem_nhds
          (hx.2.2 n.val (Nat.le_of_lt_succ n.isLt)))
    have window : ∀ᶠ a in l, ε a ≤ F.window :=
      (limit.eventually (gt_mem_nhds F.window_positive)).mono (fun _ h => h.le)
    filter_upwards [initial, allInside, positive, window] with a hi hs hp hw
    exact coordinate_word_germ (fun n => F.atlas.source (chart n))
      (fun n => F.family (ε a) (controls n a).val)
      (fun n => (F.map_regular (ε a) hp hw (controls n a)).differentiable.continuous)
      (v a) N hi (fun n hn => hs ⟨n, Nat.lt_succ_of_le hn⟩)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
