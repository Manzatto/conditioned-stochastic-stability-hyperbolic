module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseJets
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseAtlas
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualWordDomain
public import LeanShared.Analysis.FiniteCoordinateItinerary
import all LeanShared.Analysis.FiniteJetComposition

/-! The actual inverse words inherit moving-point C1 convergence by the
ordinary finite itinerary chain rule. No quantitative inverse noise rate is
an input. All maps use the ORIGINAL scales and controls. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

namespace InverseFamily
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)

abbrev atlas (_family : InverseFamily F) := F.atlas.inverse

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem moving_word_tendsto
    {A : Type*} (ε : A → ℝ≥0) (controls : ℕ → ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (v : A → M) (x : M) (moving : Tendsto v l (𝓝 x)) (N : ℕ) :
    Tendsto (fun a => word (fun n y => J.map (ε a) ((controls n a).val,y)) N (v a)) l
      (𝓝 ((T.symm : M → M)^[N] x)) := by
  induction N with
  | zero => exact moving
  | succ n ih =>
    simpa only [word,Function.comp_apply,Function.iterate_succ_apply'] using
      J.moving_tendsto ε (controls n) l limit positive _ _ ih

theorem finite_itinerary_jets
    {A : Type*} (regularity : 1 ≤ r) (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (chart : ℕ → Fin J.atlas.count) (N : ℕ) :
    JetConvergesOn (fun a => word (fun n => J.atlas.stepCoordinate
      (fun y => J.map (ε a) ((controls n a).val,y)) (chart n) (chart (n+1))) N)
      (word (fun n => J.atlas.stepCoordinate T.symm (chart n) (chart (n+1))) N) l
      (prefixDomain (fun n => J.atlas.stepCoordinate T.symm (chart n) (chart (n+1)))
        (fun n => J.atlas.stepDomain (chart n) (chart (n+1))) N) := by
  apply JetConvergesOn.finite_coordinate_itinerary
  intro n _
  exact (J.actual_jets_in_charts regularity deterministic inverse ε (controls n) l limit positive
    (J.atlas.source (chart (n+1))) (J.atlas.source (chart n))
    (J.atlas.source_smooth _) (J.atlas.source_smooth _)).mono (fun _ h => ⟨h.1.1,h.2⟩)

private theorem constant_word {X : Type*} (S : X → X) (n : ℕ) :
    word (fun _ => S) n = S^[n] := by
  induction n with
  | zero => rfl
  | succ n ih => funext x; simp only [word,Function.comp_apply,ih,Function.iterate_succ_apply']

set_option maxHeartbeats 2400000 in
theorem actual_word_jets
    {A : Type*} (regularity : 1 ≤ r) (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (chart : ℕ → Fin J.atlas.count) (N : ℕ) :
    JetConvergesOn
      (fun a => J.atlas.source (chart N) ∘ word (fun n y => J.map (ε a) ((controls n a).val,y)) N ∘
        (J.atlas.source (chart 0)).symm)
      (J.atlas.source (chart N) ∘ (T.symm : M → M)^[N] ∘ (J.atlas.source (chart 0)).symm) l
      (J.atlas.actualWordDomain chart N) := by
  have coordinate := (J.finite_itinerary_jets regularity deterministic inverse ε controls l limit positive chart N).mono
    (V := J.atlas.actualWordDomain chart N) inter_subset_left
  apply coordinate.congr_moving_germs
  · intro x hx
    have result := coordinate_word_germ (fun n => J.atlas.source (chart n))
      (fun _ => (T.symm : M → M)) (fun _ => T.symm.continuous) x N hx.2.1
      (fun n hn => by simpa only [constant_word] using hx.2.2 n hn)
    simpa only [constant_word,WhitneyAtlas.stepCoordinate] using result
  · intro x hx v moving
    have initial := moving.eventually ((J.atlas.source (chart 0)).open_target.mem_nhds hx.2.1)
    have input := ((J.atlas.source (chart 0)).continuousAt_symm hx.2.1).tendsto.comp moving
    have allInside : ∀ᶠ a in l, ∀ n : Fin (N+1),
        word (fun j y => J.map (ε a) ((controls j a).val,y)) n.val
          ((J.atlas.source (chart 0)).symm (v a)) ∈ (J.atlas.source (chart n.val)).source := by
      rw [eventually_all]
      intro n
      exact (J.moving_word_tendsto ε controls l limit positive _ _ input n.val).eventually
        ((J.atlas.source (chart n.val)).open_source.mem_nhds (hx.2.2 n.val (Nat.le_of_lt_succ n.isLt)))
    have window : ∀ᶠ a in l, ε a ≤ J.window :=
      (limit.eventually (gt_mem_nhds J.positive)).mono (fun _ h => h.le)
    filter_upwards [initial,allInside,positive,window] with a hi hs hp hw
    exact coordinate_word_germ (fun n => J.atlas.source (chart n))
      (fun n y => J.map (ε a) ((controls n a).val,y))
      (fun n => (J.map_contMDiff (ε a) hp hw (controls n a)).continuous)
      (v a) N hi (fun n hn => hs ⟨n,Nat.lt_succ_of_le hn⟩)

end InverseFamily
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
