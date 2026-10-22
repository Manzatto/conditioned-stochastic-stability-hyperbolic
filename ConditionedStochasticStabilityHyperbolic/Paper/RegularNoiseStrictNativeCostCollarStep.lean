module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseNativeCoreCostNeighborhood
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseNativeWordCostDomination
public import LeanShared.Dynamics.BasicHyperbolicStrictTerminalCostMargin
public import LeanShared.Topology.FiniteCutoffCoreBudgetCollar

/-! The strict noisy principal cost block on one common collar, together with
a uniform cap for the one-step costs on the same collar. The one-step budget
neighborhoods are added to the finite family from which the collar is built,
so the same collar and noise window serve both the block contraction and the
one-step boundedness of the actual generators. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators NNReal Topology
open LeanShared HyperbolicBasicSet FiniteSmoothCapturePartition PressureCoverRefinement
attribute [local instance] Classical.propDecidable
variable {E M I J ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I] [Fintype J] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {v : I → Set M}


private theorem common_window_step {C : Type*} (s : Finset C) (η : C → ℝ≥0)
    (positive : ∀ i ∈ s, 0 < η i) : ∃ e : ℝ≥0, 0 < e ∧ ∀ i ∈ s, e ≤ η i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s outside ih =>
    obtain ⟨e,he,bound⟩ := ih (fun j hj => positive j (Finset.mem_insert_of_mem hj))
    refine ⟨min e (η i),lt_min he (positive i (Finset.mem_insert_self _ _)),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (bound j hj)

private theorem coefficient_nonneg_step (h : HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (positive : ∀ x ∈ Λ, 0 < g x) (N : ℕ) (labels : Fin (N+1) → I) (O : Set M) :
    0 ≤ domainCoefficient Λ O (h.localizedNativeCost d g N labels) := by
  have continuous : ContinuousOn (h.localizedNativeCost d g N labels) Λ := by
    apply ((nativeWordCost_deterministic_continuousOn forward inverse
      h.normedAdaptedProjection d g weight N labels).mono h.normedAdaptedProjection.core_subset).congr
    intro x hx
    exact (nativeWordCost_core_eq_localized h d g positive N labels x hx).symm
  have bounded : BddAbove ({0} ∪ (h.localizedNativeCost d g N labels) '' (Λ ∩ O)) :=
    (isCompact_singleton.union (h.compact.image_of_continuousOn continuous)).bddAbove.mono
      (union_subset_union_right _ (image_mono inter_subset_left))
  exact le_csSup bounded (Or.inl (mem_singleton 0))

theorem Maps.exists_strict_nativeCost_collar_with_step {r : ℝ}
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (g : M → ℝ) (weight : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (d : Data (E := E) Λ v) (capture : Λ ⊆ d.capture)
    {μ ν t s : ℝ} (positiveμ : 0 < μ) (smallμ : μ < 1) (largeν : 1 < ν)
    (positiveT : 0 < t) (negativeS : s < 0) (A : ℝ) (nonnegativeA : 0 ≤ A)
    (ambient : Set M) (openAmbient : IsOpen ambient) (coreAmbient : Λ ⊆ ambient)
    (minimum : ℕ) :
    ∃ P : ℝ, ThermodynamicDefinitions.pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
    ∃ ρ radius : ℝ, 0 < ρ ∧ ρ < Real.exp P ∧ 0 < radius ∧
    ∃ N : ℕ, 0 < N ∧ minimum ≤ N ∧ ∃ centers : Finset M,
    ∃ p : Data (E := E) Λ
      (fun y : centers => BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val),
      Λ ⊆ p.capture ∧ ∃ W : Set M, IsOpen W ∧ Λ ⊆ W ∧
      closure W ⊆ (ambient ∩ p.capture) ∩ b.hyperbolic.normedAdaptedProjection.collar ∧
      ∃ η : ℝ≥0, 0 < η ∧ η ≤ F.window ∧ ∃ stepCap : ℝ, 0 ≤ stepCap ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ controls : ℕ → cube (ι := ι) ε,
      ∀ χ : M → ℝ, (∀ x, |χ x| ≤ 1) → ∀ τ : J → M → ℝ, (∀ j x, |τ j x| ≤ 1) →
      (∑ y : centers, ∑ labels : Fin (1+1) → I, ∑ j : J,
          domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
            (fun x => |τ j (FiniteJetComposition.word
                (fun n => F.family ε (controls n).val) 1 x)| *
              nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x*g x)
                (fun n => F.family ε (controls n).val) 1 labels x)) ≤ stepCap ∧
      A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s) *
        (∑ y : centers, ∑ labels : Fin (N+1) → I, ∑ j : J,
          domainCoefficient (closure W ∩ tsupport (p.beta y)) univ
            (fun x => |τ j (FiniteJetComposition.word
                (fun n => F.family ε (controls n).val) N x)| *
              nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x*g x)
                (fun n => F.family ε (controls n).val) N labels x)) < ρ^N := by
  obtain ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,p,captureP,compactPieces,insidePieces,_coverPieces,δ,positiveδ,budget⟩ :=
      b.exists_strict_terminal_cost_margin (J := J) forward inverse g weight.continuousOn positive d capture
        positiveμ smallμ largeν positiveT negativeS A nonnegativeA minimum
  let C := centers × (Fin (N+1) → I)
  let C₁ := centers × (Fin (1+1) → I)
  have individual (i : C) := F.exists_nativeCost_budget_neighborhood regularity forward
    (inverse.mdifferentiable one_ne_zero) b.hyperbolic d g weight positive N i.2
    (BowenOpenCoverCoefficient.orbitBall T (N+1) radius i.1.val)
    (Λ ∩ tsupport (p.beta i.1)) (compactPieces i.1) inter_subset_left (insidePieces i.1) δ positiveδ
  choose O openO coreO _collarO η positiveη bound using individual
  have individualStep (i : C₁) := F.exists_nativeCost_budget_neighborhood regularity forward
    (inverse.mdifferentiable one_ne_zero) b.hyperbolic d g weight positive 1 i.2
    univ (Λ ∩ tsupport (p.beta i.1)) (compactPieces i.1) inter_subset_left (subset_univ _)
    1 one_pos
  choose O₁ openO₁ coreO₁ _collarO₁ η₁ positiveη₁ bound₁ using individualStep
  obtain ⟨e,positiveE,belowE⟩ := common_window_step (Finset.univ : Finset C) η (fun i _ => positiveη i)
  obtain ⟨e₁,positiveE₁,belowE₁⟩ :=
    common_window_step (Finset.univ : Finset C₁) η₁ (fun i _ => positiveη₁ i)
  obtain ⟨W,openW,coreW,closureW,budgetW⟩ := FiniteCutoffCoreBudgetCollar.exists_collar
    b.hyperbolic.compact ((openAmbient.inter p.open_capture).inter b.hyperbolic.normedAdaptedProjection.open_collar)
    (fun x hx => ⟨⟨coreAmbient hx,captureP hx⟩,b.hyperbolic.normedAdaptedProjection.core_subset hx⟩)
    (fun i : C ⊕ C₁ => Sum.elim (fun i : C => p.beta i.1) (fun i : C₁ => p.beta i.1) i)
    (Sum.elim O O₁) (fun i => by cases i with | inl i => exact openO i | inr i => exact openO₁ i)
    (fun i => by cases i with | inl i => exact coreO i | inr i => exact coreO₁ i)
  let q₁ := fun i : C₁ => domainCoefficient Λ univ (b.hyperbolic.localizedNativeCost d g 1 i.2)
  have nonnegativeQ₁ (i : C₁) : 0 ≤ q₁ i := coefficient_nonneg_step b.hyperbolic forward
    (inverse.mdifferentiable one_ne_zero) d g weight positive 1 i.2 univ
  refine ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,p,captureP,W,openW,coreW,closureW,min (min e e₁) F.window,
    lt_min (lt_min positiveE positiveE₁) F.window_positive, min_le_right _ _,
    ∑ y : centers, ∑ labels : Fin (1+1) → I, ∑ _j : J, (q₁ (y,labels) + 1),
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun labels _ => Finset.sum_nonneg fun _ _ =>
      add_nonneg (nonnegativeQ₁ (y,labels)) zero_le_one,?_⟩
  intro ε positiveε smallε controls χ killing τ terminal
  refine ⟨?_, ?_⟩
  · apply Finset.sum_le_sum
    intro y _
    apply Finset.sum_le_sum
    intro labels _
    apply Finset.sum_le_sum
    intro j _
    unfold domainCoefficient
    apply csSup_le (s := ({(0 : ℝ)} ∪
      (fun x => |τ j (FiniteJetComposition.word (fun n => F.family ε (controls n).val) 1 x)| *
        nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x*g x)
          (fun n => F.family ε (controls n).val) 1 labels x) ''
        ((closure W ∩ tsupport (p.beta y)) ∩ univ) : Set ℝ))
      ⟨0,Or.inl (mem_singleton 0)⟩
    rintro a (zero | ⟨x,hx,rfl⟩)
    · rw [mem_singleton_iff.mp zero]
      exact add_nonneg (nonnegativeQ₁ (y,labels)) zero_le_one
    · have valid : x ∈ closure (O₁ (y,labels)) :=
        subset_closure (budgetW (Sum.inr (y,labels)) hx.1)
      have small : ε ≤ η₁ (y,labels) :=
        ((smallε.trans (min_le_left _ _)).trans (min_le_right _ _)).trans
          (belowE₁ (y,labels) (Finset.mem_univ _))
      exact (nativeWordCost_killed_terminal_le b.hyperbolic.normedAdaptedProjection d g χ (τ j)
        killing (terminal j) (fun n => F.family ε (controls n).val) 1 labels x).trans
        (bound₁ (y,labels) ε positiveε small controls x valid)
  apply budget
  intro y labels j
  have nonnegativeQ := coefficient_nonneg_step b.hyperbolic forward (inverse.mdifferentiable one_ne_zero)
    d g weight positive N labels (BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val)
  unfold domainCoefficient
  apply csSup_le (s := ({(0 : ℝ)} ∪
    (fun x => |τ j (FiniteJetComposition.word (fun n => F.family ε (controls n).val) N x)| *
      nativeWordCost b.hyperbolic.normedAdaptedProjection d (fun x => χ x*g x)
        (fun n => F.family ε (controls n).val) N labels x) ''
      ((closure W ∩ tsupport (p.beta y)) ∩ univ) : Set ℝ))
    ⟨0,Or.inl (mem_singleton 0)⟩
  rintro a (zero | ⟨x,hx,rfl⟩)
  · rw [mem_singleton_iff.mp zero]
    exact add_nonneg nonnegativeQ positiveδ.le
  · have valid : x ∈ closure (O (y,labels)) :=
      subset_closure (budgetW (Sum.inl (y,labels)) hx.1)
    have small : ε ≤ η (y,labels) :=
      ((smallε.trans (min_le_left _ _)).trans (min_le_left _ _)).trans
        (belowE (y,labels) (Finset.mem_univ _))
    exact (nativeWordCost_killed_terminal_le b.hyperbolic.normedAdaptedProjection d g χ (τ j)
      killing (terminal j) (fun n => F.family ε (controls n).val) N labels x).trans
      (bound (y,labels) ε positiveε small controls x valid)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
