module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePhysicalNativeWordCosts
public import LeanShared.Dynamics.HyperbolicLocalizedNativeCost

/-! A literal core pressure cost gives an actual nearby noisy cost budget.
The compact neighborhood and one positive noise window are constructed,
keeping the original pressure cell and its coefficient. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff NNReal BigOperators
open LeanShared LeanShared.FiniteJetComposition HyperbolicBasicSet FiniteSmoothCapturePartition
  PressureCoverRefinement
variable {E M ι I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [Fintype ι] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {v : I → Set M}

omit [Fintype ι] in
theorem nativeWordCost_core_eq_localized
    (h : HyperbolicData (E := E) T Λ) (d : Data (E := E) Λ v)
    (g : M → ℝ) (positive : ∀ x ∈ Λ, 0 < g x)
    (N : ℕ) (labels : Fin (N+1) → I) (x : M) (hx : x ∈ Λ) :
    nativeWordCost h.normedAdaptedProjection d g (fun _ => T) N labels x =
      h.localizedNativeCost d g N labels x := by
  rw [nativeWordCost_deterministic_eq]
  have invariant : MapsTo T Λ Λ := image_subset_iff.mp h.invariant.subset
  have nonnegative : 0 ≤ ∏ j ∈ Finset.range N, g ((T : M → M)^[j] x) :=
    Finset.prod_nonneg (fun j _ => (positive _ (invariant.iterate j hx)).le)
  rw [abs_of_nonneg nonnegative]
  change _ = wordCutoff d (fun j => (T : M → M)^[j.val] x) labels *
    ((∏ j ∈ Finset.range N, g ((T : M → M)^[j] x)) /
      h.nativePressureJacobian N x)
  dsimp only [HyperbolicData.nativePressureJacobian]
  ring

omit [Fintype ι] in
theorem nativeWordCost_core_le_coefficient
    (h : HyperbolicData (E := E) T Λ)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (positive : ∀ x ∈ Λ, 0 < g x) (N : ℕ) (labels : Fin (N+1) → I)
    (O : Set M) (x : M) (hx : x ∈ Λ) (ho : x ∈ O) :
    nativeWordCost h.normedAdaptedProjection d g (fun _ => T) N labels x ≤
      domainCoefficient Λ O (h.localizedNativeCost d g N labels) := by
  have continuous : ContinuousOn (h.localizedNativeCost d g N labels) Λ := by
    apply ((nativeWordCost_deterministic_continuousOn deterministic inverse
      h.normedAdaptedProjection d g weight N labels).mono h.normedAdaptedProjection.core_subset).congr
    intro y hy
    exact (nativeWordCost_core_eq_localized h d g positive N labels y hy).symm
  have bounded : BddAbove ({0} ∪ (h.localizedNativeCost d g N labels) '' (Λ ∩ O)) :=
    (isCompact_singleton.union (h.compact.image_of_continuousOn continuous)).bddAbove.mono
      (union_subset_union_right _ (image_mono inter_subset_left))
  rw [nativeWordCost_core_eq_localized h d g positive N labels x hx]
  exact le_csSup bounded (Or.inr ⟨x,⟨hx,ho⟩,rfl⟩)

theorem Maps.exists_nativeCost_budget_neighborhood
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (h : HyperbolicData (E := E) T Λ)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (positive : ∀ x ∈ Λ, 0 < g x) (N : ℕ) (labels : Fin (N+1) → I)
    (O K : Set M) (compact : IsCompact K) (core : K ⊆ Λ) (cell : K ⊆ O)
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ h.normedAdaptedProjection.collar ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
        ∀ controls : ℕ → cube (ι := ι) ε, ∀ x ∈ closure V,
          nativeWordCost h.normedAdaptedProjection d g
            (fun n => F.family ε (controls n).val) N labels x ≤
            domainCoefficient Λ O (h.localizedNativeCost d g N labels) + δ := by
  let a := h.normedAdaptedProjection
  let f := nativeWordCost a d g (fun _ => T) N labels
  let q := domainCoefficient Λ O (h.localizedNativeCost d g N labels)
  let U := a.collar ∩ f ⁻¹' Iio (q+δ/2)
  have continuous := nativeWordCost_deterministic_continuousOn deterministic inverse a d g weight N labels
  have openU : IsOpen U := continuous.isOpen_inter_preimage a.open_collar isOpen_Iio
  have inside : K ⊆ U := by
    intro x hx
    refine ⟨a.core_subset (core hx),?_⟩
    have bound := nativeWordCost_core_le_coefficient h deterministic inverse d g weight positive
      N labels O x (core hx) (cell hx)
    change f x < q+δ/2
    change f x ≤ q at bound
    linarith
  obtain ⟨V,openV,contains,closedInside⟩ := compact.exists_isOpen_closure_subset
    (openU.mem_nhdsSet.mpr inside)
  have collarV : closure V ⊆ a.collar := fun x hx => (closedInside hx).1
  obtain ⟨η,hη,budget⟩ := F.uniform_physical_nativeCost regularity deterministic inverse a d g weight
    N labels (closure V) isClosed_closure.isCompact collarV (δ/2) (by linarith)
  refine ⟨V,openV,contains,collarV,η,hη,fun ε hp hs controls x hx => ?_⟩
  have small := (abs_le.mp (budget ε hp hs controls x hx)).2
  have upper := (closedInside hx).2
  change f x < q+δ/2 at upper
  change nativeWordCost a d g (fun n => F.family ε (controls n).val) N labels x - f x ≤ δ/2 at small
  change nativeWordCost a d g (fun n => F.family ε (controls n).val) N labels x ≤ q+δ
  linarith

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
