module

public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import LeanShared.Dynamics.ProductIsolationMixing

/-! Exact global bookkeeping for stabilization by a full auxiliary manifold.
No hyperbolicity, spectral theorem or pressure identity is assumed here.
In particular the strict trapping premise is transported separately from
literal HG's weaker forward-invariance premise. -/
@[expose] public noncomputable section
open Set Function Filter Metric
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProductGlobalGeometry
variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]

 theorem infDist_product_univ (K : Set X) (hK : K.Nonempty) (z : X × Y) :
    infDist z (K ×ˢ (univ : Set Y)) = infDist z.1 K := by
  apply le_antisymm
  · apply (le_infDist hK).mpr
    intro x hx
    exact (infDist_le_dist_of_mem (show (x, z.2) ∈ K ×ˢ (univ : Set Y) from ⟨hx, mem_univ _⟩)).trans_eq
      (by simp [Prod.dist_eq])
  · apply (le_infDist (hK.prod (show (univ : Set Y).Nonempty from ⟨z.2, mem_univ _⟩))).mpr
    intro w hw
    exact (infDist_le_dist_of_mem hw.1).trans (by simp [Prod.dist_eq])

 theorem stableBasin_product_univ (T : X ≃ₜ X) (S : Y ≃ₜ Y)
    (K : Set X) (hK : K.Nonempty) :
    Global.PaperStableBasin.stableBasin (T.prodCongr S) (K ×ˢ (univ : Set Y)) =
      Global.PaperStableBasin.stableBasin T K ×ˢ (univ : Set Y) := by
  ext z
  simp only [Global.PaperStableBasin.stableBasin, mem_ofPred_eq, mem_prod, mem_univ, and_true]
  have heq : (fun n : ℕ => infDist ((T.prodCongr S : X × Y → X × Y)^[n] z)
      (K ×ˢ (univ : Set Y))) = (fun n : ℕ => infDist ((T : X → X)^[n] z.1) K) := by
    funext n
    change infDist ((Prod.map (T : X → X) (S : Y → Y))^[n] z) _ = _
    rw [LeanShared.iterate_independent]
    exact infDist_product_univ K hK _
  rw [heq]
  exact and_congr_left fun _ => ⟨fun _ => hK, fun _ => hK.prod ⟨z.2, mem_univ _⟩⟩

 theorem heteroclinic_product_univ [Nonempty Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y)
    (K : I → Set X) (hne : ∀ i, (K i).Nonempty) (i j : I) :
    Global.PaperStableBasin.heteroclinicRelation (T.prodCongr S)
      (fun k => K k ×ˢ (univ : Set Y)) i j ↔
      Global.PaperStableBasin.heteroclinicRelation T K i j := by
  unfold Global.PaperStableBasin.heteroclinicRelation Global.PaperStableBasin.unstableBasin
  rw [stableBasin_product_univ T S _ (hne j)]
  rw [show (T.prodCongr S).symm = T.symm.prodCongr S.symm from rfl,
    stableBasin_product_univ T.symm S.symm _ (hne i)]
  constructor
  · rintro ⟨z, hz, hw⟩
    exact ⟨z.1, ⟨hz.1.1, fun h => hz.2 ⟨h, mem_univ _⟩⟩,
      ⟨hw.1.1, fun h => hw.2 ⟨h, mem_univ _⟩⟩⟩
  · rintro ⟨x, hx, hw⟩
    exact ⟨(x, Classical.choice inferInstance),
      ⟨⟨hx.1, mem_univ _⟩, fun h => hx.2 h.1⟩,
      ⟨⟨hw.1, mem_univ _⟩, fun h => hw.2 h.1⟩⟩

omit [MetricSpace X] [MetricSpace Y] in
 theorem live_product_univ [Nonempty Y] (K A : Set X) :
    K ×ˢ (univ : Set Y) ⊆ (A ×ˢ (univ : Set Y))ᶜ ↔ K ⊆ Aᶜ := by
  constructor
  · intro h x hx ha
    exact h (show (x, Classical.choice (inferInstance : Nonempty Y)) ∈ K ×ˢ (univ : Set Y) from
      ⟨hx, mem_univ _⟩) ⟨ha, mem_univ _⟩
  · intro h z hz ha
    exact h hz.1 ha.1

 theorem absorbing_forward (T : X ≃ₜ X) (S : Y ≃ₜ Y) (A : Set X)
    (h : MapsTo T A A) : MapsTo (T.prodCongr S) (A ×ˢ (univ : Set Y))
      (A ×ˢ (univ : Set Y)) := fun _ hz => ⟨h hz.1, mem_univ _⟩

 theorem strict_trapping (T : X ≃ₜ X) (S : Y ≃ₜ Y) (A : Set X)
    (h : MapsTo T (closure A) A) :
    MapsTo (T.prodCongr S) (closure (A ×ˢ (univ : Set Y))) (A ×ˢ (univ : Set Y)) := by
  rw [closure_prod_eq, closure_univ]
  intro z hz
  exact ⟨h hz.1, mem_univ _⟩

end ConditionedStochasticStabilityHyperbolic.Paper.ProductGlobalGeometry
