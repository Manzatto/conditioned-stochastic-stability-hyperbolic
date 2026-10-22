module

public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductGlobalGeometry

/-! Stabilization preserves the actual adapted filtration. Every shifted
level, literal stratum, closed layer and positive prefix is the original
set times the full auxiliary space. No noisy or spectral inputs occur. -/
@[expose] public noncomputable section
open Set Function
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration
open LeanShared ShiftedFiltrationGeometry FiltrationPressureConfinement
variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]

omit [MetricSpace X] [MetricSpace Y] in
 theorem filtrationLayer_product_univ (L : ℕ → Set X) (i : ℕ) :
    filtrationLayer (fun j => L j ×ˢ (univ : Set Y)) i =
      filtrationLayer L i ×ˢ (univ : Set Y) := by
  ext z
  simp only [filtrationLayer, mem_sdiff, mem_prod, mem_univ, and_true]

 theorem isolatedCore_univ (S : Y ≃ₜ Y) : isolatedCore S univ = univ := by
  ext y
  simp [isolatedCore, forwardTrapped]

variable (T : X ≃ₜ X) (S : Y ≃ₜ Y) (A : Set X) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ)

/-- The same finite index and the literal product positive levels give an
adapted filtration for the stabilized system. -/
def source [CompactSpace Y] : AdaptedSource (T.prodCongr S)
    (A ×ˢ (univ : Set Y)) (fun i => Λ i ×ˢ univ) ℓ where
  levels := fun i => D.levels i ×ˢ univ
  index := D.index
  zero := by rw [D.zero]
  monotone := fun i j hij z hz => ⟨D.monotone hij hz.1, mem_univ _⟩
  absorbing_forward := Paper.ProductGlobalGeometry.absorbing_forward T S A D.absorbing_forward
  compact_positive := fun i hi hiℓ => (D.compact_positive i hi hiℓ).prod isCompact_univ
  adapted_positive := by
    intro i hi hiℓ z hz
    rw [interior_prod_eq, interior_univ]
    exact ⟨D.adapted_positive i hi hiℓ hz.1, mem_univ _⟩
  terminal := by rw [D.terminal]; exact univ_prod_univ
  literal_core := by
    intro i
    rw [filtrationLayer_product_univ, isolatedCore_product, D.literal_core i,
      isolatedCore_univ]

@[simp] theorem source_levels [CompactSpace Y] (i : ℕ) :
    (source T S A Λ ℓ D).levels i = D.levels i ×ˢ (univ : Set Y) := rfl

@[simp] theorem source_index [CompactSpace Y] (i : Fin ℓ) :
    (source T S A Λ ℓ D).index i = D.index i := rfl

/-- A common preimage shift commutes with stabilization, including level zero. -/
theorem shifted_levels [CompactSpace Y] (N i : ℕ) :
    levels (T.prodCongr S) (A ×ˢ (univ : Set Y)) (fun j => Λ j ×ˢ univ) ℓ N
      (source T S A Λ ℓ D) i = levels T A Λ ℓ N D i ×ˢ univ := by
  by_cases hi : i = 0
  · subst i
    rw [levels_zero, levels_zero]
  · simp only [levels, shiftedFiltration, hi, ↓reduceIte, source_levels]
    ext z
    change (Prod.map (T : X → X) (S : Y → Y))^[N] z ∈
      D.levels i ×ˢ univ ↔ z ∈ ((T : X → X)^[N] ⁻¹' D.levels i) ×ˢ univ
    rw [iterate_independent]
    simp only [mem_prod, mem_univ, and_true, mem_preimage]

theorem stratum_product [CompactSpace Y] (N : ℕ) (i : Fin ℓ) :
    stratum (T.prodCongr S) (A ×ˢ (univ : Set Y)) (fun j => Λ j ×ˢ univ) ℓ N
      (source T S A Λ ℓ D) i = stratum T A Λ ℓ N D i ×ˢ univ := by
  unfold stratum filtrationLayer
  rw [shifted_levels, shifted_levels]
  ext z
  simp only [mem_sdiff, mem_prod, mem_univ, and_true]

theorem closedLayer_product [CompactSpace Y] (N : ℕ) (i : Fin ℓ) :
    closedLayer (T.prodCongr S) (A ×ˢ (univ : Set Y)) (fun j => Λ j ×ˢ univ) ℓ N
      (source T S A Λ ℓ D) i = closedLayer T A Λ ℓ N D i ×ˢ univ := by
  rw [closedLayer, stratum_product, closure_prod_eq, closure_univ]
  rfl

theorem actualPrefix_product [CompactSpace X] [CompactSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (k : Fin ℓ) (N : ℕ) :
    DerivedHG2Application.actualPrefix (T.prodCongr S) (A ×ˢ (univ : Set Y))
      (fun j => Λ j ×ˢ univ) ℓ (source T S A Λ ℓ D) k N =
      DerivedHG2Application.actualPrefix T A Λ ℓ D k N ×ˢ univ :=
  shifted_levels T S A Λ ℓ D N (k.val + 1)

 theorem strict_trapping (h : MapsTo T (closure A) A) :
    MapsTo (T.prodCongr S) (closure (A ×ˢ (univ : Set Y))) (A ×ˢ univ) :=
  Paper.ProductGlobalGeometry.strict_trapping T S A h

end ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration
