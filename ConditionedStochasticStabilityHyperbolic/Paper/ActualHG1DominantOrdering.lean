module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualAnosovGlobalStabilization

/-! The adapted filtration itself gives injective retained indices and live
basic sets. HG1's single dominant pressure then supplies the exact strict
finite-prefix ordering, also on the constructed stabilized decomposition.
No pressure-gap conclusion is accepted as ordinary source data. -/
public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualHG1DominantOrdering
open LeanShared HyperbolicBasicSet Global.ShiftedFiltrationGeometry

variable {X I : Type*} [MetricSpace X] (T : X ≃ₜ X) (A : Set X)
  (Λ : I → Set X) (ℓ : ℕ) (filtration : AdaptedSource T A Λ ℓ)

/-- Every enumerated core is actually live, including the first stratum. -/
theorem index_live (i : Fin ℓ) : Λ (filtration.index i) ⊆ Aᶜ := by
  intro x hx
  have orbit : x ∈ isolatedCore T (filtrationLayer filtration.levels i.val) :=
    filtration.literal_core i ▸ hx
  have layer := forwardTrapped_subset T _ orbit.1
  intro hxA
  have hx0 : x ∈ filtration.levels 0 := by rw [filtration.zero]; exact hxA
  exact layer.2 (filtration.monotone (Nat.zero_le i.val) hx0)

/-- Repeating a nonempty basic core would put a point in two disjoint literal
strata, so no injectivity hypothesis is needed on the adapted source. -/
theorem index_injective (nonempty : ∀ i : Fin ℓ, (Λ (filtration.index i)).Nonempty) :
    Injective filtration.index := by
  intro i j equal
  by_contra different
  have impossible (p q : Fin ℓ) (same : filtration.index p = filtration.index q)
      (less : p.val < q.val) : False := by
    obtain ⟨x, hx⟩ := nonempty p
    have first : x ∈ isolatedCore T (filtrationLayer filtration.levels p.val) :=
      filtration.literal_core p ▸ hx
    have second : x ∈ isolatedCore T (filtrationLayer filtration.levels q.val) :=
      filtration.literal_core q ▸ (same ▸ hx)
    have firstLayer := forwardTrapped_subset T _ first.1
    have secondLayer := forwardTrapped_subset T _ second.1
    exact secondLayer.2 (filtration.monotone (by omega) firstLayer.1)
  have neVal : i.val ≠ j.val := fun equality => different (Fin.ext equality)
  rcases lt_or_gt_of_ne neVal with less | greater
  · exact impossible i j equal less
  · exact impossible j i equal.symm greater

section Hyperbolic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace X] [BorelSpace X]
  (D : SpectralDecomposition (E := E) T) {g : X → ℝ} (h : HG1 D g A)
  (retained : AdaptedSource T A D.core ℓ) (j : Fin ℓ)
  (selected : retained.index j = h.dominant)

include h selected in
omit [BorelSpace X] in
/-- HG1 needs mixing only on its selected basic set; subordinate pressure
ordering follows without any mixing or distinct-pressure premise. -/
theorem pressure_gap : ∀ i : Fin ℓ, i ≠ j →
    D.pressure g (retained.index i) < D.pressure g (retained.index j) := by
  intro i different
  have inj := index_injective T A D.core ℓ retained (fun i => (D.basic _).nonempty)
  rw [selected]
  apply h.pressure_dominant _ (index_live T A D.core ℓ retained i)
  intro equality
  exact different (inj (equality.trans selected.symm))

end Hyperbolic
end ConditionedStochasticStabilityHyperbolic.Paper.ActualHG1DominantOrdering
