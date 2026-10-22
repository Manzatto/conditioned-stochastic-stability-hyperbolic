module
public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import LeanShared.Dynamics.ProductIsolationMixing

/-! The product nonwandering and periodic-density identities are derived
from original Axiom-A periodic density and a periodic-dense full auxiliary
factor. No product Axiom-A or nonwandering identity is assumed. -/
@[expose] public noncomputable section
open Set Function
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProductNonwandering
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

omit [MetricSpace X] [MetricSpace Y] in
theorem periodic_product (f : X → X) (g : Y → Y) :
    periodicPts (Prod.map f g) = periodicPts f ×ˢ periodicPts g := by
  ext z
  constructor
  · rintro ⟨n, hn, hz⟩
    have heq : ((f^[n]) z.1, (g^[n]) z.2) = z := by
      simpa only [IsPeriodicPt, IsFixedPt, LeanShared.iterate_independent] using hz
    exact ⟨⟨n, hn, congrArg Prod.fst heq⟩, ⟨n, hn, congrArg Prod.snd heq⟩⟩
  · rintro ⟨⟨n, hn, hx⟩, ⟨m, hm, hy⟩⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    change (Prod.map f g)^[n * m] z = z
    rw [LeanShared.iterate_independent, hx.mul_const m, hy.const_mul n]

theorem periodic_subset (f : X → X) : periodicPts f ⊆ nonwanderingSet f := by
  rintro x ⟨n, hn, hx⟩ U hU hxU
  exact ⟨n, hn, x, hxU, by simpa only [hx.eq] using hxU⟩

theorem nonwandering_closed (f : X → X) : IsClosed (nonwanderingSet f) := by
  classical
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change ¬ ∀ U : Set X, IsOpen U → x ∈ U →
    ∃ n : ℕ, 0 < n ∧ ∃ y ∈ U, f^[n] y ∈ U at hx
  push Not at hx
  obtain ⟨U, hU, hxU, hno⟩ := hx
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy hynw
  obtain ⟨n, hn, z, hz, hzn⟩ := hynw U hU hy
  exact hno n hn z hz hzn

theorem nonwandering_projection (f : X → X) (g : Y → Y) :
    nonwanderingSet (Prod.map f g) ⊆ nonwanderingSet f ×ˢ (univ : Set Y) := by
  intro z hz
  refine ⟨?_, mem_univ _⟩
  intro U hU hzU
  obtain ⟨n, hn, w, hw, hwn⟩ := hz (U ×ˢ (univ : Set Y)) (hU.prod isOpen_univ)
    ⟨hzU, mem_univ _⟩
  refine ⟨n, hn, w.1, hw.1, ?_⟩
  simpa only [LeanShared.iterate_independent] using hwn.1

theorem nonwandering_product (f : X → X) (g : Y → Y)
    (hf : closure (periodicPts f) = nonwanderingSet f)
    (hg : closure (periodicPts g) = (univ : Set Y)) :
    nonwanderingSet (Prod.map f g) = nonwanderingSet f ×ˢ (univ : Set Y) := by
  apply Subset.antisymm (nonwandering_projection f g)
  rw [← hf, ← hg, ← closure_prod_eq, ← periodic_product]
  exact closure_minimal (periodic_subset _) (nonwandering_closed _)

theorem periodic_dense_product (f : X → X) (g : Y → Y)
    (hf : closure (periodicPts f) = nonwanderingSet f)
    (hg : closure (periodicPts g) = (univ : Set Y)) :
    closure (periodicPts (Prod.map f g)) = nonwanderingSet (Prod.map f g) := by
  rw [periodic_product, closure_prod_eq, hf, hg, nonwandering_product f g hf hg]

end ConditionedStochasticStabilityHyperbolic.Paper.ProductNonwandering
