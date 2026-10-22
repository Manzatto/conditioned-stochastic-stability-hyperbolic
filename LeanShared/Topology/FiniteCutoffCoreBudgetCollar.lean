module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Algebra.Support

/-! Finitely many open budgets valid on the core portions of fixed cutoff
supports hold on one genuine collar of the entire core. The same cutoffs
are retained; no extra partition or cylinder-count loss is introduced. -/
public noncomputable section
open Set
open scoped Topology
namespace LeanShared.FiniteCutoffCoreBudgetCollar
variable {X I Y : Type*} [Zero Y] [TopologicalSpace X] [RegularSpace X] [Finite I]

theorem exists_collar {K ambient : Set X} (compact : IsCompact K)
    (openAmbient : IsOpen ambient) (inside : K ⊆ ambient)
    (cutoff : I → X → Y) (budget : I → Set X) (openBudget : ∀ i, IsOpen (budget i))
    (coreBudget : ∀ i, K ∩ tsupport (cutoff i) ⊆ budget i) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ closure W ⊆ ambient ∧
      ∀ i, closure W ∩ tsupport (cutoff i) ⊆ budget i := by
  let U := ambient ∩ ⋂ i, (tsupport (cutoff i))ᶜ ∪ budget i
  have openU : IsOpen U := openAmbient.inter
    (isOpen_iInter_of_finite fun i => (isClosed_tsupport _).isOpen_compl.union (openBudget i))
  have coreU : K ⊆ U := by
    intro x hx
    refine ⟨inside hx,mem_iInter.mpr fun i => ?_⟩
    by_cases supported : x ∈ tsupport (cutoff i)
    · exact Or.inr (coreBudget i ⟨hx,supported⟩)
    · exact Or.inl supported
  obtain ⟨W,openW,coreW,closureW⟩ := compact.exists_isOpen_closure_subset (openU.mem_nhdsSet.mpr coreU)
  refine ⟨W,openW,coreW,fun x hx => (closureW hx).1,?_⟩
  intro i x hx
  rcases mem_iInter.mp (closureW hx.1).2 i with unsupported | valid
  · exact False.elim (unsupported hx.2)
  · exact valid

end LeanShared.FiniteCutoffCoreBudgetCollar
