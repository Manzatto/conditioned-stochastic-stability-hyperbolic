module
public import LeanShared.Topology.CompactRootLocalization
public import Mathlib.Topology.Constructions.SumProd

/-! Local injectivity of the actual skew map excludes every other global
root near an injective compact-state fiber. Thus a globally chosen root is
an actual local inverse, without assuming regularity of the choice. -/
public noncomputable section
namespace LeanShared.CompactLocalInverseUniqueness
open Set Filter
open scoped Topology

theorem eventually_unique_at_images
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (F : A × X → Y) (continuous : Continuous F) (a : A) (x : X)
    (injective : Function.Injective (fun z => F (a,z)))
    (V : Set (A × X)) (openV : IsOpen V) (member : (a,x) ∈ V)
    (locally : InjOn (fun p : A × X => (p.1,F p)) V) :
    ∀ᶠ p : A × X in 𝓝 (a,x), ∃! z : X, F (p.1,z) = F p := by
  obtain ⟨U,W,openU,memberU,openW,memberW,product⟩ :=
    mem_nhds_prod_iff'.mp (openV.mem_nhds member)
  have roots := LeanShared.CompactRootLocalization.eventually_all_roots F continuous a x injective W openW memberW
  have nearRoots := ((continuous_fst.prodMk continuous).tendsto (a,x)).eventually roots
  have nearParameter : ∀ᶠ p : A × X in 𝓝 (a,x), p.1 ∈ U :=
    (continuous_fst.tendsto (a,x)).eventually (openU.mem_nhds memberU)
  filter_upwards [nearRoots,nearParameter,openV.mem_nhds member] with p hp parameter inside
  refine ⟨p.2,rfl,fun z equation => ?_⟩
  have source : (p.1,z) ∈ V := product ⟨parameter,hp z equation⟩
  exact congrArg Prod.snd (locally source inside (Prod.ext rfl equation))

@[expose] def root
    {A X Y : Type*} (F : A × X → Y) (default : X) (p : A × Y) : X := by
  classical
  exact if h : ∃ z : X, F (p.1,z) = p.2 then Classical.choose h else default

theorem root_eq_of_unique
    {A X Y : Type*} (F : A × X → Y) (default : X) (a : A) (y : Y) (x : X)
    (value : F (a,x) = y) (unique : ∀ z, F (a,z) = y → z = x) : root F default (a,y) = x := by
  have witness : ∃ z : X, F (a,z) = y := ⟨x,value⟩
  rw [root,dite_eq_left witness]
  exact unique _ (Classical.choose_spec witness)

theorem eventually_leftInverse
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (F : A × X → Y) (continuous : Continuous F) (a : A) (x default : X)
    (injective : Function.Injective (fun z => F (a,z)))
    (V : Set (A × X)) (openV : IsOpen V) (member : (a,x) ∈ V)
    (locally : InjOn (fun p : A × X => (p.1,F p)) V) :
    ∀ᶠ p : A × X in 𝓝 (a,x), (p.1,root F default (p.1,F p)) = p := by
  filter_upwards [eventually_unique_at_images F continuous a x injective V openV member locally] with p hp
  refine Prod.ext (by rfl) ?_
  apply root_eq_of_unique F default p.1 (F p) p.2 rfl
  intro z hz
  exact (ExistsUnique.unique hp hz rfl)

end LeanShared.CompactLocalInverseUniqueness
