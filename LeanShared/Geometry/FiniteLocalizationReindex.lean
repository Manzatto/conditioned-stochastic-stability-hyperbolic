module
public import LeanShared.Geometry.ConstructedManifoldLocalization

/-! Reindex a genuine finite partition by its actual finite chart set.
The resulting atlas contains every original selected chart exactly once. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
namespace LeanShared.FiniteLocalizationReindex
variable {E M J:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [T2Space M] [CompactSpace M]
  {S:Set M} (e:J→OpenPartialHomeomorph M E)
  (D:ConstructedManifoldLocalization.Data e S)

@[expose] def atlas : D.indices→OpenPartialHomeomorph M E := fun i=>e i

@[expose] def data : ConstructedManifoldLocalization.Data (atlas e D) S where
  indices := Finset.univ
  cutoff i := D.cutoff i.val
  smooth i := D.smooth i.val
  support i := D.support i.val
  compact i := D.compact i.val
  partition x hx := by
    let eqv : {i:D.indices // i∈(Finset.univ:Finset D.indices)}≃D.indices :=
      { toFun := Subtype.val
        invFun := fun i=>⟨i,Finset.mem_univ i⟩
        left_inv := fun _=>rfl
        right_inv := fun _=>rfl }
    exact (Fintype.sum_equiv eqv (fun i=>D.cutoff i.val x) (fun i=>D.cutoff i x) (fun _=>rfl)).trans
      (D.partition x hx)

@[expose] def indexEquiv : (data e D).indices≃D.indices where
  toFun i := i.val
  invFun i := ⟨i,Finset.mem_univ i⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [T2Space M] in
theorem support (i:(data e D).indices) :
    ConstructedManifoldLocalization.support (atlas e D) (data e D) i =
      ConstructedManifoldLocalization.support e D i.val := rfl

variable (mem:∀j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {Core:Type*} [AddCommGroup Core] [Module ℂ Core]
  (functions:Core→ₗ[ℂ](M→ℂ))
  (smooth:∀f:Core,ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (functions f))

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [T2Space M] in
theorem localize (i:(data e D).indices) (f:Core) :
    ConstructedManifoldLocalization.localize (atlas e D) (data e D) (fun j=>mem j.val)
      functions smooth i f =
    ConstructedManifoldLocalization.localize e D mem functions smooth i.val f := rfl

variable {B:D.indices→Type*} [∀i,NormedAddCommGroup (B i)]
  (f:∀i:(data e D).indices,B i.val)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [T2Space M] in
theorem norm_reindexed : ‖f‖=‖fun i:D.indices=>f ⟨i,Finset.mem_univ i⟩‖ := by
  apply le_antisymm
  · apply pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr
    intro i
    exact norm_le_pi_norm (fun j:D.indices=>f ⟨j,Finset.mem_univ j⟩) i.val
  · apply pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr
    intro i
    exact norm_le_pi_norm f ⟨i,Finset.mem_univ i⟩
end LeanShared.FiniteLocalizationReindex
