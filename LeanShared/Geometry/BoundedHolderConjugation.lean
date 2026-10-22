module

public import LeanShared.Geometry.SmoothHolderTestSpaces
public import LeanShared.Geometry.SupportedCoreConjugation
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-! Actual pointwise complex conjugation preserves the Hölder difference
quotient graph and its norm. It restricts to the constructed little Hölder
core closure by smooth-core conjugation and density. -/

public noncomputable section
open Set
open scoped BoundedContinuousFunction Manifold ContDiff
namespace LeanShared.BoundedHolderSpace
variable (X : Type*) [MetricSpace X] (u : ℝ)

@[expose] def conjugateLinear : graph X u →ₗ[ℝ] graph X u where
  toFun v := ⟨(star v.val.1, star v.val.2), by
    intro p
    change star (v.val.2 p) * weight X u p = star (v.val.1 p.val.1) - star (v.val.1 p.val.2)
    have h := congrArg star (v.property p)
    have hw : star (weight X u p) = weight X u p := Complex.conj_ofReal _
    simpa only [star_mul, star_sub, hw, mul_comm] using h⟩
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext <;> exact star_add _ _
  map_smul' r a := by
    apply Subtype.ext
    apply Prod.ext
    · change star (r • a.val.1) = r • star a.val.1
      rw [star_smul, star_trivial]
    · change star (r • a.val.2) = r • star a.val.2
      rw [star_smul, star_trivial]

private theorem conjugateLinear_norm (v : graph X u) :
    ‖conjugateLinear X u v‖ = ‖v‖ := by
  change ‖(star v.val.1, star v.val.2)‖ = ‖v.val‖
  simp only [Prod.norm_def, norm_star]

@[expose] def conjugate : graph X u →L[ℝ] graph X u :=
  (conjugateLinear X u).mkContinuous 1 (fun v => by
    rw [conjugateLinear_norm, one_mul])

theorem conjugate_norm (v : graph X u) : ‖conjugate X u v‖ = ‖v‖ :=
  conjugateLinear_norm X u v

theorem conjugate_physical (v : graph X u) (x : X) :
    physical X u (conjugate X u v) x = star (physical X u v x) := rfl

theorem conjugate_involutive : Function.Involutive (conjugate X u) := by
  intro v
  apply physical_injective X u
  ext x
  rw [conjugate_physical, conjugate_physical, star_star]

theorem conjugate_smul (z : ℂ) (v : graph X u) :
    conjugate X u (z • v) = star z • conjugate X u v := by
  apply physical_injective X u
  ext x
  simp only [conjugate_physical, map_smul, BoundedContinuousFunction.coe_smul,
    smul_eq_mul, star_mul]
  exact mul_comm _ _

end LeanShared.BoundedHolderSpace

namespace LeanShared.SmoothHolderTestSpaces
open SmoothSupportedManifoldCore DyadicCompletion
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [CompactSpace M]
  (u : ℝ) (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u) (V : Set M)

private theorem graph_core_conjugation (c : core (E := E) V) :
    BoundedHolderSpace.conjugate M u (holderCore u holder V c) =
      holderCore u holder V (SmoothSupportedManifoldCore.conjugate V c) := by
  apply BoundedHolderSpace.physical_injective M u
  ext x
  rw [BoundedHolderSpace.conjugate_physical]
  rfl

theorem mapsTo_space (v : space u holder V) :
    BoundedHolderSpace.conjugate M u v.val ∈ space u holder V := by
  refine (coreMap_dense u holder V).induction_on
    (p := fun z => BoundedHolderSpace.conjugate M u z.val ∈ space u holder V) v
    (((holderCore u holder V).range.isClosed_topologicalClosure).preimage
      ((BoundedHolderSpace.conjugate M u).continuous.comp continuous_subtype_val)) ?_
  intro c
  change BoundedHolderSpace.conjugate M u (holderCore u holder V c) ∈ _
  rw [graph_core_conjugation]
  exact (holderCore u holder V).range.le_topologicalClosure ⟨_, rfl⟩

@[expose] def conjugateLinear : space u holder V →ₗ[ℝ] space u holder V where
  toFun v := ⟨BoundedHolderSpace.conjugate M u v.val, mapsTo_space u holder V v⟩
  map_add' a b := Subtype.ext ((BoundedHolderSpace.conjugate M u).map_add a.val b.val)
  map_smul' r a := Subtype.ext ((BoundedHolderSpace.conjugate M u).map_smul r a.val)

@[expose] def conjugate : space u holder V →L[ℝ] space u holder V :=
  (conjugateLinear u holder V).mkContinuous 1 (fun v => by
    change ‖BoundedHolderSpace.conjugate M u v.val‖ ≤ 1 * ‖v.val‖
    rw [BoundedHolderSpace.conjugate_norm, one_mul])

theorem conjugate_norm (v : space u holder V) : ‖conjugate u holder V v‖ = ‖v‖ :=
  BoundedHolderSpace.conjugate_norm M u v.val

theorem physical_conjugate (v : space u holder V) (x : M) :
    physical u holder V (conjugate u holder V v) x = star (physical u holder V v x) :=
  BoundedHolderSpace.conjugate_physical M u v.val x

theorem conjugate_coreMap (c : core (E := E) V) :
    conjugate u holder V (coreMap u holder V c) =
      coreMap u holder V (SmoothSupportedManifoldCore.conjugate V c) :=
  Subtype.ext (graph_core_conjugation u holder V c)

theorem conjugate_involutive : Function.Involutive (conjugate u holder V) := by
  intro v
  apply physical_injective u holder V
  ext x
  rw [physical_conjugate, physical_conjugate, star_star]

theorem conjugate_smul (z : ℂ) (v : space u holder V) :
    conjugate u holder V (z • v) = star z • conjugate u holder V v :=
  Subtype.ext (BoundedHolderSpace.conjugate_smul M u z v.val)

theorem view_conjugate (v : space u holder V) (x : M) :
    view u holder V (conjugate u holder V v) x = star (view u holder V v x) :=
  physical_conjugate u holder V v x

theorem includeFull_conjugate (v : space u holder V) :
    includeFull u holder V (conjugate u holder V v) =
      conjugate u holder univ (includeFull u holder V v) := by
  apply physical_injective u holder univ
  ext x
  rw [include_physical, physical_conjugate, physical_conjugate, include_physical]

end LeanShared.SmoothHolderTestSpaces
