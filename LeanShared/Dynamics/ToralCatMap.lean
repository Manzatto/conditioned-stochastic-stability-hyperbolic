module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp

/-! The actual compact two-dimensional toral cat map, with its inverse,
real linear lift, and dense periodic points. This module constructs the
map without assuming Anosov or HL data. Smooth quotient charts, tangent
hyperbolicity and topological mixing are separate geometric proofs. -/

public noncomputable section
namespace LeanShared.ToralCatMap
open Set Function

abbrev Torus := UnitAddCircle × UnitAddCircle

@[expose] def map {G : Type*} [AddCommGroup G] (z : G × G) : G × G :=
  (z.1 + z.1 + z.2, z.1 + z.2)

@[expose] def inverse {G : Type*} [AddCommGroup G] (z : G × G) : G × G :=
  (z.1 - z.2, z.2 + z.2 - z.1)

theorem inverse_map {G : Type*} [AddCommGroup G] (z : G × G) : inverse (map z) = z := by
  ext <;> dsimp only [map, inverse] <;> abel

theorem map_inverse {G : Type*} [AddCommGroup G] (z : G × G) : map (inverse z) = z := by
  ext <;> dsimp only [map, inverse] <;> abel

@[expose] def equiv (G : Type*) [AddCommGroup G] : G × G ≃ G × G where
  toFun := map
  invFun := inverse
  left_inv := inverse_map
  right_inv := map_inverse

@[expose] def homeomorph : Torus ≃ₜ Torus where
  toEquiv := equiv UnitAddCircle
  continuous_toFun := by change Continuous (map (G := UnitAddCircle)); unfold map; fun_prop
  continuous_invFun := by change Continuous (inverse (G := UnitAddCircle)); unfold inverse; fun_prop

@[expose] def quotient (z : ℝ × ℝ) : Torus := (z.1, z.2)

theorem quotient_map (z : ℝ × ℝ) : quotient (map z) = map (quotient z) := by
  ext <;> simp only [quotient, map, AddCircle.coe_add]

theorem quotient_iterate (n : ℕ) (z : ℝ × ℝ) :
    quotient ((map (G := ℝ))^[n] z) = (map (G := UnitAddCircle))^[n] (quotient z) :=
  (show Semiconj quotient (map (G := ℝ)) (map (G := UnitAddCircle)) from quotient_map).iterate_right n z

/-- Every point in a finite torsion subgroup is a genuine periodic point
of this concrete invertible map. -/
theorem mem_periodic_of_torsion (n : ℕ) (positive : 0 < n) (z : Torus)
    (first : n • z.1 = 0) (second : n • z.2 = 0) :
    z ∈ periodicPts (map (G := UnitAddCircle)) := by
  let S : Set UnitAddCircle := {x | n • x = 0}
  have finiteS : S.Finite := AddCircle.finite_torsion 1 positive
  let finitePair := (finiteS.prod finiteS).fintype
  let f : (S ×ˢ S) → (S ×ˢ S) := fun x =>
    ⟨map x.val, by
      rcases x.property with ⟨hx, hy⟩
      change n • x.val.1 = 0 at hx
      change n • x.val.2 = 0 at hy
      change n • (x.val.1 + x.val.1 + x.val.2) = 0 ∧ n • (x.val.1 + x.val.2) = 0
      simp only [nsmul_add, hx, hy, zero_add, and_self]⟩
  have injective : Injective f := by
    intro x y same
    apply Subtype.ext
    exact (equiv UnitAddCircle).injective (congrArg Subtype.val same)
  let x : S ×ˢ S := ⟨z, first, second⟩
  obtain ⟨p, positiveP, periodic⟩ := injective.mem_periodicPts x
  refine ⟨p, positiveP, ?_⟩
  exact periodic.map (g := Subtype.val) (show Semiconj Subtype.val f map from fun _ => rfl)

theorem rational_mem_periodic (q r : ℚ) :
    (((q : ℝ) : UnitAddCircle), ((r : ℝ) : UnitAddCircle)) ∈
      periodicPts (map (G := UnitAddCircle)) := by
  have torsion (a : ℚ) : a.den • ((a : ℝ) : UnitAddCircle) = 0 := by
    have order : addOrderOf ((a : ℝ) : UnitAddCircle) = a.den := by
      simpa only [mul_one] using AddCircle.addOrderOf_coe_rat (p := (1 : ℝ)) (q := a)
    rw [← order]
    exact addOrderOf_nsmul_eq_zero _
  apply mem_periodic_of_torsion (q.den * r.den) (Nat.mul_pos q.pos r.pos)
  · change (q.den * r.den) • ((q : ℝ) : UnitAddCircle) = 0
    rw [Nat.mul_comm, mul_smul, torsion, smul_zero]
  · change (q.den * r.den) • ((r : ℝ) : UnitAddCircle) = 0
    rw [mul_smul, torsion, smul_zero]

/-- Periodic density is proved for the literal cat map, independently of
the general hyperbolic periodic-specification theorem. -/
theorem dense_periodic : Dense (periodicPts (homeomorph : Torus → Torus)) := by
  have surjective : Surjective (fun x : ℝ => (x : UnitAddCircle)) :=
    QuotientAddGroup.mk_surjective
  have denseCircle : DenseRange (fun q : ℚ => ((q : ℝ) : UnitAddCircle)) :=
    surjective.denseRange.comp Rat.denseRange_cast (AddCircle.continuous_mk' 1)
  have densePairs : Dense (range (Prod.map
      (fun q : ℚ => ((q : ℝ) : UnitAddCircle))
      (fun q : ℚ => ((q : ℝ) : UnitAddCircle)))) := denseCircle.prodMap denseCircle
  apply densePairs.mono
  rintro _ ⟨⟨q, r⟩, rfl⟩
  exact rational_mem_periodic q r

theorem closure_periodic_eq_univ :
    closure (periodicPts (homeomorph : Torus → Torus)) = univ := dense_periodic.closure_eq

end LeanShared.ToralCatMap
