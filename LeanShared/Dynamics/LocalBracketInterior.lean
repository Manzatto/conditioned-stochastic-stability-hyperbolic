module

public import LeanShared.Dynamics.CompatibleRectangleBrackets
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic.Linarith

/-! Ambient interiors and closures preserve sufficiently small local
rectangles.  The proof uses the constructed continuous local bracket,
including its conditional rectangular-band identity.  In particular
closure of interior is a proper rectangle, not an assumed Markov field.
-/

public noncomputable section
namespace LeanShared.ExpansiveLocalProduct
open Set Function
open scoped Topology
variable {X : Type*} [MetricSpace X] {η : ℝ}

/-- The rectangular-band identity whenever all indicated local products exist. -/
@[expose] def ConditionalBand (bracket : NearbyPairs (X := X) η → X) : Prop :=
  ∀ p q r : NearbyPairs (X := X) η, ∀ h : dist (bracket p) (bracket q) < η,
    p.val.1 = r.val.1 → q.val.2 = r.val.2 →
      bracket ⟨(bracket p, bracket q), h⟩ = bracket r

/-- A subset closed under every defined local product of its points. -/
@[expose] def IsLocalRectangle (bracket : NearbyPairs (X := X) η → X) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ h : dist x y < η, bracket ⟨(x, y), h⟩ ∈ S

theorem conditionalBand_of_product (T : X ≃ₜ X) (c δ : ℝ)
    (expansive : ∀ x y : X, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (small : 3 * δ ≤ c) (bracket : NearbyPairs (X := X) η → X)
    (bounds : ∀ p, ProductRelation T δ p.val.1 p.val.2 (bracket p)) :
    ConditionalBand bracket := by
  intro p q r h first second
  apply expansive
  intro j
  have outer := bounds ⟨(bracket p, bracket q), h⟩ j
  have left := bounds p j
  have right := bounds q j
  have target := bounds r j
  rw [first] at left
  rw [second] at right
  constructor
  · have reverse := target.1
    rw [dist_comm] at reverse
    have triangle₁ := dist_triangle
      ((T : X → X)^[j] (bracket ⟨(bracket p, bracket q), h⟩))
      ((T : X → X)^[j] (bracket p)) ((T : X → X)^[j] r.val.1)
    have triangle₂ := dist_triangle
      ((T : X → X)^[j] (bracket ⟨(bracket p, bracket q), h⟩))
      ((T : X → X)^[j] r.val.1) ((T : X → X)^[j] (bracket r))
    linarith
  · have reverse := target.2
    rw [dist_comm] at reverse
    have triangle₁ := dist_triangle
      ((T.symm : X → X)^[j] (bracket ⟨(bracket p, bracket q), h⟩))
      ((T.symm : X → X)^[j] (bracket q)) ((T.symm : X → X)^[j] r.val.2)
    have triangle₂ := dist_triangle
      ((T.symm : X → X)^[j] (bracket ⟨(bracket p, bracket q), h⟩))
      ((T.symm : X → X)^[j] r.val.2) ((T.symm : X → X)^[j] (bracket r))
    linarith

variable (positiveη : 0 < η) (bracket : NearbyPairs (X := X) η → X)
    (idempotent : ∀ (x : X) (h : dist x x < η), bracket ⟨(x, x), h⟩ = x)
    (band : ConditionalBand bracket)

include positiveη idempotent band

theorem bracket_left_inverse (p : NearbyPairs (X := X) η)
    (h : dist (bracket p) p.val.1 < η) : bracket ⟨(bracket p, p.val.1), h⟩ = p.val.1 := by
  let q : NearbyPairs (X := X) η := ⟨(p.val.1, p.val.1), by simpa only [dist_self] using positiveη⟩
  have hq : bracket q = p.val.1 := idempotent _ _
  have small : dist (bracket p) (bracket q) < η := hq.symm ▸ h
  have identity := band p q q small rfl rfl
  simpa only [hq] using identity

theorem bracket_right_inverse (p : NearbyPairs (X := X) η)
    (h : dist p.val.2 (bracket p) < η) : bracket ⟨(p.val.2, bracket p), h⟩ = p.val.2 := by
  let q : NearbyPairs (X := X) η := ⟨(p.val.2, p.val.2), by simpa only [dist_self] using positiveη⟩
  have hq : bracket q = p.val.2 := idempotent _ _
  have small : dist (bracket q) (bracket p) < η := hq.symm ▸ h
  have identity := band q p q small rfl rfl
  simpa only [hq] using identity

/-- The AMBIENT interior is a rectangle.  The proof locally reconstructs
each nearby point from its projections close to the two interior points. -/
theorem IsLocalRectangle.interior (continuous : Continuous bracket) (S : Set X)
    (rectangle : IsLocalRectangle bracket S)
    (small : ∀ x ∈ S, ∀ y ∈ S, dist x y < η) :
    IsLocalRectangle bracket (interior S) := by
  intro x hx y hy hxy
  let p : NearbyPairs (X := X) η := ⟨(x, y), hxy⟩
  let z := bracket p
  have insideZ : z ∈ S := rectangle x (interior_subset hx) y (interior_subset hy) hxy
  let U : Set X := {w | dist w x < η ∧ dist y w < η}
  have openU : IsOpen U := (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
    (isOpen_lt (continuous_const.dist continuous_id) continuous_const)
  have insideU : z ∈ U :=
    ⟨small z insideZ x (interior_subset hx), small y (interior_subset hy) z insideZ⟩
  let point : U := ⟨z, insideU⟩
  let left : U → X := fun w => bracket ⟨(w.val, x), w.property.1⟩
  let right : U → X := fun w => bracket ⟨(y, w.val), w.property.2⟩
  have continuousLeft : Continuous left := continuous.comp
    (Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const) _)
  have continuousRight : Continuous right := continuous.comp
    (Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _)
  have leftPoint : left point = x :=
    bracket_left_inverse positiveη bracket idempotent band p insideU.1
  have rightPoint : right point = y :=
    bracket_right_inverse positiveη bracket idempotent band p insideU.2
  let V : Set U := left ⁻¹' _root_.interior S ∩ right ⁻¹' _root_.interior S
  have openV : IsOpen V := (isOpen_interior.preimage continuousLeft).inter
    (isOpen_interior.preimage continuousRight)
  have insideV : point ∈ V := by
    change left point ∈ _root_.interior S ∧ right point ∈ _root_.interior S
    exact ⟨leftPoint.symm ▸ hx, rightPoint.symm ▸ hy⟩
  have imageInside : (Subtype.val : U → X) '' V ⊆ S := by
    rintro w ⟨v, hv, rfl⟩
    have leftInside : left v ∈ S := interior_subset hv.1
    have rightInside : right v ∈ S := interior_subset hv.2
    have close : dist (left v) (right v) < η := small _ leftInside _ rightInside
    let diagonal : NearbyPairs (X := X) η :=
      ⟨(v.val, v.val), by simpa only [dist_self] using positiveη⟩
    have identity := band ⟨(v.val, x), v.property.1⟩ ⟨(y, v.val), v.property.2⟩
      diagonal close rfl rfl
    have result : bracket ⟨(left v, right v), close⟩ = v.val :=
      identity.trans (idempotent _ _)
    exact result ▸ rectangle _ leftInside _ rightInside close
  exact interior_maximal imageInside (openU.isOpenMap_subtype_val _ openV) ⟨point, insideV, rfl⟩

omit positiveη idempotent band in
/-- Closure preservation uses the open domain of the local bracket. -/
theorem IsLocalRectangle.closure (continuous : Continuous bracket) (S : Set X)
    (rectangle : IsLocalRectangle bracket S) : IsLocalRectangle bracket (_root_.closure S) := by
  intro x hx y hy hxy
  let p : NearbyPairs (X := X) η := ⟨(x, y), hxy⟩
  let D : Set (X × X) := {p | dist p.1 p.2 < η}
  have openD : IsOpen D := isOpen_lt (continuous_fst.dist continuous_snd) continuous_const
  have openMap : IsOpenMap (Subtype.val : NearbyPairs (X := X) η → X × X) :=
    openD.isOpenMap_subtype_val
  have continuousVal : Continuous (Subtype.val : NearbyPairs (X := X) η → X × X) :=
    continuous_subtype_val
  let A : Set (NearbyPairs (X := X) η) := {q | q.val.1 ∈ S ∧ q.val.2 ∈ S}
  have base : p.val ∈ _root_.closure (S ×ˢ S) := by
    rw [closure_prod_eq]
    exact ⟨hx, hy⟩
  have nearbyClosure : p ∈ _root_.closure A := by
    change p ∈ _root_.closure ((Subtype.val : NearbyPairs (X := X) η → X × X) ⁻¹' (S ×ˢ S))
    have identity := openMap.preimage_closure_eq_closure_preimage continuousVal (S ×ˢ S)
    rw [← identity]
    exact base
  have imageInside : bracket '' A ⊆ S := by
    rintro w ⟨q, hq, rfl⟩
    exact rectangle _ hq.1 _ hq.2 q.property
  exact closure_mono imageInside
    (image_closure_subset_closure_image continuous ⟨p, nearbyClosure, rfl⟩)

/-- Closing the ambient interior gives a proper local rectangle. -/
theorem IsLocalRectangle.regularize (continuous : Continuous bracket) (S : Set X)
    (rectangle : IsLocalRectangle bracket S)
    (small : ∀ x ∈ S, ∀ y ∈ S, dist x y < η) :
    IsLocalRectangle bracket (_root_.closure (_root_.interior S)) :=
  IsLocalRectangle.closure bracket continuous _
    (IsLocalRectangle.interior positiveη bracket idempotent band continuous S rectangle small)

end LeanShared.ExpansiveLocalProduct
