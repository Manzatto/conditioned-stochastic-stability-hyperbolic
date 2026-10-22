module

public import LeanShared.Dynamics.RectangleRefinementTopology

/-! The constructed global local bracket induces total compatible
brackets on small rectangles.  Their stable/unstable hit sets are closed
actual classifiers, inherit the appropriate bracket coordinate, and meet
simultaneously exactly on the overlap of the two rectangles.
-/

public noncomputable section
namespace LeanShared.ExpansiveLocalProduct
open Set Function RectangleFourWayRefinement
open scoped Topology
variable {X : Type*} [MetricSpace X] {η : ℝ}

/-- Restrict the common local bracket to a small rectangle. -/
@[expose] def restrictedBracket (bracket : NearbyPairs (X := X) η → X) (R : Set X)
    (rectangle : IsLocalRectangle bracket R)
    (small : ∀ x ∈ R, ∀ y ∈ R, dist x y < η) : R × R → R :=
  fun p => ⟨bracket ⟨(p.1.val, p.2.val), small _ p.1.property _ p.2.property⟩,
    rectangle _ p.1.property _ p.2.property _⟩

variable (bracket : NearbyPairs (X := X) η → X) (R : Set X)
    (rectangle : IsLocalRectangle bracket R)
    (small : ∀ x ∈ R, ∀ y ∈ R, dist x y < η)

theorem restrictedBracket_continuous (continuous : Continuous bracket) :
    Continuous (restrictedBracket bracket R rectangle small) := by
  apply Continuous.subtype_mk
  apply continuous.comp
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)

theorem restrictedBracket_idempotent
    (idempotent : ∀ (x : X) (h : dist x x < η), bracket ⟨(x, x), h⟩ = x) (x : R) :
    restrictedBracket bracket R rectangle small (x, x) = x :=
  Subtype.ext (idempotent _ _)

theorem restrictedBracket_band (band : ConditionalBand bracket) (x y u v : R) :
    restrictedBracket bracket R rectangle small
        (restrictedBracket bracket R rectangle small (x, y),
          restrictedBracket bracket R rectangle small (u, v)) =
      restrictedBracket bracket R rectangle small (x, v) := by
  apply Subtype.ext
  exact band _ _ _ _ rfl rfl

/-- Stable-hit classifier in the ambient core, confined to the base rectangle. -/
@[expose] def stableClassifier (S : Set X) : Set X :=
  (Subtype.val : R → X) '' {x : R |
    StableHit (restrictedBracket bracket R rectangle small) {z : R | z.val ∈ S} x}

/-- Unstable-hit classifier in the ambient core. -/
@[expose] def unstableClassifier (S : Set X) : Set X :=
  (Subtype.val : R → X) '' {x : R |
    UnstableHit (restrictedBracket bracket R rectangle small) {z : R | z.val ∈ S} x}

theorem stableClassifier_subset (S : Set X) : stableClassifier bracket R rectangle small S ⊆ R := by
  rintro x ⟨z, _, rfl⟩
  exact z.property

theorem unstableClassifier_subset (S : Set X) : unstableClassifier bracket R rectangle small S ⊆ R := by
  rintro x ⟨z, _, rfl⟩
  exact z.property

theorem mem_stableClassifier (S : Set X) (x : X) (inside : x ∈ R) :
    x ∈ stableClassifier bracket R rectangle small S ↔
      StableHit (restrictedBracket bracket R rectangle small) {z : R | z.val ∈ S} ⟨x, inside⟩ := by
  constructor
  · rintro ⟨z, hit, equal⟩
    have same : z = ⟨x, inside⟩ := Subtype.ext equal
    exact same ▸ hit
  · intro hit
    exact ⟨⟨x, inside⟩, hit, rfl⟩

theorem mem_unstableClassifier (S : Set X) (x : X) (inside : x ∈ R) :
    x ∈ unstableClassifier bracket R rectangle small S ↔
      UnstableHit (restrictedBracket bracket R rectangle small) {z : R | z.val ∈ S} ⟨x, inside⟩ := by
  constructor
  · rintro ⟨z, hit, equal⟩
    have same : z = ⟨x, inside⟩ := Subtype.ext equal
    exact same ▸ hit
  · intro hit
    exact ⟨⟨x, inside⟩, hit, rfl⟩

variable (idempotent : ∀ (x : X) (h : dist x x < η), bracket ⟨(x, x), h⟩ = x)
    (band : ConditionalBand bracket)
include idempotent band

theorem stableClassifier_isClosed (continuous : Continuous bracket) (compact : IsCompact R)
    (S : Set X) (closed : IsClosed S) : IsClosed (stableClassifier bracket R rectangle small S) := by
  let : CompactSpace R := isCompact_iff_compactSpace.mp compact
  have hitClosed := stableHit_isClosed (restrictedBracket bracket R rectangle small)
    (restrictedBracket_idempotent bracket R rectangle small idempotent)
    (restrictedBracket_band bracket R rectangle small band)
    (restrictedBracket_continuous bracket R rectangle small continuous)
    {z : R | z.val ∈ S} (closed.preimage continuous_subtype_val)
  exact (hitClosed.isCompact.image continuous_subtype_val).isClosed

theorem unstableClassifier_isClosed (continuous : Continuous bracket) (compact : IsCompact R)
    (S : Set X) (closed : IsClosed S) : IsClosed (unstableClassifier bracket R rectangle small S) := by
  let : CompactSpace R := isCompact_iff_compactSpace.mp compact
  have hitClosed := unstableHit_isClosed (restrictedBracket bracket R rectangle small)
    (restrictedBracket_idempotent bracket R rectangle small idempotent)
    (restrictedBracket_band bracket R rectangle small band)
    (restrictedBracket_continuous bracket R rectangle small continuous)
    {z : R | z.val ∈ S} (closed.preimage continuous_subtype_val)
  exact (hitClosed.isCompact.image continuous_subtype_val).isClosed

theorem stableClassifier_inherit (S : Set X) (x y : X) (hx : x ∈ R) (hy : y ∈ R)
    (h : dist x y < η) :
    bracket ⟨(x, y), h⟩ ∈ stableClassifier bracket R rectangle small S ↔
      x ∈ stableClassifier bracket R rectangle small S := by
  rw [mem_stableClassifier _ _ _ _ _ _ (rectangle x hx y hy h),
    mem_stableClassifier _ _ _ _ _ _ hx]
  exact stableHit_bracket (restrictedBracket bracket R rectangle small)
    (restrictedBracket_idempotent bracket R rectangle small idempotent)
    (restrictedBracket_band bracket R rectangle small band) _ ⟨x, hx⟩ ⟨y, hy⟩

theorem unstableClassifier_inherit (S : Set X) (x y : X) (hx : x ∈ R) (hy : y ∈ R)
    (h : dist x y < η) :
    bracket ⟨(x, y), h⟩ ∈ unstableClassifier bracket R rectangle small S ↔
      y ∈ unstableClassifier bracket R rectangle small S := by
  rw [mem_unstableClassifier _ _ _ _ _ _ (rectangle x hx y hy h),
    mem_unstableClassifier _ _ _ _ _ _ hy]
  exact unstableHit_bracket (restrictedBracket bracket R rectangle small)
    (restrictedBracket_idempotent bracket R rectangle small idempotent)
    (restrictedBracket_band bracket R rectangle small band) _ ⟨x, hx⟩ ⟨y, hy⟩

/-- The two hit classifiers meet exactly on the actual rectangle overlap. -/
theorem classifiers_inter_eq (S : Set X) (otherRectangle : IsLocalRectangle bracket S) :
    stableClassifier bracket R rectangle small S ∩ unstableClassifier bracket R rectangle small S = R ∩ S := by
  have overlap : IsRectangle (restrictedBracket bracket R rectangle small) {z : R | z.val ∈ S} := by
    intro x hx y hy
    exact otherRectangle x.val hx y.val hy (small _ x.property _ y.property)
  ext x
  constructor
  · rintro ⟨stable, unstable⟩
    have inside := stableClassifier_subset bracket R rectangle small S stable
    have both := And.intro ((mem_stableClassifier bracket R rectangle small S x inside).mp stable)
      ((mem_unstableClassifier bracket R rectangle small S x inside).mp unstable)
    exact ⟨inside, (both_hits_iff (restrictedBracket bracket R rectangle small)
      (restrictedBracket_idempotent bracket R rectangle small idempotent)
      (restrictedBracket_band bracket R rectangle small band) _ overlap ⟨x, inside⟩).mp both⟩
  · rintro ⟨inside, otherInside⟩
    have both := (both_hits_iff (restrictedBracket bracket R rectangle small)
      (restrictedBracket_idempotent bracket R rectangle small idempotent)
      (restrictedBracket_band bracket R rectangle small band) _ overlap ⟨x, inside⟩).mpr otherInside
    exact ⟨(mem_stableClassifier bracket R rectangle small S x inside).mpr both.1,
      (mem_unstableClassifier bracket R rectangle small S x inside).mpr both.2⟩

end LeanShared.ExpansiveLocalProduct
