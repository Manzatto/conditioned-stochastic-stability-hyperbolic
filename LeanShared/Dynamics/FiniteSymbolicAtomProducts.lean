module

public import LeanShared.Dynamics.FiniteSymbolicCodedBracketRefinement

/-! Exact classifier atoms inherit the product structure of the literal
cylinder rectangles.  Compatibility on overlaps is proved from the
common expansivity scale, and both hit classifiers recover membership
in every other cylinder.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ExpansiveLocalProduct RectangleFourWayRefinement FiniteClosedRefinement
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

omit [TopologicalSpace A] in
theorem codedAtom_bracket_mem (T : X ≃ₜ X) (code : Path R → X) (c δ : ℝ)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (bounds : ∀ i p, ProductRelation T δ p.1.val p.2.val (bracket i p).val)
    (idempotent : ∀ i (x : rectangle code i), bracket i (x, x) = x)
    (band : ∀ i (x y u v : rectangle code i),
      bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v))
    (status : (A ⊕ ((A × A) × Bool)) → Bool) (x y : X)
    (insideX : x ∈ atom (codedClassifiers code bracket) status)
    (insideY : y ∈ atom (codedClassifiers code bracket) status)
    (i : A) (hx : x ∈ rectangle code i) (hy : y ∈ rectangle code i) :
    (bracket i (⟨x, hx⟩, ⟨y, hy⟩)).val ∈ atom (codedClassifiers code bracket) status := by
  let z := bracket i (⟨x, hx⟩, ⟨y, hy⟩)
  have same (k) := atom_membership_agrees (codedClassifiers code bracket) status x y insideX insideY k
  have compatible (a b : A) (u v : X) (hua : u ∈ rectangle code a) (hva : v ∈ rectangle code a)
      (hub : u ∈ rectangle code b) (hvb : v ∈ rectangle code b) :
      (bracket a (⟨u, hua⟩, ⟨v, hva⟩)).val = (bracket b (⟨u, hub⟩, ⟨v, hvb⟩)).val :=
    bracket_overlap T c δ expansive small _ _ (bracket a) (bracket b) (bounds a) (bounds b) u v hua hva hub hvb
  have both (j : A) (u : rectangle code i) :
      (StableHit (bracket i) {v : rectangle code i | v.val ∈ rectangle code j} u ∧
        UnstableHit (bracket i) {v : rectangle code i | v.val ∈ rectangle code j} u) ↔
      u.val ∈ rectangle code j :=
    both_hits_iff (bracket i) (idempotent i) (band i) _
      (overlap_isRectangle (rectangle code) bracket compatible i j) u
  have base (j : A) : z.val ∈ rectangle code j ↔ x ∈ rectangle code j := by
    have stableSame := stableHit_bracket (bracket i) (idempotent i) (band i)
      {v : rectangle code i | v.val ∈ rectangle code j} ⟨x, hx⟩ ⟨y, hy⟩
    have unstableSame := unstableHit_bracket (bracket i) (idempotent i) (band i)
      {v : rectangle code i | v.val ∈ rectangle code j} ⟨x, hx⟩ ⟨y, hy⟩
    have sourceSame : UnstableHit (bracket i) {v : rectangle code i | v.val ∈ rectangle code j} ⟨y, hy⟩ ↔
        UnstableHit (bracket i) {v : rectangle code i | v.val ∈ rectangle code j} ⟨x, hx⟩ :=
      (mem_codedUnstable code bracket i j y hy).symm.trans
        ((same (.inr ((i, j), true))).symm.trans (mem_codedUnstable code bracket i j x hx))
    exact (both j z).symm.trans ((and_congr stableSame (unstableSame.trans sourceSame)).trans (both j ⟨x, hx⟩))
  have pattern (k) : z.val ∈ codedClassifiers code bracket k ↔ x ∈ codedClassifiers code bracket k := by
    cases k with
    | inl j => exact base j
    | inr k =>
      rcases k with ⟨⟨a, b⟩, kind⟩
      by_cases hxa : x ∈ rectangle code a
      · have hya : y ∈ rectangle code a := (same (.inl a)).mp hxa
        have hza : z.val ∈ rectangle code a := (base a).mpr hxa
        have equal : (⟨z.val, hza⟩ : rectangle code a) = bracket a (⟨x, hxa⟩, ⟨y, hya⟩) :=
          Subtype.ext (compatible i a x y hx hy hxa hya)
        cases kind
        · rw [mem_codedStable code bracket a b z.val hza, mem_codedStable code bracket a b x hxa, equal]
          exact stableHit_bracket (bracket a) (idempotent a) (band a) _ ⟨x, hxa⟩ ⟨y, hya⟩
        · rw [mem_codedUnstable code bracket a b z.val hza, mem_codedUnstable code bracket a b x hxa, equal]
          exact (unstableHit_bracket (bracket a) (idempotent a) (band a) _ ⟨x, hxa⟩ ⟨y, hya⟩).trans
            ((mem_codedUnstable code bracket a b y hya).symm.trans
              ((same (.inr ((a, b), true))).symm.trans (mem_codedUnstable code bracket a b x hxa)))
      · have hza : z.val ∉ rectangle code a := fun hz => hxa ((base a).mp hz)
        cases kind <;>
          exact iff_of_false (fun ⟨hz, _⟩ => hza hz) (fun ⟨hx', _⟩ => hxa hx')
  exact (mem_atom_iff _ status z.val).mpr
    (fun k => (pattern k).trans ((mem_atom_iff _ status x).mp insideX k))

omit [TopologicalSpace A] in
/-- Every exact atom has an actual product point with the same bound as
the original cylinder brackets. -/
theorem codedAtom_product (T : X ≃ₜ X) (code : Path R → X) (onto : Surjective code) (c δ : ℝ)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 2 * δ ≤ c)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (bounds : ∀ i p, ProductRelation T δ p.1.val p.2.val (bracket i p).val)
    (idempotent : ∀ i (x : rectangle code i), bracket i (x, x) = x)
    (band : ∀ i (x y u v : rectangle code i),
      bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v))
    (status : (A ⊕ ((A × A) × Bool)) → Bool) (x y : X)
    (insideX : x ∈ atom (codedClassifiers code bracket) status)
    (insideY : y ∈ atom (codedClassifiers code bracket) status) :
    ∃ z ∈ atom (codedClassifiers code bracket) status, ProductRelation T δ x y z := by
  obtain ⟨a, coded⟩ := onto x
  have hx : x ∈ rectangle code (a.val 0) := ⟨a, rfl, coded⟩
  have hy : y ∈ rectangle code (a.val 0) :=
    (atom_membership_agrees _ status x y insideX insideY (.inl (a.val 0))).mp hx
  exact ⟨(bracket (a.val 0) (⟨x, hx⟩, ⟨y, hy⟩)).val,
    codedAtom_bracket_mem T code c δ expansive small bracket bounds idempotent band status x y
      insideX insideY (a.val 0) hx hy, bounds _ _⟩

end LeanShared.BilateralShadowingCoding
