module

public import LeanShared.Dynamics.FiniteSymbolicUnstableHitTransport
public import LeanShared.Dynamics.LocalRectangleAtomRefinement

/-! Literal cylinder classifiers and their raw-atom Markov inclusion.
The dynamical inclusion is derived from symbolic splicing; no Markov
property is an input.  Proper regularization is a subsequent step.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
open RectangleFourWayRefinement FiniteClosedRefinement
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

/-- Base, stable-hit, and unstable-hit classifiers for literal cylinders. -/
@[expose] def codedClassifiers (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i) :
    A ⊕ ((A × A) × Bool) → Set X
  | .inl i => rectangle code i
  | .inr ((i, j), false) => {x | ∃ hx : x ∈ rectangle code i,
      StableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨x, hx⟩}
  | .inr ((i, j), true) => {x | ∃ hx : x ∈ rectangle code i,
      UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨x, hx⟩}

omit [TopologicalSpace A] [MetricSpace X] in
theorem mem_codedStable (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (i j : A) (x : X) (hx : x ∈ rectangle code i) :
    x ∈ codedClassifiers code bracket (.inr ((i, j), false)) ↔
      StableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨x, hx⟩ := by
  constructor
  · rintro ⟨_, hit⟩
    exact hit
  · exact fun hit => ⟨hx, hit⟩

omit [TopologicalSpace A] [MetricSpace X] in
theorem mem_codedUnstable (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (i j : A) (x : X) (hx : x ∈ rectangle code i) :
    x ∈ codedClassifiers code bracket (.inr ((i, j), true)) ↔
      UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨x, hx⟩ := by
  constructor
  · rintro ⟨_, hit⟩
    exact hit
  · exact fun hit => ⟨hx, hit⟩

variable (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (c ε : ℝ)
    (nonnegativeε : 0 ≤ ε)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 4 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (intertwines : ∀ a, code (shift R a) = T (code a))
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (bounds : ∀ i p, ProductRelation T (2 * ε) p.1.val p.2.val (bracket i p).val)
    (idempotent : ∀ i (x : rectangle code i), bracket i (x, x) = x)
    (band : ∀ i (x y u v : rectangle code i),
      bracket i (bracket i (x, y), bracket i (u, v)) = bracket i (x, v))
include nonnegativeε expansive small near intertwines bounds idempotent band

/-- All finite classifier memberships propagate on a stable atom slice. -/
theorem stable_classifier_membership_forward (x y : X)
    (same : ∀ k, x ∈ codedClassifiers code bracket k ↔ y ∈ codedClassifiers code bracket k)
    (stable : ∀ n : ℕ, dist ((T : X → X)^[n] y) ((T : X → X)^[n] x) ≤ 2 * ε)
    (k : A ⊕ ((A × A) × Bool)) :
    T x ∈ codedClassifiers code bracket k ↔ T y ∈ codedClassifiers code bracket k := by
  have base (i : A) : x ∈ rectangle code i ↔ y ∈ rectangle code i := same (.inl i)
  have targetBase (i : A) : T x ∈ rectangle code i ↔ T y ∈ rectangle code i :=
    stable_base_membership_forward T center code c ε nonnegativeε expansive small near intertwines
      x y base stable i
  have targetStable : ∀ n : ℕ,
      dist ((T : X → X)^[n] (T y)) ((T : X → X)^[n] (T x)) ≤ 2 * ε := by
    intro n
    simpa only [Function.iterate_succ_apply] using stable (n + 1)
  have sourceUnstable (i j : A) (hx : x ∈ rectangle code i) (hy : y ∈ rectangle code i) :
      UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨x, hx⟩ ↔
        UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨y, hy⟩ :=
    (mem_codedUnstable code bracket i j x hx).symm.trans
      ((same (.inr ((i, j), true))).trans (mem_codedUnstable code bracket i j y hy))
  cases k with
  | inl i => exact targetBase i
  | inr k =>
    rcases k with ⟨⟨i, j⟩, kind⟩
    by_cases insideX : T x ∈ rectangle code i
    · have insideY := (targetBase i).mp insideX
      cases kind
      · rw [mem_codedStable code bracket i j (T x) insideX,
          mem_codedStable code bracket i j (T y) insideY]
        exact stableHit_iff_of_forward_close T c (2 * ε) (by linarith) expansive (by linarith)
          (rectangle code i) (bracket i) (bounds i) (idempotent i) (band i)
          {z : rectangle code i | z.val ∈ rectangle code j} ⟨T x, insideX⟩ ⟨T y, insideY⟩ targetStable
      · rw [mem_codedUnstable code bracket i j (T x) insideX,
          mem_codedUnstable code bracket i j (T y) insideY]
        constructor
        · exact unstableHit_forward_imp T center code c ε nonnegativeε expansive small near intertwines
            bracket bounds idempotent band x y base sourceUnstable i j insideX insideY
        · exact unstableHit_forward_imp T center code c ε nonnegativeε expansive small near intertwines
            bracket bounds idempotent band y x (fun a => (base a).symm)
            (fun a b hy hx => (sourceUnstable a b hx hy).symm) i j insideY insideX
    · have insideY : T y ∉ rectangle code i := fun hy => insideX ((targetBase i).mpr hy)
      cases kind <;>
        exact iff_of_false (fun ⟨hx, _⟩ => insideX hx) (fun ⟨hy, _⟩ => insideY hy)

/-- The exact finite membership atoms have the forward stable Markov
inclusion, directly from their literal finite-graph cylinder provenance. -/
theorem raw_atom_stable_forward (source target : (A ⊕ ((A × A) × Bool)) → Bool)
    (x y : X) (insideX : x ∈ atom (codedClassifiers code bracket) source)
    (insideY : y ∈ atom (codedClassifiers code bracket) source)
    (imageX : T x ∈ atom (codedClassifiers code bracket) target)
    (stable : ∀ n : ℕ, dist ((T : X → X)^[n] y) ((T : X → X)^[n] x) ≤ 2 * ε) :
    T y ∈ atom (codedClassifiers code bracket) target ∧
      ∀ n : ℕ, dist ((T : X → X)^[n] (T y)) ((T : X → X)^[n] (T x)) ≤ 2 * ε := by
  refine ⟨(mem_atom_iff _ target (T y)).mpr (fun k => ?_), ?_⟩
  · exact (stable_classifier_membership_forward T center code c ε nonnegativeε expansive small near
      intertwines bracket bounds idempotent band x y
      (atom_membership_agrees _ source x y insideX insideY) stable k).symm.trans
        ((mem_atom_iff _ target (T x)).mp imageX k)
  · intro n
    simpa only [Function.iterate_succ_apply] using stable (n + 1)

end LeanShared.BilateralShadowingCoding
