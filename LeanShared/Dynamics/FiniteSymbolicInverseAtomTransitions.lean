module

public import LeanShared.Dynamics.FiniteSymbolicTimeReversal

/-! The inverse unstable raw-atom Markov inclusion follows by reversing
the literal directed graph and transposing the actual cylinder brackets.
The finite classifiers are transported exactly, rather than replaced by
an independently chosen inverse coding.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct
open RectangleFourWayRefinement FiniteClosedRefinement
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

@[expose] def reverseCylinder (code : Path R → X) (i : A) :
    rectangle (reverseCode code) i ≃ rectangle code i where
  toFun x := ⟨x.val, (reverseCode_rectangle code i) ▸ x.property⟩
  invFun x := ⟨x.val, (reverseCode_rectangle code i).symm ▸ x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def reverseBracket (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (i : A) (p : rectangle (reverseCode code) i × rectangle (reverseCode code) i) :
    rectangle (reverseCode code) i :=
  (reverseCylinder code i).symm (bracket i (reverseCylinder code i p.2, reverseCylinder code i p.1))

@[expose] def reverseClassifierIndex : A ⊕ ((A × A) × Bool) → A ⊕ ((A × A) × Bool)
  | .inl i => .inl i
  | .inr (ij, kind) => .inr (ij, !kind)

omit [TopologicalSpace A] [MetricSpace X] in
theorem reverseClassifierIndex_involutive (k : A ⊕ ((A × A) × Bool)) :
    reverseClassifierIndex (reverseClassifierIndex k) = k := by
  cases k with
  | inl i => rfl
  | inr k => rcases k with ⟨ij, kind⟩; cases kind <;> rfl

omit [MetricSpace X] in
theorem reverse_stableHit (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (i j : A) (x : rectangle (reverseCode code) i) :
    StableHit (reverseBracket code bracket i)
      {z : rectangle (reverseCode code) i | z.val ∈ rectangle (reverseCode code) j} x ↔
    UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} (reverseCylinder code i x) := by
  constructor
  · rintro ⟨z, inside, equation⟩
    refine ⟨reverseCylinder code i z, (reverseCode_rectangle code j) ▸ inside, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : rectangle (reverseCode code) i => z.val) equation
  · rintro ⟨z, inside, equation⟩
    refine ⟨(reverseCylinder code i).symm z, (reverseCode_rectangle code j).symm ▸ inside, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : rectangle code i => z.val) equation

omit [MetricSpace X] in
theorem reverse_unstableHit (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (i j : A) (x : rectangle (reverseCode code) i) :
    UnstableHit (reverseBracket code bracket i)
      {z : rectangle (reverseCode code) i | z.val ∈ rectangle (reverseCode code) j} x ↔
    StableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} (reverseCylinder code i x) := by
  constructor
  · rintro ⟨z, inside, equation⟩
    refine ⟨reverseCylinder code i z, (reverseCode_rectangle code j) ▸ inside, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : rectangle (reverseCode code) i => z.val) equation
  · rintro ⟨z, inside, equation⟩
    refine ⟨(reverseCylinder code i).symm z, (reverseCode_rectangle code j).symm ▸ inside, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : rectangle code i => z.val) equation

omit [MetricSpace X] in
theorem reverse_codedClassifiers (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (k : A ⊕ ((A × A) × Bool)) :
    codedClassifiers (reverseCode code) (reverseBracket code bracket) k =
      codedClassifiers code bracket (reverseClassifierIndex k) := by
  cases k with
  | inl i => exact reverseCode_rectangle code i
  | inr k =>
    rcases k with ⟨⟨i, j⟩, kind⟩
    ext x
    cases kind
    · constructor
      · rintro ⟨hx, hit⟩
        exact ⟨(reverseCode_rectangle code i) ▸ hx, (reverse_stableHit code bracket i j ⟨x, hx⟩).mp hit⟩
      · rintro ⟨hx, hit⟩
        have hx' : x ∈ rectangle (reverseCode code) i := (reverseCode_rectangle code i).symm ▸ hx
        exact ⟨hx', (reverse_stableHit code bracket i j ⟨x, hx'⟩).mpr hit⟩
    · constructor
      · rintro ⟨hx, hit⟩
        exact ⟨(reverseCode_rectangle code i) ▸ hx, (reverse_unstableHit code bracket i j ⟨x, hx⟩).mp hit⟩
      · rintro ⟨hx, hit⟩
        have hx' : x ∈ rectangle (reverseCode code) i := (reverseCode_rectangle code i).symm ▸ hx
        exact ⟨hx', (reverse_unstableHit code bracket i j ⟨x, hx'⟩).mpr hit⟩

omit [MetricSpace X] in
theorem reverse_codedAtom (code : Path R → X)
    (bracket : ∀ i : A, rectangle code i × rectangle code i → rectangle code i)
    (status : (A ⊕ ((A × A) × Bool)) → Bool) :
    atom (codedClassifiers (reverseCode code) (reverseBracket code bracket))
      (fun k => status (reverseClassifierIndex k)) = atom (codedClassifiers code bracket) status := by
  ext x
  rw [mem_atom_iff, mem_atom_iff]
  constructor
  · intro pattern k
    have result := pattern (reverseClassifierIndex k)
    rwa [reverse_codedClassifiers, reverseClassifierIndex_involutive] at result
  · intro pattern k
    rw [reverse_codedClassifiers]
    exact pattern (reverseClassifierIndex k)

/-- Exact inverse unstable Markov inclusion for the same raw atoms as
the forward theorem, obtained by reversing their actual graph coding. -/
theorem raw_atom_unstable_inverse (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
    (c ε : ℝ) (nonnegativeε : 0 ≤ ε)
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
    (source target : (A ⊕ ((A × A) × Bool)) → Bool)
    (x y : X) (insideX : x ∈ atom (codedClassifiers code bracket) source)
    (insideY : y ∈ atom (codedClassifiers code bracket) source)
    (imageX : T.symm x ∈ atom (codedClassifiers code bracket) target)
    (unstable : ∀ n : ℕ,
      dist ((T.symm : X → X)^[n] y) ((T.symm : X → X)^[n] x) ≤ 2 * ε) :
    T.symm y ∈ atom (codedClassifiers code bracket) target ∧
      ∀ n : ℕ, dist ((T.symm : X → X)^[n] (T.symm y))
        ((T.symm : X → X)^[n] (T.symm x)) ≤ 2 * ε := by
  have reverseExpansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c ∧
      dist ((T.symm.symm : X → X)^[n] x) ((T.symm.symm : X → X)^[n] y) ≤ c) → x = y := by
    intro x y close
    exact expansive x y (fun n => ⟨(close n).2, (close n).1⟩)
  have reverseBounds (i : A) (p : rectangle (reverseCode code) i × rectangle (reverseCode code) i) :
      ProductRelation T.symm (2 * ε) p.1.val p.2.val (reverseBracket code bracket i p).val := by
    intro n
    exact ⟨(bounds i (reverseCylinder code i p.2, reverseCylinder code i p.1) n).2,
      (bounds i (reverseCylinder code i p.2, reverseCylinder code i p.1) n).1⟩
  have reverseIdempotent (i : A) (x : rectangle (reverseCode code) i) :
      reverseBracket code bracket i (x, x) = x := by
    apply Subtype.ext
    exact congrArg (fun z : rectangle code i => z.val) (idempotent i (reverseCylinder code i x))
  have reverseBand (i : A) (x y u v : rectangle (reverseCode code) i) :
      reverseBracket code bracket i (reverseBracket code bracket i (x, y),
        reverseBracket code bracket i (u, v)) = reverseBracket code bracket i (x, v) := by
    apply Subtype.ext
    exact congrArg (fun z : rectangle code i => z.val) (band i (reverseCylinder code i v) (reverseCylinder code i u)
      (reverseCylinder code i y) (reverseCylinder code i x))
  have result := raw_atom_stable_forward T.symm center (reverseCode code) c ε nonnegativeε reverseExpansive
    small (reverseCode_near T center code ε near) (reverseCode_intertwines T code intertwines)
    (reverseBracket code bracket) reverseBounds reverseIdempotent reverseBand
    (fun k => source (reverseClassifierIndex k)) (fun k => target (reverseClassifierIndex k)) x y
    (by rwa [reverse_codedAtom]) (by rwa [reverse_codedAtom]) (by rwa [reverse_codedAtom]) unstable
  rwa [reverse_codedAtom] at result

end LeanShared.BilateralShadowingCoding
