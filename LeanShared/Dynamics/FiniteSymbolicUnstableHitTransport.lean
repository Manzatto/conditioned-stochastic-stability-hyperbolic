module

public import LeanShared.Dynamics.FiniteSymbolicClassifierTransitions
public import LeanShared.Dynamics.CompatibleRectangleBrackets
import Mathlib.Tactic.Linarith

/-! The unstable-hit step of the Bowen--Sinai refinement.  Two incoming
coded branches, equality of the source classifiers, overlap compatibility,
and exact bracket covariance construct the required target hit.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit ExpansiveLocalProduct RectangleFourWayRefinement
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

theorem unstableHit_forward_imp (T : X ≃ₜ X) (center : A → X) (code : Path R → X)
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
    (x y : X)
    (sameBase : ∀ i, x ∈ rectangle code i ↔ y ∈ rectangle code i)
    (sameUnstable : ∀ i j (hx : x ∈ rectangle code i) (hy : y ∈ rectangle code i),
      UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨x, hx⟩ ↔
        UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨y, hy⟩)
    (i j : A) (insideX : T x ∈ rectangle code i) (insideY : T y ∈ rectangle code i)
    (hit : UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨T x, insideX⟩) :
    UnstableHit (bracket i) {z : rectangle code i | z.val ∈ rectangle code j} ⟨T y, insideY⟩ := by
  obtain ⟨v, insideVj, hitEquation⟩ := hit
  have unstableV : ∀ n : ℕ,
      dist ((T.symm : X → X)^[n] v.val) ((T.symm : X → X)^[n] (T x)) ≤ 2 * ε :=
    (unstable_iff_bracket T c (2 * ε) (by linarith) expansive (by linarith)
      (rectangle code i) (bracket i) (bounds i) v ⟨T x, insideX⟩).mpr hitEquation
  obtain ⟨a, codedA, nextA⟩ := exists_branch_to T code intertwines x i insideX
  have unstableA : ∀ n : ℕ,
      dist ((T.symm : X → X)^[n] v.val) ((T.symm : X → X)^[n] (T (code a))) ≤ 2 * ε := by
    simpa only [codedA] using unstableV
  have insideNext : v.val ∈ rectangle code (a.val 1) := nextA.symm ▸ v.property
  obtain ⟨az, codedZ, zeroZ, nextZ⟩ := unstable_branch_lift T center code c ε nonnegativeε expansive
    small near intertwines a v.val insideNext unstableA
  have targetZ : az.val 1 = i := nextZ.trans nextA
  let z := code az
  have imageZ : T z = v.val := by
    dsimp only [z]
    rw [codedZ, T.apply_symm_apply]
  have insideZ : z ∈ rectangle code (az.val 0) := ⟨az, rfl, rfl⟩
  have insideSourceX : x ∈ rectangle code (az.val 0) := by
    rw [zeroZ]
    exact ⟨a, rfl, codedA⟩
  have insideSourceY : y ∈ rectangle code (az.val 0) := (sameBase _).mp insideSourceX
  have imageZj : T z ∈ rectangle code j := imageZ.symm ▸ insideVj
  obtain ⟨other, codedOther, nextOther⟩ := exists_branch_to T code intertwines z j imageZj
  have insideOther : z ∈ rectangle code (other.val 0) := ⟨other, rfl, codedOther⟩
  have unstableZ : ∀ n : ℕ,
      dist ((T.symm : X → X)^[n] z) ((T.symm : X → X)^[n] x) ≤ 2 * ε := by
    have estimate := (weak_unstable_transition T center code c ε nonnegativeε expansive small near
      intertwines a v.val insideNext unstableA).2
    simpa only [z, ← codedZ, codedA] using estimate
  have sourceEquation : bracket (az.val 0) (⟨z, insideZ⟩, ⟨x, insideSourceX⟩) = ⟨z, insideZ⟩ :=
    (unstable_iff_bracket T c (2 * ε) (by linarith) expansive (by linarith)
      _ (bracket (az.val 0)) (bounds _) ⟨z, insideZ⟩ ⟨x, insideSourceX⟩).mp unstableZ
  have sourceHit : UnstableHit (bracket (az.val 0))
      {q : rectangle code (az.val 0) | q.val ∈ rectangle code (other.val 0)} ⟨x, insideSourceX⟩ :=
    ⟨⟨z, insideZ⟩, insideOther, sourceEquation⟩
  obtain ⟨u, insideOtherU, unstableU⟩ :=
    (sameUnstable (az.val 0) (other.val 0) insideSourceX insideSourceY).mp sourceHit
  let w := bracket (az.val 0) (⟨z, insideZ⟩, ⟨y, insideSourceY⟩)
  have productW := bounds (az.val 0) (⟨z, insideZ⟩, ⟨y, insideSourceY⟩)
  have replaceY : bracket (az.val 0) (⟨z, insideZ⟩, u) = w := by
    have identity := bracket_right (bracket (az.val 0)) (idempotent _) (band _)
      u ⟨y, insideSourceY⟩ ⟨z, insideZ⟩
    rw [unstableU] at identity
    exact identity
  have otherW : w.val ∈ rectangle code (other.val 0) := by
    have compatible := bracket_overlap T c (2 * ε) expansive (by linarith)
      (rectangle code (az.val 0)) (rectangle code (other.val 0)) (bracket _) (bracket _)
      (bounds _) (bounds _) z u.val insideZ u.property insideOther insideOtherU
    have identity : w.val = (bracket (other.val 0) (⟨z, insideOther⟩, ⟨u.val, insideOtherU⟩)).val :=
      (congrArg Subtype.val replaceY).symm.trans compatible
    rw [identity]
    exact (bracket (other.val 0) (⟨z, insideOther⟩, ⟨u.val, insideOtherU⟩)).property
  have stableW : ∀ n : ℕ,
      dist ((T : X → X)^[n] w.val) ((T : X → X)^[n] (code other)) ≤ 2 * ε := by
    simpa only [codedOther] using fun n => (productW n).1
  have imageWj : T w.val ∈ rectangle code j := by
    have estimate := (weak_stable_transition T center code c ε nonnegativeε expansive small near
      intertwines other w.val otherW stableW).1
    simpa only [nextOther] using estimate
  have targetY : T y ∈ rectangle code (az.val 1) := targetZ.symm ▸ insideY
  have imageProduct : ProductRelation T (2 * ε) (T z) (T y) (T w.val) :=
    (product_forward_on_branch T center code c ε nonnegativeε expansive small near
      intertwines az y w.val w.property targetY productW).2
  rw [imageZ] at imageProduct
  have imageEquation : T w.val = (bracket i (v, ⟨T y, insideY⟩)).val := by
    exact product_unique T c (2 * ε) expansive (by linarith) _ _ _ _ imageProduct (bounds i _)
  refine ⟨bracket i (v, ⟨T y, insideY⟩), ?_, ?_⟩
  · change (bracket i (v, ⟨T y, insideY⟩)).val ∈ rectangle code j
    rw [← imageEquation]
    exact imageWj
  · exact bracket_left (bracket i) (idempotent i) (band i) v ⟨T y, insideY⟩ ⟨T y, insideY⟩

end LeanShared.BilateralShadowingCoding
