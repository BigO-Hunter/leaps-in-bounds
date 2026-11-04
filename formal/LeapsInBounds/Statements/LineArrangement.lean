module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic

/-!
# Arrangements of lines in the affine plane

Formal statements of bounds on the number of combinatorial types of
arrangements of `n` lines in the real affine plane, and of those in general
position (no two lines parallel and no three through a point).

The combinatorial type of an arrangement is given by its covectors: for each
point of the plane, the vector of signs saying which side of each line the
point is on (or that it's on the line). Two arrangements have the same type
when the lines of one can be renumbered, and their two sides swapped, so that
the covectors become those of the other. This is the usual notion of
combinatorial equivalence (isomorphism of the oriented matroids, or of the cell
decompositions of the plane), and it identifies mirror images. For lines in
general position, it's the equivalence of OEIS A090338: the lines can be
numbered so that the order of crossings along each line is the same.

OEIS A241600 counts arrangements that need not be in general position up to
rigid isotopy (moving the lines continuously without changing the incidences),
and its known terms were computed as combinatorial types. Isotopic
arrangements have the same type, so a lower bound on the number of types is
also a lower bound on the number of isotopy classes.

A certificate for `affine-line-arrangements-{n}` with lower bound `N` must
prove `LowerBound n N`, and one with upper bound `N` must prove
`UpperBound n N`. For `affine-line-arrangements-general-position-{n}`, they
are `GeneralLowerBound n N` and `GeneralUpperBound n N`.

This file is trusted: changing it changes what every certificate means.
-/

@[expose] public section

namespace LeapsInBounds.LineArrangement

/-- The line `a x + b y = c`, with `a` and `b` not both zero. -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nondegenerate : a ≠ 0 ∨ b ≠ 0

/-- The side of the line `l` that the point `p` is on: `0` on the line, and
`1` or `-1` on either side. -/
noncomputable def Line.side (l : Line) (p : ℝ × ℝ) : SignType :=
  SignType.sign (l.a * p.1 + l.b * p.2 - l.c)

/-- An arrangement of `n` distinct lines. -/
structure Arrangement (n : ℕ) where
  line : Fin n → Line
  distinct : ∀ i j, i ≠ j → ∃ p : ℝ × ℝ, (line i).side p = 0 ∧ (line j).side p ≠ 0

/-- The covectors of an arrangement: the sign vectors of all points. -/
def Arrangement.covectors {n : ℕ} (A : Arrangement n) : Set (Fin n → SignType) :=
  Set.range fun p i => (A.line i).side p

/-- `A` and `B` have the same combinatorial type: renumbering the lines of `A`
by `σ` and swapping the sides of the lines `i` with `ε i = -1` turns its
covectors into those of `B`. -/
def Equivalent {n : ℕ} (A B : Arrangement n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∃ ε : Fin n → SignType, (∀ i, ε i ≠ 0) ∧
    B.covectors = (fun v i => ε i * v (σ i)) '' A.covectors

/-- No two lines of `A` are parallel and no three go through a point. -/
def Arrangement.IsGeneral {n : ℕ} (A : Arrangement n) : Prop :=
  (∀ i j, i ≠ j → ∃ p : ℝ × ℝ, (A.line i).side p = 0 ∧ (A.line j).side p = 0) ∧
  ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    ¬∃ p : ℝ × ℝ, (A.line i).side p = 0 ∧ (A.line j).side p = 0 ∧ (A.line k).side p = 0

/-- At least `N` combinatorial types of arrangements of `n` lines satisfy `P`:
there are `N` such arrangements, no two of the same type. -/
def AtLeast {n : ℕ} (P : Arrangement n → Prop) (N : ℕ) : Prop :=
  ∃ A : Fin N → Arrangement n, (∀ i, P (A i)) ∧ ∀ i j, i ≠ j → ¬Equivalent (A i) (A j)

/-- At most `N` combinatorial types of arrangements of `n` lines satisfy `P`:
among any `N + 1` such arrangements, two have the same type. -/
def AtMost {n : ℕ} (P : Arrangement n → Prop) (N : ℕ) : Prop :=
  ∀ A : Fin (N + 1) → Arrangement n, (∀ i, P (A i)) → ∃ i j, i ≠ j ∧ Equivalent (A i) (A j)

/-- There are at least `N` combinatorial types of arrangements of `n` lines. -/
def LowerBound (n N : ℕ) : Prop := AtLeast (n := n) (fun _ => True) N

/-- There are at most `N` combinatorial types of arrangements of `n` lines. -/
def UpperBound (n N : ℕ) : Prop := AtMost (n := n) (fun _ => True) N

/-- There are at least `N` combinatorial types of arrangements of `n` lines in
general position. -/
def GeneralLowerBound (n N : ℕ) : Prop := AtLeast (n := n) Arrangement.IsGeneral N

/-- There are at most `N` combinatorial types of arrangements of `n` lines in
general position. -/
def GeneralUpperBound (n N : ℕ) : Prop := AtMost (n := n) Arrangement.IsGeneral N

/-- Sanity check on the definitions: a lower bound never exceeds an upper bound. -/
theorem AtLeast.le_of_atMost {n : ℕ} {P : Arrangement n → Prop} {m N : ℕ}
    (hl : AtLeast P m) (hu : AtMost P N) : m ≤ N := by
  by_contra h
  obtain ⟨A, hP, hA⟩ := hl
  obtain ⟨i, j, hij, he⟩ := hu (fun k => A (Fin.castLE (by omega) k)) (fun k => hP _)
  exact hA _ _ (fun h' => hij (Fin.castLE_injective _ h')) he

theorem LowerBound.le_of_upperBound {n m N : ℕ} (hl : LowerBound n m)
    (hu : UpperBound n N) : m ≤ N :=
  AtLeast.le_of_atMost hl hu

theorem GeneralLowerBound.le_of_generalUpperBound {n m N : ℕ} (hl : GeneralLowerBound n m)
    (hu : GeneralUpperBound n N) : m ≤ N :=
  AtLeast.le_of_atMost hl hu

end LeapsInBounds.LineArrangement
