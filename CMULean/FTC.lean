import Mathlib

/-!
# The Fundamental Theorem of Calculus, part (i), for strictly monotone functions

Everything lives in the namespace `FTC`, because current Mathlib already has a
top-level `Partition`.

Two lemmas are still `sorry`:
* `lowerSum_le_upperSum` (A5, cross comparison via common refinement)
* `hasDerivWithinAt_of_eps` (translating the ε–δ statement into Mathlib's `HasDerivWithinAt`)
-/

open Finset Set

namespace FTC

noncomputable section

private lemma le_div_of_mul_le {lo A c : ℝ} (hc : 0 < c) (h : lo * c ≤ A) : lo ≤ A / c := by
  have hne : c ≠ 0 := ne_of_gt hc
  have hcan : A / c * c = A := by field_simp
  refine le_of_mul_le_mul_right ?_ hc
  rw [hcan]; exact h

private lemma div_le_of_le_mul {A hi c : ℝ} (hc : 0 < c) (h : A ≤ hi * c) : A / c ≤ hi := by
  have hne : c ≠ 0 := ne_of_gt hc
  have hcan : A / c * c = A := by field_simp
  refine le_of_mul_le_mul_right ?_ hc
  rw [hcan]; exact h

private lemma mul_le_of_div_le {A c d : ℝ} (hc : 0 < c) (h : A / c ≤ d) : A ≤ d * c := by
  have hne : c ≠ 0 := ne_of_gt hc
  have hcan : A / c * c = A := by field_simp
  have h' := mul_le_mul_of_nonneg_right h hc.le
  rwa [hcan] at h'

/-! ## Section 0: partitions, sums, and two constructions -/

/-- A partition of `[a,b]`: `a = x 0 < x 1 < ... < x n = b`. Values of `x` beyond `n`
are irrelevant and unconstrained. -/
structure Partition (a b : ℝ) where
  n : ℕ
  x : ℕ → ℝ
  pos : 0 < n
  left : x 0 = a
  right : x n = b
  step : ∀ j < n, x j < x (j + 1)

namespace Partition

variable {a b : ℝ}

/-- The partition points increase along indices `≤ n`. -/
lemma mono (P : Partition a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) :
    P.x i ≤ P.x j := by
  revert hj
  induction hij with
  | refl => intro _; exact le_rfl
  | @step m hm ih =>
      intro hj
      have hmn : m < P.n := Nat.lt_of_succ_le hj
      exact (ih hmn.le).trans (P.step m hmn).le

lemma mem_Icc (P : Partition a b) {j : ℕ} (hj : j ≤ P.n) : P.x j ∈ Icc a b := by
  constructor
  · simpa [P.left] using P.mono (Nat.zero_le j) hj
  · simpa [P.right] using P.mono hj le_rfl

lemma width_nonneg (P : Partition a b) {j : ℕ} (hj : j < P.n) :
    0 ≤ P.x (j + 1) - P.x j :=
  sub_nonneg.mpr (P.step j hj).le

/-- The widths sum to `b - a`. -/
lemma sum_widths (P : Partition a b) :
    ∑ j ∈ range P.n, (P.x (j + 1) - P.x j) = b - a := by
  rw [Finset.sum_range_sub (fun j => P.x j) P.n, P.left, P.right]

/-- The mesh: the largest subinterval width. -/
def mesh (P : Partition a b) : ℝ :=
  (range P.n).sup' (nonempty_range_iff.mpr P.pos.ne') fun j => P.x (j + 1) - P.x j

lemma width_le_mesh (P : Partition a b) {j : ℕ} (hj : j < P.n) :
    P.x (j + 1) - P.x j ≤ P.mesh := by
  unfold mesh
  exact Finset.le_sup' (fun j => P.x (j + 1) - P.x j) (mem_range.mpr hj)

lemma mesh_le_iff (P : Partition a b) (δ : ℝ) :
    P.mesh ≤ δ ↔ ∀ j < P.n, P.x (j + 1) - P.x j ≤ δ := by
  unfold mesh
  rw [Finset.sup'_le_iff]
  simp [Finset.mem_range]

lemma mesh_nonneg (P : Partition a b) : 0 ≤ P.mesh :=
  le_trans (P.width_nonneg P.pos) (P.width_le_mesh P.pos)

/-- **A7a.** The uniform partition into `n` equal pieces. Its existence is what makes the
mesh → 0 condition non-vacuous, hence what makes the integral unique (gap G2). -/
def uniformPart (a b : ℝ) (n : ℕ) (hn : 0 < n) (hab : a < b) : Partition a b where
  n := n
  x := fun j => a + (j : ℝ) * ((b - a) / n)
  pos := hn
  left := by simp
  right := by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
    ring
  step := by
    intro j _
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hba : 0 < (b - a) / n := div_pos (sub_pos.mpr hab) hn'
    have : (j : ℝ) < (j : ℝ) + 1 := by linarith
    push_cast
    nlinarith [hba]

lemma mesh_uniformPart (n : ℕ) (hn : 0 < n) (hab : a < b) :
    (uniformPart a b n hn hab).mesh ≤ (b - a) / n := by
  rw [mesh_le_iff]
  intro j _
  have hwidth : (uniformPart a b n hn hab).x (j + 1) - (uniformPart a b n hn hab).x j
      = (b - a) / n := by
    simp only [uniformPart]
    push_cast
    ring
  rw [hwidth]

/-- **Append one interval on the right.** Given a partition of `[a,u]` and `u < v`, glue on
the single subinterval `[u,v]` to get a partition of `[a,v]`. This replaces the general
concatenation lemma; it is all that B3 needs. -/
def snoc {u v : ℝ} (P : Partition a u) (huv : u < v) : Partition a v where
  n := P.n + 1
  x := fun j => if j ≤ P.n then P.x j else v
  pos := Nat.succ_pos _
  left := by simp [Nat.zero_le, P.left]
  right := by simp
  step := by
    intro j hj
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
    · have h1 : j ≤ P.n := h.le
      have h2 : j + 1 ≤ P.n := Nat.succ_le_of_lt h
      simpa [h1, h2] using P.step j h
    · subst h
      have : ¬ (P.n + 1 ≤ P.n) := by omega
      simpa [this, P.right] using huv

end Partition

/-- A tagged partition: a partition together with a tag `t j ∈ [x j, x (j+1)]`. -/
structure Tagged (a b : ℝ) extends Partition a b where
  t : ℕ → ℝ
  tag_ge : ∀ j < n, x j ≤ t j
  tag_le : ∀ j < n, t j ≤ x (j + 1)

namespace Tagged

variable {a b : ℝ}

lemma tag_mem_Icc (P : Tagged a b) {j : ℕ} (hj : j < P.n) : P.t j ∈ Icc a b := by
  refine ⟨le_trans ?_ (P.tag_ge j hj), le_trans (P.tag_le j hj) ?_⟩
  · exact (P.toPartition.mem_Icc hj.le).1
  · exact (P.toPartition.mem_Icc (Nat.succ_le_of_lt hj)).2

end Tagged

variable {f : ℝ → ℝ} {a b : ℝ}

/-- A Riemann sum for an arbitrary tag choice. -/
def riemannSum (f : ℝ → ℝ) (P : Tagged a b) : ℝ :=
  ∑ j ∈ range P.n, f (P.t j) * (P.x (j + 1) - P.x j)

/-- The left-endpoint sum. For monotone increasing `f` this is the smallest Riemann sum
over the given partition — and, crucially, it *is* an honest Riemann sum (tag on the left),
so no separate Darboux theory is required. -/
def lowerSum (f : ℝ → ℝ) (P : Partition a b) : ℝ :=
  ∑ j ∈ range P.n, f (P.x j) * (P.x (j + 1) - P.x j)

/-- The right-endpoint sum. -/
def upperSum (f : ℝ → ℝ) (P : Partition a b) : ℝ :=
  ∑ j ∈ range P.n, f (P.x (j + 1)) * (P.x (j + 1) - P.x j)

/-- Tagging a partition with left endpoints. -/
def Partition.leftTagged (P : Partition a b) : Tagged a b where
  toPartition := P
  t := P.x
  tag_ge := fun _ _ => le_rfl
  tag_le := fun j hj => (P.step j hj).le

/-- Tagging a partition with right endpoints. -/
def Partition.rightTagged (P : Partition a b) : Tagged a b where
  toPartition := P
  t := fun j => P.x (j + 1)
  tag_ge := fun j hj => (P.step j hj).le
  tag_le := fun _ _ => le_rfl

lemma riemannSum_leftTagged (f : ℝ → ℝ) (P : Partition a b) :
    riemannSum f P.leftTagged = lowerSum f P := rfl

lemma riemannSum_rightTagged (f : ℝ → ℝ) (P : Partition a b) :
    riemannSum f P.rightTagged = upperSum f P := rfl

/-- Definition of the Riemann integral: mesh → 0 forces every tag choice to converge. -/
def IsRiemannIntegral (f : ℝ → ℝ) (a b : ℝ) (I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ P : Tagged a b, P.mesh ≤ δ → |riemannSum f P - I| < ε

/-! ## Section 1: the monotone estimates (A1, A2', A3) -/

section Monotone

variable (hf : MonotoneOn f (Icc a b))

/-- **A1.** A monotone function on `[a,b]` is bounded by its endpoint values. -/
lemma monotoneOn_bounds (hf : MonotoneOn f (Icc a b)) (hab : a ≤ b) {y : ℝ}
    (hy : y ∈ Icc a b) : f a ≤ f y ∧ f y ≤ f b :=
  ⟨hf (left_mem_Icc.mpr hab) hy hy.1, hf hy (right_mem_Icc.mpr hab) hy.2⟩

/-- **A2', lower half.** Any tag choice gives at least the left-endpoint sum. -/
lemma lowerSum_le_riemannSum (hf : MonotoneOn f (Icc a b)) (P : Tagged a b) :
    lowerSum f P.toPartition ≤ riemannSum f P := by
  refine Finset.sum_le_sum ?_
  intro j hj
  have hjn := mem_range.mp hj
  have hstep : f (P.x j) ≤ f (P.t j) :=
    hf (P.toPartition.mem_Icc hjn.le) (P.tag_mem_Icc hjn) (P.tag_ge j hjn)
  exact mul_le_mul_of_nonneg_right hstep (P.toPartition.width_nonneg hjn)

/-- **A2', upper half.** Any tag choice gives at most the right-endpoint sum. -/
lemma riemannSum_le_upperSum (hf : MonotoneOn f (Icc a b)) (P : Tagged a b) :
    riemannSum f P ≤ upperSum f P.toPartition := by
  refine Finset.sum_le_sum ?_
  intro j hj
  have hjn := mem_range.mp hj
  have hstep : f (P.t j) ≤ f (P.x (j + 1)) :=
    hf (P.tag_mem_Icc hjn) (P.toPartition.mem_Icc (Nat.succ_le_of_lt hjn)) (P.tag_le j hjn)
  exact mul_le_mul_of_nonneg_right hstep (P.toPartition.width_nonneg hjn)

lemma lowerSum_le_upperSum_same (hf : MonotoneOn f (Icc a b)) (P : Partition a b) :
    lowerSum f P ≤ upperSum f P := by
  have h := lowerSum_le_riemannSum hf P.leftTagged
  have h' := riemannSum_le_upperSum hf P.leftTagged
  rw [riemannSum_leftTagged] at h h'
  exact h'

/-- **A3 (telescoping oscillation bound).** The single quantitative engine of the whole
development: for monotone `f` the total oscillation collapses to `f b - f a`. -/
lemma upperSum_sub_lowerSum_le (hf : MonotoneOn f (Icc a b)) (P : Partition a b)
    {δ : ℝ} (hmesh : P.mesh ≤ δ) :
    upperSum f P - lowerSum f P ≤ δ * (f b - f a) := by
  have key : upperSum f P - lowerSum f P
      = ∑ j ∈ range P.n, (f (P.x (j + 1)) - f (P.x j)) * (P.x (j + 1) - P.x j) := by
    rw [upperSum, lowerSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have bound : ∀ j ∈ range P.n,
      (f (P.x (j + 1)) - f (P.x j)) * (P.x (j + 1) - P.x j)
        ≤ (f (P.x (j + 1)) - f (P.x j)) * δ := by
    intro j hj
    have hjn := mem_range.mp hj
    have hfdiff : 0 ≤ f (P.x (j + 1)) - f (P.x j) := by
      have := hf (P.mem_Icc hjn.le) (P.mem_Icc (Nat.succ_le_of_lt hjn)) (P.step j hjn).le
      linarith
    exact mul_le_mul_of_nonneg_left
      (le_trans (P.width_le_mesh hjn) hmesh) hfdiff
  calc upperSum f P - lowerSum f P
      = ∑ j ∈ range P.n, (f (P.x (j + 1)) - f (P.x j)) * (P.x (j + 1) - P.x j) := key
    _ ≤ ∑ j ∈ range P.n, (f (P.x (j + 1)) - f (P.x j)) * δ := Finset.sum_le_sum bound
    _ = (∑ j ∈ range P.n, (f (P.x (j + 1)) - f (P.x j))) * δ := by rw [Finset.sum_mul]
    _ = (f b - f a) * δ := by
        rw [Finset.sum_range_sub (fun j => f (P.x j)) P.n, P.left, P.right]
    _ = δ * (f b - f a) := by ring

/-- Crude bound used to get `BddAbove` for free — no refinement needed here (this is the
shortcut that lets A6 avoid depending on A5). -/
lemma lowerSum_le_const (hf : MonotoneOn f (Icc a b)) (hab : a < b) (P : Partition a b) :
    lowerSum f P ≤ f b * (b - a) := by
  have : lowerSum f P ≤ ∑ j ∈ range P.n, f b * (P.x (j + 1) - P.x j) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjn := mem_range.mp hj
    exact mul_le_mul_of_nonneg_right
      ((monotoneOn_bounds hf hab.le (P.mem_Icc hjn.le)).2) (P.width_nonneg hjn)
  calc lowerSum f P ≤ ∑ j ∈ range P.n, f b * (P.x (j + 1) - P.x j) := this
    _ = f b * (b - a) := by rw [← Finset.mul_sum, P.sum_widths]

end Monotone

/-! ## Section 2: constructing the integral (A5 – A8) -/

/-- **A5 (cross comparison).** Proof plan: let `R` be the common refinement of `P` and `Q`
(the partition whose point set is the union of the two point sets). The inductive step is
single-point insertion: adding a point `c ∈ (x j, x (j+1))` replaces the term
`f (x j) * (x (j+1) - x j)` by `f (x j) * (c - x j) + f c * (x (j+1) - c)`, which is larger
because `f (x j) ≤ f c`; dually for upper sums. Iterating gives
`lowerSum P ≤ lowerSum R ≤ upperSum R ≤ upperSum Q`, the middle inequality being
`lowerSum_le_upperSum_same`.

The obstruction is bookkeeping, not mathematics: inserting a point into an `ℕ`-indexed
partition forces a reindexing of the sum. -/
lemma lowerSum_le_upperSum (hf : MonotoneOn f (Icc a b)) (hab : a < b)
    (P Q : Partition a b) : lowerSum f P ≤ upperSum f Q := by
  sorry

/-- The set of all lower sums. -/
def lowerSums (f : ℝ → ℝ) (a b : ℝ) : Set ℝ := {y | ∃ P : Partition a b, y = lowerSum f P}

/-- **A6.** The integral, *as a function* (gap G1), with the degenerate convention
`integ f a a = 0` (gap G3). -/
def integ (f : ℝ → ℝ) (a b : ℝ) : ℝ := if a < b then sSup (lowerSums f a b) else 0

@[simp] lemma integ_self (f : ℝ → ℝ) (a : ℝ) : integ f a a = 0 := by simp [integ]

lemma lowerSums_nonempty (hab : a < b) : (lowerSums f a b).Nonempty :=
  ⟨lowerSum f (Partition.uniformPart a b 1 Nat.one_pos hab),
    Partition.uniformPart a b 1 Nat.one_pos hab, rfl⟩

lemma lowerSums_bddAbove (hf : MonotoneOn f (Icc a b)) (hab : a < b) :
    BddAbove (lowerSums f a b) := by
  refine ⟨f b * (b - a), ?_⟩
  rintro y ⟨P, rfl⟩
  exact lowerSum_le_const hf hab P

/-- **A6a, lower half.** -/
lemma lowerSum_le_integ (hf : MonotoneOn f (Icc a b)) (hab : a < b) (P : Partition a b) :
    lowerSum f P ≤ integ f a b := by
  rw [integ, if_pos hab]
  exact le_csSup (lowerSums_bddAbove hf hab) ⟨P, rfl⟩

/-- **A6a, upper half.** This is the only place A5 is used — and it propagates from here
to everything else. -/
lemma integ_le_upperSum (hf : MonotoneOn f (Icc a b)) (hab : a < b) (Q : Partition a b) :
    integ f a b ≤ upperSum f Q := by
  rw [integ, if_pos hab]
  refine csSup_le (lowerSums_nonempty hab) ?_
  rintro y ⟨P, rfl⟩
  exact lowerSum_le_upperSum hf hab P Q

/-- **A7.** Upper sums approach the integral from above. Proved by the uniform partition
plus the telescoping bound A3 — this is the `I_low = I_up` content of the outline, in the
form actually used later. -/
lemma exists_upperSum_le (hf : MonotoneOn f (Icc a b)) (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Partition a b, upperSum f P ≤ integ f a b + ε := by
  have hVnn : 0 ≤ f b - f a := by
    have h := monotoneOn_bounds hf hab.le (right_mem_Icc.mpr hab.le)
    linarith [h.1]
  have hba : (0 : ℝ) ≤ b - a := by linarith
  -- choose `n` with `(b - a) * (f b - f a) / n ≤ ε`
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) * (f b - f a) / ε)
  have hnpos : 0 < n := by
    by_contra hcon
    have hz : n = 0 := by omega
    rw [hz] at hn
    have h0 : 0 ≤ (b - a) * (f b - f a) / ε := div_nonneg (mul_nonneg hba hVnn) hε.le
    simp at hn
    linarith
  have hncast : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  refine ⟨Partition.uniformPart a b n hnpos hab, ?_⟩
  have h3 := upperSum_sub_lowerSum_le hf (Partition.uniformPart a b n hnpos hab)
    (Partition.mesh_uniformPart n hnpos hab)
  have hsmall : (b - a) / n * (f b - f a) ≤ ε := by
    rw [div_mul_eq_mul_div]
    refine div_le_of_le_mul hncast ?_
    have hmul := mul_le_of_div_le hε hn.le  -- `A ≤ n * ε`, goal wants `A ≤ ε * n`
    linarith [hmul]
  have hlow := lowerSum_le_integ hf hab (Partition.uniformPart a b n hnpos hab)
  linarith [h3, hsmall, hlow]

/-- **A8.** The integral defined in A6 really is the Riemann integral. -/
theorem isRiemannIntegral_integ (hf : MonotoneOn f (Icc a b)) (hab : a < b) :
    IsRiemannIntegral f a b (integ f a b) := by
  intro ε hε
  have hVnn : 0 ≤ f b - f a := by
    have h := monotoneOn_bounds hf hab.le (right_mem_Icc.mpr hab.le)
    linarith [h.1]
  -- G3's fix: the `+1` keeps δ well-defined even if `f b = f a`
  have hden : (0 : ℝ) < 2 * ((f b - f a) + 1) := by linarith
  refine ⟨ε / (2 * ((f b - f a) + 1)), div_pos hε hden, ?_⟩
  intro P hmesh
  have hL := lowerSum_le_riemannSum hf P
  have hU := riemannSum_le_upperSum hf P
  have hLI := lowerSum_le_integ hf hab P.toPartition
  have hIU := integ_le_upperSum hf hab P.toPartition
  have hosc := upperSum_sub_lowerSum_le hf P.toPartition hmesh
  -- `δ * (f b - f a) ≤ ε / 2`, proved without any `div_le_iff`-family lemma
  have hbound : ε / (2 * ((f b - f a) + 1)) * (f b - f a) ≤ ε / 2 := by
    rw [div_mul_eq_mul_div]
    refine div_le_of_le_mul hden ?_
    nlinarith [hε.le, hVnn]
  rw [abs_lt]
  constructor <;> linarith

/-- Uniqueness of the Riemann integral (gap G2: this is exactly where `uniformPart`,
i.e. A7a, is indispensable — without arbitrarily fine partitions the defining condition
would be vacuous and *every* real would be "the" integral). -/
theorem IsRiemannIntegral.unique (hab : a < b) {I I' : ℝ}
    (h : IsRiemannIntegral f a b I) (h' : IsRiemannIntegral f a b I') : I = I' := by
  by_contra hne
  have habs : 0 < |I - I'| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δ, hδ, hP⟩ := h (|I - I'| / 2) (by linarith)
  obtain ⟨δ', hδ', hP'⟩ := h' (|I - I'| / 2) (by linarith)
  have hmin : 0 < min δ δ' := lt_min hδ hδ'
  -- a uniform partition of small enough mesh exists (this is where A7a is essential)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / min δ δ')
  have hnpos : 0 < n := by
    by_contra hc
    have hz : n = 0 := by omega
    rw [hz] at hn
    have h0 : 0 ≤ (b - a) / min δ δ' := div_nonneg (by linarith) hmin.le
    simp at hn
    linarith
  have hncast : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hmesh : (Partition.uniformPart a b n hnpos hab).mesh ≤ min δ δ' := by
    refine le_trans (Partition.mesh_uniformPart n hnpos hab) ?_
    refine div_le_of_le_mul hncast ?_
    have hmul := mul_le_of_div_le hmin hn.le  -- `b - a ≤ n * min δ δ'`
    linarith [hmul]
  have h1 := hP (Partition.uniformPart a b n hnpos hab).leftTagged
    (le_trans hmesh (min_le_left _ _))
  have h2 := hP' (Partition.uniformPart a b n hnpos hab).leftTagged
    (le_trans hmesh (min_le_right _ _))
  obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
  obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
  -- both `I` and `I'` sit within `|I - I'|/2` of the same Riemann sum
  have hcontra : |I - I'| < 2 * (|I - I'| / 2) :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-! ## Section 3: the increment lemma (B3)

`snoc` sum identities, then the two-sided bound on `F v - F u`. -/

lemma lowerSum_snoc (f : ℝ → ℝ) {u v : ℝ} (P : Partition a u) (huv : u < v) :
    lowerSum f (P.snoc huv) = lowerSum f P + f u * (v - u) := by
  simp only [lowerSum, Partition.snoc]
  rw [Finset.sum_range_succ]
  have hmain : ∀ j ∈ range P.n,
      f (if j ≤ P.n then P.x j else v) *
        ((if j + 1 ≤ P.n then P.x (j + 1) else v) - (if j ≤ P.n then P.x j else v))
        = f (P.x j) * (P.x (j + 1) - P.x j) := by
    intro j hj
    have h1 : j ≤ P.n := (mem_range.mp hj).le
    have h2 : j + 1 ≤ P.n := Nat.succ_le_of_lt (mem_range.mp hj)
    simp [h1, h2]
  rw [Finset.sum_congr rfl hmain]
  have hlast : ¬ (P.n + 1 ≤ P.n) := by omega
  simp [hlast, P.right]  -- routine

lemma upperSum_snoc (f : ℝ → ℝ) {u v : ℝ} (P : Partition a u) (huv : u < v) :
    upperSum f (P.snoc huv) = upperSum f P + f v * (v - u) := by
  simp only [upperSum, Partition.snoc]
  rw [Finset.sum_range_succ]
  have hmain : ∀ j ∈ range P.n,
      f (if j + 1 ≤ P.n then P.x (j + 1) else v) *
        ((if j + 1 ≤ P.n then P.x (j + 1) else v) - (if j ≤ P.n then P.x j else v))
        = f (P.x (j + 1)) * (P.x (j + 1) - P.x j) := by
    intro j hj
    have h1 : j ≤ P.n := (mem_range.mp hj).le
    have h2 : j + 1 ≤ P.n := Nat.succ_le_of_lt (mem_range.mp hj)
    simp [h1, h2]
  rw [Finset.sum_congr rfl hmain]
  have hlast : ¬ (P.n + 1 ≤ P.n) := by omega
  simp [hlast, P.right]  -- routine

/-- The one-piece partition of `[u,v]`, used for the degenerate `u = a` cases. -/
lemma lowerSum_one (f : ℝ → ℝ) {u v : ℝ} (huv : u < v) :
    lowerSum f (Partition.uniformPart u v 1 Nat.one_pos huv) = f u * (v - u) := by
  simp [lowerSum, Partition.uniformPart]  -- routine

lemma upperSum_one (f : ℝ → ℝ) {u v : ℝ} (huv : u < v) :
    upperSum f (Partition.uniformPart u v 1 Nat.one_pos huv) = f v * (v - u) := by
  simp [upperSum, Partition.uniformPart]  -- routine

section Increment

variable (hf : MonotoneOn f (Icc a b))

/-- Restriction of the monotonicity hypothesis to an initial subinterval. -/
lemma mono_restrict (hf : MonotoneOn f (Icc a b)) {v : ℝ} (hvb : v ≤ b) :
    MonotoneOn f (Icc a v) :=
  hf.mono (Icc_subset_Icc le_rfl hvb)

/-- **B3, lower half.** -/
lemma integ_increment_lower (hf : MonotoneOn f (Icc a b)) {u v : ℝ}
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b) :
    f u * (v - u) ≤ integ f a v - integ f a u := by
  have hav : a < v := lt_of_le_of_lt hau huv
  have hmv : MonotoneOn f (Icc a v) := mono_restrict hf hvb
  rcases eq_or_lt_of_le hau with hua | hau'
  · -- degenerate case u = a, where `integ f a a = 0` (gap G3)
    subst hua
    have : lowerSum f (Partition.uniformPart a v 1 Nat.one_pos hav) ≤ integ f a v :=
      lowerSum_le_integ hmv hav _
    rw [lowerSum_one] at this
    simpa using this
  · -- generic case: extend an arbitrary partition of [a,u] by the interval [u,v]
    have hmu : MonotoneOn f (Icc a u) := mono_restrict hf (huv.le.trans hvb)
    have key : ∀ P : Partition a u, lowerSum f P ≤ integ f a v - f u * (v - u) := by
      intro P
      have h := lowerSum_le_integ hmv hav (P.snoc huv)
      rw [lowerSum_snoc] at h
      linarith
    have : integ f a u ≤ integ f a v - f u * (v - u) := by
      rw [integ, if_pos hau']
      refine csSup_le (lowerSums_nonempty hau') ?_
      rintro y ⟨P, rfl⟩
      exact key P
    linarith

/-- **B3, upper half.** -/
lemma integ_increment_upper (hf : MonotoneOn f (Icc a b)) {u v : ℝ}
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b) :
    integ f a v - integ f a u ≤ f v * (v - u) := by
  have hav : a < v := lt_of_le_of_lt hau huv
  have hmv : MonotoneOn f (Icc a v) := mono_restrict hf hvb
  rcases eq_or_lt_of_le hau with hua | hau'
  · subst hua
    have := integ_le_upperSum hmv hav (Partition.uniformPart a v 1 Nat.one_pos hav)
    rw [upperSum_one] at this
    simpa using this
  · have hmu : MonotoneOn f (Icc a u) := mono_restrict hf (huv.le.trans hvb)
    -- for every ε, an upper sum on [a,u] within ε of `integ f a u` (this is A7)
    have key : ∀ ε > 0, integ f a v ≤ (integ f a u + f v * (v - u)) + ε := by
      intro ε hεpos
      obtain ⟨P, hP⟩ := exists_upperSum_le hmu hau' hεpos
      have h := integ_le_upperSum hmv hav (P.snoc huv)
      rw [upperSum_snoc] at h
      linarith
    have := le_of_forall_pos_le_add key
    linarith

end Increment

/-! ## Section 4: the derivative (B4, B5, B6)

Stated as a single two-sided statement relative to `Icc a b` (gap G6): no endpoint case
split, and at `x = a` / `x = b` it automatically means the appropriate one-sided derivative.
The difference quotient is bounded by A2'-style endpoint values, then squeezed by continuity.
-/

/-- **B4 + B5 + B6, in explicit ε–δ form.** No filter machinery: the whole content is the
squeeze `f (min) ≤ quotient ≤ f (max)` coming from B3, closed off by continuity at `x`. -/
theorem integ_difference_quotient (hf : MonotoneOn f (Icc a b)) (hab : a < b)
    {x : ℝ} (hx : x ∈ Icc a b)
    (hcont : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Icc a b, |y - x| ≤ δ → |f y - f x| ≤ ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Icc a b, y ≠ x → |y - x| ≤ δ →
      |(integ f a y - integ f a x) / (y - x) - f x| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδy⟩ := hcont ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyx hclose
  have hfy : |f y - f x| ≤ ε := hδy y hy hclose
  rcases lt_or_gt_of_ne hyx with hlt | hgt
  · -- y < x : apply B3 with u = y, v = x, after rewriting the quotient over `x - y > 0`
    have hlow := integ_increment_lower hf hy.1 hlt hx.2
    have hupp := integ_increment_upper hf hy.1 hlt hx.2
    have hpos : 0 < x - y := sub_pos.mpr hlt
    have hswap : (integ f a y - integ f a x) / (y - x)
        = (integ f a x - integ f a y) / (x - y) := by
      rw [← neg_sub (integ f a x) (integ f a y), ← neg_sub x y, neg_div_neg_eq]
    rw [hswap]
    have h1 : f y ≤ (integ f a x - integ f a y) / (x - y) :=
      le_div_of_mul_le hpos (by linarith)
    have h2 : (integ f a x - integ f a y) / (x - y) ≤ f x :=
      div_le_of_le_mul hpos (by linarith)
    rw [abs_le] at hfy ⊢
    constructor <;> linarith [hfy.1, hfy.2]
  · -- x < y : apply B3 with u = x, v = y
    have hlow := integ_increment_lower hf hx.1 hgt hy.2
    have hupp := integ_increment_upper hf hx.1 hgt hy.2
    have hpos : 0 < y - x := sub_pos.mpr hgt
    have h1 : f x ≤ (integ f a y - integ f a x) / (y - x) :=
      le_div_of_mul_le hpos (by linarith)
    have h2 : (integ f a y - integ f a x) / (y - x) ≤ f y :=
      div_le_of_le_mul hpos (by linarith)
    rw [abs_le] at hfy ⊢
    constructor <;> linarith [hfy.1, hfy.2]

lemma hasDerivWithinAt_of_eps {F : ℝ → ℝ} {L x : ℝ} {s : Set ℝ}
    (h : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ s, y ≠ x → |y - x| ≤ δ →
      |(F y - F x) / (y - x) - L| ≤ ε) :
    HasDerivWithinAt F L s x := by
  sorry  -- routine

/-! ## Section 5: the two headline theorems -/

/-- **FTC (i), strictly increasing case.** `F x = ∫_a^x f` is differentiable within
`[a,b]` with derivative `f x` at every point. -/
theorem ftc_strictMono (hf : StrictMonoOn f (Icc a b)) (hab : a < b)
    {x : ℝ} (hx : x ∈ Icc a b)
    (hcont : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Icc a b, |y - x| ≤ δ → |f y - f x| ≤ ε) :
    HasDerivWithinAt (fun y => integ f a y) (f x) (Icc a b) x :=
  hasDerivWithinAt_of_eps (integ_difference_quotient hf.monotoneOn hab hx hcont)

/-- ...and `∫_a^b f` in the sense of A6 is the Riemann integral. -/
theorem ftc_strictMono_isIntegral (hf : StrictMonoOn f (Icc a b)) (hab : a < b) :
    IsRiemannIntegral f a b (integ f a b) :=
  isRiemannIntegral_integ hf.monotoneOn hab

/-- Negating the integrand negates the integral (used only for the decreasing case, C1). -/
theorem IsRiemannIntegral.neg {I : ℝ} (h : IsRiemannIntegral f a b I) :
    IsRiemannIntegral (fun t => -f t) a b (-I) := by
  intro ε hε
  obtain ⟨δ, hδ, hP⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hsum : riemannSum (fun t => -f t) P = -riemannSum f P := by
    simp [riemannSum, ← Finset.sum_neg_distrib]
  rw [hsum, show -riemannSum f P - -I = -(riemannSum f P - I) by ring, abs_neg]
  exact hP P hmesh

/-- **FTC (i), strictly decreasing case (C1).** Obtained for free from the increasing case
applied to `g = -f`; no integration theory is redone. -/
theorem ftc_strictAnti (hf : StrictAntiOn f (Icc a b)) (hab : a < b)
    {x : ℝ} (hx : x ∈ Icc a b)
    (hcont : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Icc a b, |y - x| ≤ δ → |f y - f x| ≤ ε) :
    HasDerivWithinAt (fun y => -(integ (fun t => -f t) a y)) (f x) (Icc a b) x := by
  have hg : StrictMonoOn (fun t => -f t) (Icc a b) := hf.neg
  have hgcont : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Icc a b, |y - x| ≤ δ →
      |(fun t => -f t) y - (fun t => -f t) x| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hy⟩ := hcont ε hε
    refine ⟨δ, hδ, fun y hyI hclose => ?_⟩
    show |(-f y) - (-f x)| ≤ ε
    rw [show (-f y) - (-f x) = -(f y - f x) by ring, abs_neg]
    exact hy y hyI hclose
  have hd := ftc_strictMono hg hab hx hgcont
  have := hd.neg
  -- only cancel the double negative in the derivative; full `simp` also rewrote the
  -- function into a form that no longer matched the goal
  simp only [neg_neg] at this
  exact this

/-- ...and the corresponding value really is the Riemann integral of `f`. -/
theorem ftc_strictAnti_isIntegral (hf : StrictAntiOn f (Icc a b)) (hab : a < b) :
    IsRiemannIntegral f a b (-(integ (fun t => -f t) a b)) := by
  have hg : StrictMonoOn (fun t => -f t) (Icc a b) := hf.neg
  have h := (isRiemannIntegral_integ hg.monotoneOn hab).neg
  simpa using h

end

end FTC
