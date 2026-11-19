import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-!
# The block construction

The integer parameter in this development is the cube root of the parameter
in the paper. Thus edge probability is D(i,j)^3/n, the large-set threshold
is n/D(i,j), and the weak-set threshold is n/D(i,j)^24.
Thresholds are written as integer inequalities with denominators cleared.
-/

open Finset

namespace Erdos1111

abbrev Vertex (r n : ℕ) := Fin r × Fin n
abbrev Param (r : ℕ) := Fin r → Fin r → ℕ

variable {r n : ℕ}

/-- Read a parameter in the order of increasing block index. -/
def strength (D : Param r) (i j : Fin r) : ℕ :=
  D (min i j) (max i j)

lemma strength_comm (D : Param r) (i j : Fin r) : strength D i j = strength D j i := by
  simp [strength, min_comm i j, max_comm i j]

/-- The number of vertices of a finite set in block i. -/
def load (X : Finset (Vertex r n)) (i : Fin r) : ℕ :=
  (X.filter fun v => v.1 = i).card

lemma load_mono {X Y : Finset (Vertex r n)} (hXY : X ⊆ Y) (i : Fin r) :
    load X i ≤ load Y i := by
  exact card_le_card (filter_subset_filter _ hXY)

/-- A block pair is weak if at least one side is below the weak-set threshold. -/
def Weak (D : Param r) (X : Finset (Vertex r n)) (i j : Fin r) : Prop :=
  strength D i j ^ 24 * min (load X i) (load X j) ≤ n

instance (D : Param r) (X : Finset (Vertex r n)) (i j : Fin r) :
    Decidable (Weak D X i j) := by
  unfold Weak
  infer_instance

lemma weak_comm (D : Param r) (X : Finset (Vertex r n)) (i j : Fin r) :
    Weak D X i j ↔ Weak D X j i := by
  rw [Weak, Weak, strength_comm D i j, min_comm (load X i) (load X j)]

/-- The spanning graph consisting of the weak edges inside X. -/
def weakGraph (D : Param r) (H : SimpleGraph (Vertex r n))
    (X : Finset (Vertex r n)) : SimpleGraph (Vertex r n) where
  Adj u v := H.Adj u v ∧ u ∈ X ∧ v ∈ X ∧ Weak D X u.1 v.1
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, (weak_comm D X _ _).1 h.2.2.2⟩
  loopless := by
    constructor
    intro u h
    exact H.loopless.irrefl u h.1

@[simp] theorem weakGraph_adj (D : Param r) (H : SimpleGraph (Vertex r n))
    (X : Finset (Vertex r n)) (u v : Vertex r n) :
    (weakGraph D H X).Adj u v ↔ H.Adj u v ∧ u ∈ X ∧ v ∈ X ∧ Weak D X u.1 v.1 :=
  Iff.rfl

/-- (S) Every weak-edge graph has average degree less than three on X. -/
def GoodS (D : Param r) (H : SimpleGraph (Vertex r n)) : Prop := by
  classical
  exact ∀ X : Finset (Vertex r n), X.Nonempty →
    2 * (weakGraph D H X).edgeFinset.card < 3 * X.card

/-- (L) Two large subsets of different blocks have an edge between them. -/
def GoodL (D : Param r) (H : SimpleGraph (Vertex r n)) : Prop :=
  ∀ (i j : Fin r), i < j → ∀ (U V : Finset (Vertex r n)),
    (∀ v ∈ U, v.1 = i) → (∀ v ∈ V, v.1 = j) →
    n ≤ strength D i j * U.card → n ≤ strength D i j * V.card →
    ∃ u ∈ U, ∃ v ∈ V, H.Adj u v

/-- All edges cross between blocks. -/
def Cross (H : SimpleGraph (Vertex r n)) : Prop :=
  ∀ ⦃u v⦄, H.Adj u v → u.1 ≠ v.1

/-- Each unordered pair is one random coordinate. Within a block its weight is zero. -/
noncomputable def edgeProb (D : Param r) (n : ℕ) : Sym2 (Vertex r n) → ℝ :=
  Sym2.lift ⟨fun u v => if u.1 = v.1 then 0 else (strength D u.1 v.1 : ℝ)^3 / n,
    by
      intro u v
      dsimp only
      by_cases huv : u.1 = v.1
      · simp [huv]
      · simp [huv, Ne.symm huv, strength_comm D u.1 v.1]⟩

lemma edgeProb_apply_cross (D : Param r) (n : ℕ) (u v : Vertex r n)
    (h : u.1 ≠ v.1) :
    edgeProb D n s(u, v) = (strength D u.1 v.1 : ℝ)^3 / n := by
  simp [edgeProb, h]

lemma edgeProb_apply_same (D : Param r) (n : ℕ) (u v : Vertex r n)
    (h : u.1 = v.1) : edgeProb D n s(u, v) = 0 := by
  simp [edgeProb, h]

/-- Convert a sample of the Boolean coordinates into a simple graph. -/
def sampleGraph (ω : Sym2 (Vertex r n) → Bool) : SimpleGraph (Vertex r n) where
  Adj u v := u.1 ≠ v.1 ∧ ω s(u, v) = true
  symm := by
    constructor
    intro u v h
    exact ⟨Ne.symm h.1, by rw [Sym2.eq_swap]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem sampleGraph_adj (ω : Sym2 (Vertex r n) → Bool) (u v : Vertex r n) :
    (sampleGraph ω).Adj u v ↔ u.1 ≠ v.1 ∧ ω s(u, v) = true :=
  Iff.rfl

theorem sampleGraph_cross (ω : Sym2 (Vertex r n) → Bool) : Cross (sampleGraph ω) := by
  intro u v h
  exact h.1

end Erdos1111
