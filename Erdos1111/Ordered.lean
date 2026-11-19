import Erdos1111.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max

namespace Erdos1111

open scoped BigOperators

section ParameterOrder

variable {r : ℕ}

/-- A numeric rank for increasing second index, then decreasing first index. -/
private def pairRank (p : Fin r × Fin r) : ℕ :=
  p.2.val * r + (r - p.1.val)

private theorem pairRank_lt {i j k l : Fin r}
    (h : j < l ∨ j = l ∧ k < i) :
    pairRank (i, j) < pairRank (k, l) := by
  rcases h with hjl | ⟨hjl, hki⟩
  · have hstep : (j.val + 1) * r ≤ l.val * r :=
      Nat.mul_le_mul_right r (Nat.succ_le_of_lt hjl)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    change j.val * r + (r - i.val) < l.val * r + (r - k.val)
    have hk := k.isLt
    omega
  · rw [← hjl]
    change j.val * r + (r - i.val) < j.val * r + (r - k.val)
    have hki' : k.val < i.val := hki
    have hi := i.isLt
    omega

/-- Any later pair has strength greater than the 24th power of an earlier strength. -/
def Ordered (D : Param r) : Prop :=
  ∀ i j k l : Fin r, i < j → k < l → (j < l ∨ j = l ∧ k < i) →
    strength D i j ^ 24 < strength D k l

private theorem strength_of_lt (D : Param r) {i j : Fin r} (h : i < j) :
    strength D i j = D i j := by
  simp [strength, min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]

/-- Parameters can be fixed independently of the block size, above any given lower bound. -/
theorem exists_ordered (m : ℕ) :
    ∃ D : Param r, Ordered D ∧ ∀ i j, m ≤ strength D i j := by
  let base := max m 2
  have hbase : 1 < base :=
    (show 1 < (2 : ℕ) by decide).trans_le (le_max_right m 2)
  let D : Param r := fun i j => base ^ (25 ^ pairRank (i, j))
  refine ⟨D, ?_, ?_⟩
  · intro i j k l hij hkl h
    rw [strength_of_lt D hij, strength_of_lt D hkl]
    change (base ^ (25 ^ pairRank (i, j))) ^ 24 < base ^ (25 ^ pairRank (k, l))
    rw [← pow_mul]
    apply Nat.pow_lt_pow_right hbase
    calc
      25 ^ pairRank (i, j) * 24 < 25 ^ pairRank (i, j) * 25 :=
        Nat.mul_lt_mul_of_pos_left (by decide) (by positivity)
      _ = 25 ^ (pairRank (i, j) + 1) := (pow_succ _ _).symm
      _ ≤ 25 ^ pairRank (k, l) :=
        Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt (pairRank_lt h))
  · intro i j
    change m ≤ base ^ (25 ^ pairRank (min i j, max i j))
    calc
      m ≤ base := le_max_left _ _
      _ = base ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega)
        (Nat.succ_le_of_lt (pow_pos (by decide : 0 < (25 : ℕ)) _))

end ParameterOrder

section GreedyColoring

/-- Greedy extension from a smaller set, avoiding the at most two neighbor colors. -/
private theorem colorable_three_of_small_neighborhoods {V : Type*}
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (hsmall : ∀ Y ⊆ X, Y.Nonempty → ∃ v ∈ Y, (Y.filter (G.Adj v)).card ≤ 2) :
    (G.induce (X : Set V)).Colorable 3 := by
  classical
  have recolor : ∀ Y : Finset V, Y ⊆ X →
      ∃ f : V → Fin 3, ∀ u ∈ Y, ∀ w ∈ Y, G.Adj u w → f u ≠ f w := by
    intro Y
    induction Y using Finset.strongInductionOn with
    | _ Y ih =>
      intro hYX
      by_cases hY : Y.Nonempty
      · obtain ⟨v, hv, hdeg⟩ := hsmall Y hYX hY
        obtain ⟨f, hf⟩ :=
          ih (Y.erase v) (Finset.erase_ssubset hv) ((Finset.erase_subset _ _).trans hYX)
        let neighbors := Y.filter (G.Adj v)
        let used := neighbors.image f
        have hused : used.card ≤ 2 := Finset.card_image_le.trans hdeg
        have hfresh : used.card < (Finset.univ : Finset (Fin 3)).card := by
          simpa using (show used.card < 3 by omega)
        obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hfresh
        have hav : ∀ w ∈ Y, G.Adj v w → c ≠ f w := by
          intro w hw hvw heq
          apply hc
          exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hvw⟩, heq.symm⟩
        refine ⟨Function.update f v c, ?_⟩
        intro u hu w hw huw
        by_cases huv : u = v
        · subst u
          simpa [Function.update_of_ne (Ne.symm (G.ne_of_adj huw))] using hav w hw huw
        · by_cases hwv : w = v
          · subst w
            simpa [Function.update_of_ne huv] using (hav u hu huw.symm).symm
          · simpa [Function.update_of_ne huv, Function.update_of_ne hwv] using
              hf u (Finset.mem_erase.mpr ⟨huv, hu⟩)
                 w (Finset.mem_erase.mpr ⟨hwv, hw⟩) huw
      · exact ⟨fun _ => 0, fun u hu => False.elim (hY ⟨u, hu⟩)⟩
  obtain ⟨f, hf⟩ := recolor X Finset.Subset.rfl
  exact ⟨SimpleGraph.Coloring.mk (fun v => f v) (fun {u v} h => hf u u.2 v v.2 h)⟩

end GreedyColoring

section Blocks

variable {r n : ℕ} {D : Param r} {H : SimpleGraph (Vertex r n)}

private theorem weak_mono {X Y : Finset (Vertex r n)} (hYX : Y ⊆ X)
    {i j : Fin r} (hweak : Weak D X i j) : Weak D Y i j := by
  unfold Weak at *
  exact (Nat.mul_le_mul_left _ (min_le_min (load_mono hYX i) (load_mono hYX j))).trans hweak

/-- Every weak-edge graph is three-colorable, by the sparsity bound on each subset. -/
private theorem weak_colorable (hS : GoodS D H) (X : Finset (Vertex r n)) :
    ((weakGraph D H X).induce (X : Set (Vertex r n))).Colorable 3 := by
  classical
  apply colorable_three_of_small_neighborhoods
  intro Y hYX hY
  let K := weakGraph D H Y
  have hz : ∀ v ∉ Y, K.degree v = 0 := by
    intro v hv
    apply (K.degree_eq_zero_iff_notMem_support v).mpr
    rintro ⟨w, hw⟩
    exact hv ((weakGraph_adj D H Y v w).mp hw).2.1
  have hsum : (∑ v ∈ Y, K.degree v) = 2 * K.edgeFinset.card := by
    rw [← K.sum_degrees_eq_twice_card_edges]
    exact Finset.sum_subset (Finset.subset_univ Y) (fun v _ hv => hz v hv)
  have hsmall : ∃ v ∈ Y, K.degree v ≤ 2 := by
    by_contra! hbad
    have hmin : 3 * Y.card ≤ ∑ v ∈ Y, K.degree v := calc
      3 * Y.card = ∑ _v ∈ Y, (3 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v hv => by have := hbad v hv; omega)
    have hbound : 2 * K.edgeFinset.card < 3 * Y.card := hS Y hY
    omega
  obtain ⟨v, hv, hdeg⟩ := hsmall
  refine ⟨v, hv, le_trans ?_ hdeg⟩
  rw [← K.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hwY, hadj⟩ := Finset.mem_filter.mp hw
  obtain ⟨he, _, _, hwk⟩ := (weakGraph_adj D H X v w).mp hadj
  exact (K.mem_neighborFinset v w).mpr
    ((weakGraph_adj D H Y v w).mpr ⟨he, hv, hwY, weak_mono hYX hwk⟩)

/-- Combine a coloring of the weak edges and the two sides of a cut. -/
private theorem colorable_of_crossing (hS : GoodS D H) (hCross : Cross H)
    (X : Finset (Vertex r n)) (cut : ℕ)
    (hcut : ∀ i j : Fin r, i < j → ¬ Weak D X i j →
      i.val ≤ cut ∧ cut < j.val) :
    (H.induce (X : Set (Vertex r n))).Colorable 6 := by
  obtain ⟨C⟩ := weak_colorable hS X
  let side (u : Vertex r n) : Bool := decide (u.1.val ≤ cut)
  let palette : Bool × Fin 3 ≃ Fin 6 :=
    (Fintype.equivFin (Bool × Fin 3)).trans (finCongr (by simp))
  refine ⟨SimpleGraph.Coloring.mk (fun u => palette (side u, C u)) ?_⟩
  intro u v hAdj heq
  have hAdj' : H.Adj u.val v.val := hAdj
  have hp := palette.injective heq
  by_cases hw : Weak D X u.val.1 v.val.1
  · have hWeakAdj : ((weakGraph D H X).induce (X : Set (Vertex r n))).Adj u v :=
      (weakGraph_adj D H X u.val v.val).mpr ⟨hAdj', u.2, v.2, hw⟩
    exact C.valid hWeakAdj (congrArg Prod.snd hp)
  · have hside : side u.val = side v.val := congrArg Prod.fst hp
    rcases lt_or_gt_of_ne (hCross hAdj') with hlt | hgt
    · obtain ⟨hu, hv⟩ := hcut _ _ hlt hw
      simp [side, hu, not_le_of_gt hv] at hside
    · have hw' : ¬ Weak D X v.val.1 u.val.1 := fun h => hw ((weak_comm D X _ _).mp h)
      obtain ⟨hv, hu⟩ := hcut _ _ hgt hw'
      simp [side, hv, not_le_of_gt hu] at hside

private def LargePair (D : Param r) (X : Finset (Vertex r n)) (p : Fin r × Fin r) : Prop :=
  p.1 < p.2 ∧ ¬ Weak D X p.1 p.2

/-- If the earliest large pair belongs to one set, every large pair in the other crosses
the cut just after the first block of the earliest pair. -/
private theorem crossing_of_first_pair {A B : Finset (Vertex r n)} {i j : Fin r}
    (hO : Ordered D) (hL : GoodL D H)
    (hAB : ∀ u ∈ A, ∀ v ∈ B, ¬ H.Adj u v)
    (hA : LargePair D A (i, j))
    (hfirst : ∀ p, LargePair D B p → pairRank (i, j) ≤ pairRank p) :
    ∀ k l : Fin r, k < l → ¬ Weak D B k l → k.val ≤ i.val ∧ i.val < l.val := by
  intro k l hkl hweak
  obtain ⟨hij, ha⟩ := hA
  have hmin := hfirst (k, l) ⟨hkl, hweak⟩
  have hjl : j ≤ l := by
    by_contra! hlj
    exact (not_lt_of_ge hmin) (pairRank_lt (Or.inl hlj))
  have hil : i < l := hij.trans_le hjl
  refine ⟨?_, hil⟩
  by_contra! hik
  have hik' : i < k := hik
  have hjl' : j < l := by
    rcases lt_or_eq_of_le hjl with hlt | heq
    · exact hlt
    · exact False.elim ((not_lt_of_ge hmin) (pairRank_lt (Or.inr ⟨heq.symm, hik'⟩)))
  have horderA := hO i j i l hij hil (Or.inl hjl')
  have horderB := hO k l i l hkl hil (Or.inr ⟨rfl, hik'⟩)
  have haSmall : n < strength D i j ^ 24 * load A i :=
    (lt_of_not_ge ha).trans_le (Nat.mul_le_mul_left _ (min_le_left _ _))
  have hbSmall : n < strength D k l ^ 24 * load B l :=
    (lt_of_not_ge hweak).trans_le (Nat.mul_le_mul_left _ (min_le_right _ _))
  let U := A.filter (fun u => u.1 = i)
  let V := B.filter (fun v => v.1 = l)
  have hU : n ≤ strength D i l * U.card :=
    haSmall.le.trans (Nat.mul_le_mul_right _ horderA.le)
  have hV : n ≤ strength D i l * V.card :=
    hbSmall.le.trans (Nat.mul_le_mul_right _ horderB.le)
  obtain ⟨u, hu, v, hv, huv⟩ := hL i l hil U V
    (fun u hu => (Finset.mem_filter.mp hu).2)
    (fun v hv => (Finset.mem_filter.mp hv).2) hU hV
  exact hAB u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 huv

/-- The ordered-block coloring lemma (Lemma 2 of the paper). -/
theorem ordered_colorable (hO : Ordered D) (hL : GoodL D H) (hS : GoodS D H)
    (hCross : Cross H) {A B : Finset (Vertex r n)}
    (hAB : ∀ u ∈ A, ∀ v ∈ B, ¬ H.Adj u v) :
    (H.induce (A : Set (Vertex r n))).Colorable 6 ∨
    (H.induce (B : Set (Vertex r n))).Colorable 6 := by
  classical
  let large := Finset.univ.filter (fun p => LargePair D A p ∨ LargePair D B p)
  by_cases hlarge : large.Nonempty
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image large pairRank hlarge
    obtain ⟨i, j⟩ := p
    have hbelongs : LargePair D A (i, j) ∨ LargePair D B (i, j) :=
      (Finset.mem_filter.mp hp).2
    rcases hbelongs with ha | hb
    · refine Or.inr (colorable_of_crossing hS hCross B i.val ?_)
      exact crossing_of_first_pair hO hL hAB ha
        (fun p hp => hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hp⟩))
    · refine Or.inl (colorable_of_crossing hS hCross A i.val ?_)
      exact crossing_of_first_pair hO hL (fun v hv u hu h => hAB u hu v hv h.symm) hb
        (fun p hp => hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hp⟩))
  · refine Or.inl (colorable_of_crossing hS hCross A 0 ?_)
    intro i j hij hw
    exact False.elim (hlarge ⟨(i, j),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hij, hw⟩⟩⟩)

end Blocks

end Erdos1111
