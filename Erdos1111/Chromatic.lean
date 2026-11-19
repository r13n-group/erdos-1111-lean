import Erdos1111.Basic

open scoped BigOperators

namespace Erdos1111

private theorem load_le_blockSize {r n : ℕ} (I : Finset (Vertex r n)) (i : Fin r) :
    load I i ≤ n := by
  classical
  unfold load
  have hsub : (I.filter fun v => v.1 = i) ⊆ ({i} : Finset (Fin r)) ×ˢ
      (Finset.univ : Finset (Fin n)) := by
    intro v hv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_singleton.mpr (Finset.mem_filter.mp hv).2, Finset.mem_univ _⟩
  simpa [Finset.card_product] using Finset.card_le_card hsub

/-- The large-pair condition makes an independent set large in at most one block. -/
theorem independent_card_le {r n : ℕ} {D : Param r} {H : SimpleGraph (Vertex r n)}
    (hr : 0 < r) (hD : ∀ i j, i < j → r ≤ strength D i j) (hL : GoodL D H)
    (I : Finset (Vertex r n)) (hI : ∀ u ∈ I, ∀ v ∈ I, ¬ H.Adj u v) :
    I.card ≤ 2 * n := by
  classical
  have hsorted (i j : Fin r) (hij : i < j)
      (hi : n ≤ r * load I i) (hj : n ≤ r * load I j) : False := by
    obtain ⟨u, hu, v, hv, hadj⟩ :=
      hL i j hij (I.filter fun u => u.1 = i) (I.filter fun v => v.1 = j)
        (fun _ h => (Finset.mem_filter.mp h).2) (fun _ h => (Finset.mem_filter.mp h).2)
        (hi.trans (Nat.mul_le_mul_right _ (hD i j hij)))
        (hj.trans (Nat.mul_le_mul_right _ (hD i j hij)))
    exact hI u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 hadj
  have hlight (J : Finset (Fin r)) (hJ : ∀ j ∈ J, r * load I j ≤ n) :
      (∑ j ∈ J, load I j) ≤ n := by
    apply Nat.le_of_mul_le_mul_left _ hr
    calc
      r * (∑ j ∈ J, load I j) = ∑ j ∈ J, r * load I j := Finset.mul_sum ..
      _ ≤ ∑ _j ∈ J, n := Finset.sum_le_sum hJ
      _ = J.card * n := by simp
      _ ≤ r * n := Nat.mul_le_mul_right _ (by simpa using Finset.card_le_univ J)
  have htotal : (∑ j : Fin r, load I j) = I.card := by
    simpa [load] using
      Finset.sum_card_fiberwise_eq_card_filter I (Finset.univ : Finset (Fin r))
        (fun v : Vertex r n => v.1)
  by_cases h : ∃ i : Fin r, n ≤ r * load I i
  · obtain ⟨i, hi⟩ := h
    have hrest := hlight (Finset.univ.erase i) (by
      intro j hj
      have hne : j ≠ i := (Finset.mem_erase.mp hj).1
      by_contra! hj'
      rcases lt_or_gt_of_ne hne with hji | hij
      · exact hsorted j i hji hj'.le hi
      · exact hsorted i j hij hi hj'.le)
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin r)) (load I)
      (Finset.mem_univ i)
    have hsingle := load_le_blockSize I i
    rw [htotal] at hsum
    omega
  · have hall := hlight (Finset.univ : Finset (Fin r)) (by
      intro j _
      exact (lt_of_not_ge fun hj => h ⟨j, hj⟩).le)
    rw [htotal] at hall
    omega

/-- Deleting at most one block's worth of vertices leaves chromatic number at least `d`. -/
theorem chromatic_after_deletion {r n d : ℕ} {D : Param r} {H : SimpleGraph (Vertex r n)}
    (hn : 0 < n) (hr : r = 2 * d + 2)
    (hD : ∀ i j, i < j → r ≤ strength D i j) (hL : GoodL D H)
    (U : Finset (Vertex r n)) (hU : U.card ≤ n) :
    (d : ℕ∞) ≤ (H.induce ((U : Set (Vertex r n))ᶜ)).chromaticNumber := by
  classical
  let A : Set (Vertex r n) := (U : Set (Vertex r n))ᶜ
  let _ : Fintype A := Fintype.ofFinite _
  have hrpos : 0 < r := by omega
  have hcardA : Fintype.card A = Uᶜ.card := by
    apply Fintype.card_of_subtype
    intro v
    simp [A]
  have hsum : Fintype.card A + U.card = r * n := by
    simp [hcardA, Finset.card_compl_add_card, Vertex]
  have hremaining : (2 * d) * n ≤ Fintype.card A := by
    have htotal : r * n = (2 * d) * n + (n + n) := by rw [hr]; ring
    omega
  change (d : ℕ∞) ≤ (H.induce A).chromaticNumber
  apply SimpleGraph.le_chromaticNumber_iff_coloring.mpr
  intro k c
  let fiber (j : Fin k) : Finset A := Finset.univ.filter (fun v : A => c v = j)
  have hfiber (j : Fin k) : (fiber j).card ≤ 2 * n := by
    let embed : A ↪ Vertex r n := Function.Embedding.subtype _
    let I : Finset (Vertex r n) := (fiber j).map embed
    have hI : ∀ u ∈ I, ∀ v ∈ I, ¬ H.Adj u v := by
      intro u hu v hv hadj
      obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
      exact c.valid (show (H.induce A).Adj u' v' from hadj)
        (((Finset.mem_filter.mp hu').2).trans ((Finset.mem_filter.mp hv').2).symm)
    simpa only [I, Finset.card_map] using independent_card_le hrpos hD hL I hI
  have hpartition : Fintype.card A = ∑ j, (fiber j).card := by
    simpa only [fiber, Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (f := fun v : A => c v)
        (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset (Fin k)))
        (fun _ _ => Finset.mem_univ _))
  have hcolors : Fintype.card A ≤ k * (2 * n) := by
    rw [hpartition]
    calc
      ∑ j : Fin k, (fiber j).card ≤ ∑ _j : Fin k, 2 * n :=
        Finset.sum_le_sum fun j _ => hfiber j
      _ = k * (2 * n) := by simp
  have hmul : n * (2 * d) ≤ n * (2 * k) := by
    calc
      n * (2 * d) = (2 * d) * n := Nat.mul_comm ..
      _ ≤ Fintype.card A := hremaining
      _ ≤ k * (2 * n) := hcolors
      _ = n * (2 * k) := by ring
  have hdk := Nat.le_of_mul_le_mul_left hmul hn
  omega

end Erdos1111
