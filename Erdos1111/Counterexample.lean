import Erdos1111.Ordered
import Erdos1111.LargePairs
import Erdos1111.Sparsity
import Erdos1111.ShortCycles
import Erdos1111.Chromatic
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# A counterexample to the El-Zahar–Erdős conjecture

The three bad events have probabilities at most 1/4, 1/7, and 1/4.
After choosing a graph outside their union, we delete one vertex from each
short cycle. The coloring obstruction survives passage to the induced graph.
-/

open scoped BigOperators
open Finset

namespace Erdos1111

universe u

/-- Two sets are anticomplete if they are disjoint and there are no edges between them. -/
def Anticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v

/-- The original El-Zahar–Erdős question, with clique number < t expressed as clique-freeness. -/
def ElZaharErdos : Prop :=
  ∀ t c : ℕ, 1 ≤ t → 1 ≤ c → ∃ d : ℕ, 1 ≤ d ∧
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V),
      (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
      ∃ A B : Set V, Anticomplete G A B ∧
        (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
        (c : ℕ∞) ≤ (G.induce B).chromaticNumber

private theorem exists_sample {r : ℕ} (hr : 0 < r) (D : Param r) (g : ℕ)
    (hD : ∀ i j, 128 * r + 4 ≤ strength D i j) :
    ∃ (n : ℕ) (_ : 0 < n) (ω : Sym2 (Vertex r n) → Bool),
      GoodL D (sampleGraph ω) ∧ GoodS D (sampleGraph ω) ∧
        (shortCycles (sampleGraph ω) g).card < n := by
  classical
  let C : ℕ := ∑ i : Fin r, ∑ j : Fin r, strength D i j ^ 3
  let T : ℝ := ∑ k : Fin g, ((r : ℝ) * (C : ℝ)) ^ k.val
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hCr : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  obtain ⟨n, hnLarge⟩ := exists_nat_gt (1 + (C : ℝ) + 4 * (r : ℝ)^2 + 4 * T)
  have hn' : (0 : ℝ) < n := by nlinarith
  have hn : 0 < n := by exact_mod_cast hn'
  have hC_lt : (C : ℝ) < n := by nlinarith
  have hpow : (n : ℝ) < (2 : ℝ)^n := by exact_mod_cast n.lt_two_pow_self
  have hDbound (i j : Fin r) : strength D i j ^ 3 ≤ C := by
    exact (Finset.single_le_sum (fun k _ => Nat.zero_le (strength D i k ^ 3))
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Nat.zero_le (∑ l : Fin r, strength D k l ^ 3))
        (Finset.mem_univ i))
  have hpMax (e : Sym2 (Vertex r n)) : edgeProb D n e ≤ (C : ℝ) / n := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      by_cases h : u.1 = v.1
      · rw [edgeProb_apply_same D n u v h]
        positivity
      · rw [edgeProb_apply_cross D n u v h]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hDbound u.1 v.1) hn'.le
  have hp (e : Sym2 (Vertex r n)) : 0 ≤ edgeProb D n e ∧ edgeProb D n e ≤ 1 := by
    refine ⟨?_, (hpMax e).trans ((div_le_iff₀ hn').2 (by simpa using hC_lt.le))⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      by_cases h : u.1 = v.1
      · simp [edgeProb_apply_same D n u v h]
      · rw [edgeProb_apply_cross D n u v h]
        positivity
  let badL (ω : Sym2 (Vertex r n) → Bool) := ¬ GoodL D (sampleGraph ω)
  let badS (ω : Sym2 (Vertex r n) → Bool) := ¬ GoodS D (sampleGraph ω)
  let badC (ω : Sym2 (Vertex r n) → Bool) := n ≤ (shortCycles (sampleGraph ω) g).card
  have hL : coinProb (edgeProb D n) badL ≤ 1 / 4 := by
    apply (coinProb_not_goodL D hn (fun i j _ => by have := hD i j; omega) hp).trans
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have hS : coinProb (edgeProb D n) badS ≤ 1 / 7 := by
    apply coinProb_not_goodS_le D hr hn _ hp
    intro i j _
    have hlo := hD i j
    have hle : strength D i j ≤ strength D i j ^ 3 := by
      calc
        _ ≤ strength D i j * strength D i j ^ 2 := by
          simpa using Nat.mul_le_mul_left (strength D i j) (Nat.one_le_pow 2 (strength D i j) (by omega))
        _ = _ := by ring
    omega
  have hCycles : coinProb (edgeProb D n) badC ≤ 1 / 4 := by
    apply (coinProb_shortCycles_ge_le D n g n hpMax hCr hn hp hn).trans
    change T / n ≤ 1 / 4
    exact (div_le_iff₀ hn').2 (by linarith [sq_nonneg (r : ℝ)])
  have hGood : ∃ ω : Sym2 (Vertex r n) → Bool,
      GoodL D (sampleGraph ω) ∧ GoodS D (sampleGraph ω) ∧
        (shortCycles (sampleGraph ω) g).card < n := by
    apply exists_of_coinProb_compl_lt_one (edgeProb D n)
    calc
      _ ≤ coinProb (edgeProb D n) (fun ω => badL ω ∨ (badS ω ∨ badC ω)) := by
        apply coinProb_mono _ hp
        intro ω h
        by_contra! hbad
        apply h
        exact ⟨of_not_not hbad.1, of_not_not hbad.2.1, Nat.lt_of_not_ge hbad.2.2⟩
      _ ≤ coinProb (edgeProb D n) badL +
          coinProb (edgeProb D n) (fun ω => badS ω ∨ badC ω) :=
        coinProb_union_le _ hp _ _
      _ ≤ coinProb (edgeProb D n) badL +
          (coinProb (edgeProb D n) badS + coinProb (edgeProb D n) badC) :=
        add_le_add_right (coinProb_union_le _ hp badS badC) (coinProb (edgeProb D n) badL)
      _ ≤ 1 / 4 + (1 / 7 + 1 / 4) := add_le_add hL (add_le_add hS hCycles)
      _ < 1 := by norm_num
  obtain ⟨ω, hω⟩ := hGood
  exact ⟨n, hn, ω, hω⟩

private noncomputable def ambientVertices {V : Type*} [Finite V] {S : Set V}
    (A : Set S) : Finset V := by
  classical
  exact (Set.toFinite A).toFinset.image Subtype.val

private theorem mem_ambientVertices {V : Type*} [Finite V] {S : Set V}
    {A : Set S} {v : V} :
    v ∈ ambientVertices A ↔ ∃ a ∈ A, (a : V) = v := by
  classical
  simp [ambientVertices]

private def inducedToAmbient {V : Type*} [Finite V] (H : SimpleGraph V) {S : Set V}
    (A : Set S) : ((H.induce S).induce A) →g (H.induce (ambientVertices A : Set V)) where
  toFun a := ⟨a.val.val, mem_ambientVertices.2 ⟨a.val, a.property, rfl⟩⟩
  map_rel' := fun h => h

/-- Theorem 1 of Liu and Meng. A forest has extended girth infinity. -/
theorem counterexample_large_girth (d g : ℕ) (_hg : 4 ≤ g) :
    ∃ (V : Type) (G : SimpleGraph V), Finite V ∧
      (d : ℕ∞) ≤ G.chromaticNumber ∧ (g : ℕ∞) ≤ G.egirth ∧
      ∀ A B : Set V, Anticomplete G A B →
        min (G.induce A).chromaticNumber (G.induce B).chromaticNumber ≤ 6 := by
  classical
  let r := 2 * d + 2
  have hr : 0 < r := by dsimp [r]; omega
  obtain ⟨D, hO, hD⟩ := exists_ordered (r := r) (128 * r + 4)
  obtain ⟨n, hn, ω, hL, hS, hC⟩ := exists_sample hr D g hD
  let H := sampleGraph ω
  obtain ⟨U, hU, hGirth⟩ := delete_shortCycles H g
  let S : Set (Vertex r n) := (U : Set (Vertex r n))ᶜ
  let G := H.induce S
  have hd : (d : ℕ∞) ≤ G.chromaticNumber :=
    chromatic_after_deletion hn rfl
      (fun i j _ => by have := hD i j; omega) hL U (le_trans hU hC.le)
  refine ⟨S, G, inferInstance, hd, hGirth, ?_⟩
  intro A B hAB
  have hNoEdges : ∀ u ∈ ambientVertices A, ∀ v ∈ ambientVertices B, ¬ H.Adj u v := by
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := mem_ambientVertices.1 hu
    obtain ⟨b, hb, rfl⟩ := mem_ambientVertices.1 hv
    exact hAB.2 a ha b hb
  rcases ordered_colorable hO hL hS (sampleGraph_cross ω) hNoEdges with hA | hB
  · exact (min_le_left _ _).trans (hA.of_hom (inducedToAmbient H A)).chromaticNumber_le
  · exact (min_le_right _ _).trans (hB.of_hom (inducedToAmbient H B)).chromaticNumber_le

private theorem erdos_1111_false_small : ¬ ElZaharErdos.{0} := by
  intro h
  obtain ⟨d, _, h⟩ := h 3 7 (by decide) (by decide)
  obtain ⟨V, G, hfinite, hd, hg, hAnti⟩ := counterexample_large_girth d 4 (by decide)
  let _ := hfinite
  have hClique : G.CliqueFree 3 := by
    intro s hs
    obtain ⟨u, w, hw, h3⟩ := SimpleGraph.is3Clique_iff_exists_cycle_length_three.mp ⟨s, hs⟩
    have hle := SimpleGraph.le_egirth.mp hg u w hw
    rw [h3] at hle
    norm_num at hle
  obtain ⟨A, B, hAB, hA, hB⟩ := h V G hd hClique
  have h7 : (7 : ℕ∞) ≤ min (G.induce A).chromaticNumber (G.induce B).chromaticNumber :=
    le_min hA hB
  have : (7 : ℕ∞) ≤ 6 := h7.trans (hAnti A B hAB)
  norm_num at this

/-- A counterexample in the smallest universe refutes each universe instance of the conjecture. -/
private theorem elZaharErdos_of_universe (h : ElZaharErdos.{u}) : ElZaharErdos.{0} := by
  intro t c ht hc
  obtain ⟨d, hd, solve⟩ := h t c ht hc
  refine ⟨d, hd, ?_⟩
  intro V _ G hχ hG
  let e : ULift.{u} V ≃ V := Equiv.ulift
  let L : SimpleGraph (ULift.{u} V) := G.comap e
  let E : L ≃g G := SimpleGraph.Iso.comap e G
  have hLχ : (d : ℕ∞) ≤ L.chromaticNumber := by
    rwa [SimpleGraph.chromaticNumber_congr E]
  obtain ⟨A, B, hAB, hA, hB⟩ := solve (ULift.{u} V) L hLχ (hG.comap E.isContained)
  refine ⟨e.symm ⁻¹' A, e.symm ⁻¹' B, ⟨?_, ?_⟩, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro v hvA hvB
    exact Set.disjoint_left.mp hAB.1 hvA hvB
  · intro v hv w hw hadj
    exact hAB.2 (e.symm v) hv (e.symm w) hw (E.symm.map_rel_iff.mpr hadj)
  · rw [SimpleGraph.chromaticNumber_congr (E.symm.induce e.symm.bijective.bijOn_preimage)]
    exact hA
  · rw [SimpleGraph.chromaticNumber_congr (E.symm.induce e.symm.bijective.bijOn_preimage)]
    exact hB

/-- The full negative answer to Erdős problem 1111 (JSP-000922). -/
theorem erdos_1111_false : ¬ ElZaharErdos.{u} :=
  fun h => erdos_1111_false_small (elZaharErdos_of_universe h)

end Erdos1111
