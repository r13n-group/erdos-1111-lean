import Erdos1111.Basic
import Erdos1111.Probability
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

open scoped BigOperators

namespace Erdos1111

variable {V : Type*} {r : ℕ}

/-- Ordered candidates for cycles of length less than `g`. Rotations and reversals
are counted separately, which is harmless for the deletion bound. -/
abbrev CycleCandidate (V : Type*) (g : ℕ) :=
  Σ k : Fin g, Fin k.val ↪ V

private def cycleNext {k : ℕ} (i : Fin k) : Fin k :=
  if h : i.val + 1 < k then ⟨i.val + 1, h⟩ else ⟨0, Nat.zero_lt_of_lt i.isLt⟩

private theorem cycleNext_val {k : ℕ} (i : Fin k) :
    (cycleNext i).val = if i.val + 1 < k then i.val + 1 else 0 := by
  unfold cycleNext
  split <;> rfl

private theorem cycleNext_cycleNext_ne {k : ℕ} (hk : 3 ≤ k) (i : Fin k) :
    cycleNext (cycleNext i) ≠ i := by
  intro heq
  have hi := i.isLt
  have h := congrArg Fin.val heq
  change (cycleNext (cycleNext i)).val = i.val at h
  rw [cycleNext_val (cycleNext i), cycleNext_val i] at h
  split_ifs at h <;> omega

private def cycleEdge {k : ℕ} (f : Fin k ↪ V) (i : Fin k) : Sym2 V :=
  s(f i, f (cycleNext i))

private theorem cycleEdge_injective {k : ℕ} (hk : 3 ≤ k) (f : Fin k ↪ V) :
    Function.Injective (cycleEdge f) := by
  intro i j h
  change s(f i, f (cycleNext i)) = s(f j, f (cycleNext j)) at h
  rcases Sym2.eq_iff.mp h with h' | h'
  · exact f.injective h'.1
  · have h₁ := f.injective h'.1
    have h₂ := f.injective h'.2
    exact (cycleNext_cycleNext_ne hk j (by rw [← h₁, h₂])).elim

private def IsCycleCandidate (G : SimpleGraph V) {g : ℕ} (c : CycleCandidate V g) : Prop :=
  3 ≤ c.1.val ∧ ∀ i, G.Adj (c.2 i) (c.2 (cycleNext i))

/-- The ordered short cycles present in a particular graph. -/
noncomputable def shortCycles [Fintype V] (G : SimpleGraph V) (g : ℕ) :
    Finset (CycleCandidate V g) := by
  classical
  exact Finset.univ.filter (IsCycleCandidate G)

private theorem isCycleCandidate_of_mem_shortCycles [Fintype V] {G : SimpleGraph V} {g : ℕ}
    {c : CycleCandidate V g} (hc : c ∈ shortCycles G g) : IsCycleCandidate G c := by
  classical
  exact (Finset.mem_filter.mp hc).2

private def cycleAnchor [Fintype V] (G : SimpleGraph V) (g : ℕ)
    (c : ↥(shortCycles G g)) : V :=
  c.val.2 ⟨0, by
    have hc := (isCycleCandidate_of_mem_shortCycles c.property).1
    omega⟩

/-- Deleting the first vertex of every ordered short cycle gives the required girth. -/
theorem delete_shortCycles [Fintype V] (G : SimpleGraph V) (g : ℕ) :
    ∃ U : Finset V, U.card ≤ (shortCycles G g).card ∧
      (g : ℕ∞) ≤ (G.induce ((U : Set V)ᶜ)).egirth := by
  classical
  let U := (shortCycles G g).attach.image (cycleAnchor G g)
  refine ⟨U, ?_, SimpleGraph.le_egirth.mpr ?_⟩
  · calc
      U.card ≤ (shortCycles G g).attach.card := Finset.card_image_le
      _ = _ := Finset.card_attach
  intro v w hw
  apply le_of_not_gt
  intro h
  have hwlt : w.length < g := ENat.natCast_lt_natCast.mp h
  let c : CycleCandidate V g :=
    ⟨⟨w.length, hwlt⟩, ⟨fun i => (w.getVert i.val).val, by
      intro i j hij
      apply Fin.ext
      have hi : i.val < w.length := i.isLt
      have hj : j.val < w.length := j.isLt
      have hi' : i.val ≤ w.length - 1 := by omega
      have hj' : j.val ≤ w.length - 1 := by omega
      exact hw.getVert_injOn' hi' hj' (Subtype.ext hij)⟩⟩
  have hc : c ∈ shortCycles G g := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hw.three_le_length, ?_⟩
    intro i
    change G.Adj (w.getVert i.val).val (w.getVert (cycleNext i).val).val
    have hindex : i.val < w.length := i.isLt
    have hNext : (cycleNext i).val = if i.val + 1 < w.length then i.val + 1 else 0 :=
      cycleNext_val i
    have hadj : G.Adj (w.getVert i.val).val (w.getVert (i.val + 1)).val :=
      w.adj_getVert_succ hindex
    by_cases hi : i.val + 1 < w.length
    · simpa [hNext, hi] using hadj
    · have hlast : i.val + 1 = w.length := by omega
      simpa [hNext, hlast] using hadj
  have hv : v.val ∈ U := by
    refine Finset.mem_image.mpr ⟨⟨c, hc⟩, Finset.mem_attach _ _, ?_⟩
    change (w.getVert 0).val = v.val
    rw [w.getVert_zero]
  exact v.property hv

private theorem coinProb_cycle_le {n g : ℕ} (D : Param r) (C : ℝ) (hC : 0 ≤ C)
    (hMax : ∀ e, edgeProb D n e ≤ C / (n : ℝ))
    (hp : ∀ e, 0 ≤ edgeProb D n e ∧ edgeProb D n e ≤ 1)
    (c : CycleCandidate (Vertex r n) g) :
    coinProb (edgeProb D n) (fun ω => IsCycleCandidate (sampleGraph ω) c) ≤
      (C / (n : ℝ)) ^ c.1.val := by
  classical
  by_cases hk : 3 ≤ c.1.val
  · let S := Finset.univ.image (cycleEdge c.2)
    have hcard : S.card = c.1.val := by
      dsimp only [S]
      rw [Finset.card_image_of_injective _ (cycleEdge_injective hk c.2)]
      simp
    calc
      coinProb (edgeProb D n) (fun ω => IsCycleCandidate (sampleGraph ω) c) ≤
          coinProb (edgeProb D n) (fun ω => ∀ e ∈ S, ω e = true) := by
        apply coinProb_mono _ hp
        intro ω h e he
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        exact ((sampleGraph_adj ω _ _).mp (h.2 i)).2
      _ = ∏ e ∈ S, edgeProb D n e := by simp [coinProb_cylinder]
      _ ≤ ∏ _e ∈ S, C / (n : ℝ) :=
        Finset.prod_le_prod₀ (fun e _ => (hp e).1) (fun e _ => hMax e)
      _ = (C / (n : ℝ)) ^ c.1.val := by rw [Finset.prod_const, hcard]
  · rw [coinProb_congr _ (Q := fun _ => False) (fun _ =>
        ⟨fun h => hk h.1, False.elim⟩), coinProb_false]
    positivity

/-- Markov's inequality for the number of ordered short cycles. The numerator is
independent of the number `n` of vertices per block. -/
theorem coinProb_shortCycles_ge_le (D : Param r) (n g q : ℕ) {C : ℝ}
    (hMax : ∀ e, edgeProb D n e ≤ C / (n : ℝ)) (hC : 0 ≤ C) (hn : 0 < n)
    (hp : ∀ e, 0 ≤ edgeProb D n e ∧ edgeProb D n e ≤ 1) (hq : 0 < q) :
    coinProb (edgeProb D n) (fun ω => q ≤ (shortCycles (sampleGraph ω) g).card) ≤
      (∑ k : Fin g, ((r : ℝ) * C) ^ k.val) / q := by
  classical
  unfold shortCycles
  apply (coinProb_count_ge_le (edgeProb D n) hp Finset.univ
    (fun c ω => IsCycleCandidate (sampleGraph ω) c) q hq).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  calc
    (∑ c : CycleCandidate (Vertex r n) g,
        coinProb (edgeProb D n) (fun ω => IsCycleCandidate (sampleGraph ω) c)) ≤
        ∑ c : CycleCandidate (Vertex r n) g, (C / (n : ℝ)) ^ c.1.val :=
      Finset.sum_le_sum fun c _ => coinProb_cycle_le D C hC hMax hp c
    _ = ∑ k : Fin g, (Fintype.card (Fin k.val ↪ Vertex r n) : ℝ) *
          (C / (n : ℝ)) ^ k.val := by
      rw [Fintype.sum_sigma]
      simp
    _ ≤ ∑ k : Fin g, ((r : ℝ) * C) ^ k.val := by
      apply Finset.sum_le_sum
      intro k _
      have hcard : Fintype.card (Fin k.val ↪ Vertex r n) ≤ (r * n) ^ k.val := by
        have h := Fintype.card_le_of_injective
          (fun f : Fin k.val ↪ Vertex r n => (f : Fin k.val → Vertex r n))
          DFunLike.coe_injective
        simpa [Vertex, Fintype.card_fun] using h
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      calc
        (Fintype.card (Fin k.val ↪ Vertex r n) : ℝ) * (C / (n : ℝ)) ^ k.val ≤
            ((r : ℝ) * n) ^ k.val * (C / (n : ℝ)) ^ k.val := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
        _ = ((r : ℝ) * C) ^ k.val := by
          rw [← mul_pow]
          congr 1
          field_simp

end Erdos1111
