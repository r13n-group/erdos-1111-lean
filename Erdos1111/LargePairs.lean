import Erdos1111.Basic
import Erdos1111.Probability
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Powerset

open scoped BigOperators

namespace Erdos1111

/-! A missing edge across two large parts of distinct blocks has exponentially small
probability. Taking a union over pairs of blocks and choices of both parts proves (L). -/

private def crossEmbedding {r n : ℕ} {i j : Fin r} (hij : i ≠ j) :
    (Fin n × Fin n) ↪ Sym2 (Vertex r n) where
  toFun ab := s((i, ab.1), (j, ab.2))
  inj' := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · apply Prod.ext
      · exact congrArg (fun v : Vertex r n => v.2) h.1
      · exact congrArg (fun v : Vertex r n => v.2) h.2
    · exact (hij (congrArg Prod.fst h.1)).elim

private def crossAbsent {r n : ℕ} (i j : Fin r) (U V : Finset (Fin n))
    (ω : Sym2 (Vertex r n) → Bool) : Prop :=
  ∀ a ∈ U, ∀ b ∈ V, ω s((i, a), (j, b)) = false

private theorem coinProb_crossAbsent {r n : ℕ} (D : Param r)
    (i j : Fin r) (hij : i ≠ j) (U V : Finset (Fin n)) :
    coinProb (edgeProb D n) (crossAbsent i j U V) =
      (1 - (strength D i j : ℝ) ^ 3 / n) ^ (U.card * V.card) := by
  let testEdges := (U.product V).map (crossEmbedding hij)
  have hEvent : crossAbsent i j U V =
      (fun ω => ∀ e ∈ testEdges, ω e = false) := by
    funext ω
    apply propext
    constructor
    · intro h e he
      rcases Finset.mem_map.mp he with ⟨⟨a, b⟩, hab, rfl⟩
      have hab' := Finset.mem_product.mp hab
      exact h a hab'.1 b hab'.2
    · intro h a ha b hb
      exact h _ (Finset.mem_map.mpr ⟨(a, b), Finset.mk_mem_product ha hb, rfl⟩)
  rw [hEvent, coinProb_cylinder]
  simp only [Bool.false_eq_true, ite_false]
  calc
    _ = ∏ _e ∈ testEdges, (1 - (strength D i j : ℝ) ^ 3 / n) := by
      apply Finset.prod_congr rfl
      intro e he
      rcases Finset.mem_map.mp he with ⟨⟨a, b⟩, _, rfl⟩
      change 1 - edgeProb D n s((i, a), (j, b)) = _
      rw [edgeProb_apply_cross D n (i, a) (j, b) hij]
    _ = _ := by simp [testEdges, Finset.prod_const]

private theorem exp_neg_four_le : Real.exp (-4) ≤ (1 : ℝ) / 8 := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := calc
    (3 : ℝ) = 2 + 1 := by norm_num
    _ ≤ Real.exp 2 := Real.add_one_le_exp 2
  have h8 : (8 : ℝ) ≤ Real.exp 4 := calc
    (8 : ℝ) ≤ 3 ^ 2 := by norm_num
    _ ≤ Real.exp 2 ^ 2 := pow_le_pow_left₀ (by norm_num) h3 2
    _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h8

private theorem absent_power_le {n B u v : ℕ}
    (hn : 0 < n) (hB : 4 ≤ B) (hu : n ≤ B * u) (hv : n ≤ B * v)
    (hp : (B : ℝ) ^ 3 / n ≤ 1) :
    (1 - (B : ℝ) ^ 3 / n) ^ (u * v) ≤ (1 / 8 : ℝ) ^ n := by
  let p : ℝ := (B : ℝ) ^ 3 / n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hB' : (4 : ℝ) ≤ B := by exact_mod_cast hB
  have hu' : (n : ℝ) ≤ (B : ℝ) * (u : ℝ) := by exact_mod_cast hu
  have hv' : (n : ℝ) ≤ (B : ℝ) * (v : ℝ) := by exact_mod_cast hv
  have hsize : (n : ℝ) * n ≤ ((B : ℝ) * (u : ℝ)) * ((B : ℝ) * (v : ℝ)) :=
    mul_le_mul hu' hv' hn'.le (by positivity)
  have hrate : (n : ℝ) * 4 ≤ p * ((u : ℝ) * (v : ℝ)) := by
    calc
      (n : ℝ) * 4 = 4 * n := mul_comm _ _
      _ ≤ (B : ℝ) * n := mul_le_mul_of_nonneg_right hB' hn'.le
      _ ≤ p * ((u : ℝ) * (v : ℝ)) := by
        have hnumer : (B : ℝ) * n * n ≤ (B : ℝ) ^ 3 * ((u : ℝ) * (v : ℝ)) := calc
          (B : ℝ) * n * n = (B : ℝ) * ((n : ℝ) * n) := by ring
          _ ≤ (B : ℝ) * (((B : ℝ) * (u : ℝ)) * ((B : ℝ) * (v : ℝ))) :=
            mul_le_mul_of_nonneg_left hsize (by positivity)
          _ = _ := by ring
        dsimp only [p]
        rw [div_mul_eq_mul_div₀]
        exact (le_div_iff₀ hn').mpr hnumer
  have hbase : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc
    (1 - p) ^ (u * v) ≤ Real.exp (-p) ^ (u * v) :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp) hbase _
    _ = Real.exp (-(p * ((u : ℝ) * (v : ℝ)))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp ((n : ℝ) * (-4)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = Real.exp (-4) ^ n := Real.exp_nat_mul (-4) n
    _ ≤ (1 / 8 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_four_le n

private abbrev PairTest (r n : ℕ) := Fin r × Fin r × Finset (Fin n) × Finset (Fin n)

private def badPairTest {r n : ℕ} (D : Param r) (test : PairTest r n)
    (ω : Sym2 (Vertex r n) → Bool) : Prop :=
  let (i, j, U, V) := test
  i < j ∧ n ≤ strength D i j * U.card ∧ n ≤ strength D i j * V.card ∧
    crossAbsent i j U V ω

private theorem block_mem_of_mem_coordinates {r n : ℕ}
    {i : Fin r} {U : Finset (Vertex r n)} (hU : ∀ u ∈ U, u.1 = i)
    {a : Fin n} (ha : a ∈ U.image Prod.snd) : (i, a) ∈ U := by
  rcases Finset.mem_image.mp ha with ⟨⟨j, b⟩, hb, hba⟩
  have hji := hU (j, b) hb
  change j = i at hji
  change b = a at hba
  cases hji
  cases hba
  exact hb

private theorem card_block_coordinates {r n : ℕ} {i : Fin r}
    {U : Finset (Vertex r n)} (hU : ∀ u ∈ U, u.1 = i) :
    (U.image Prod.snd).card = U.card := by
  apply Finset.card_image_of_injOn
  intro u hu v hv huv
  exact Prod.ext ((hU u hu).trans (hU v hv).symm) huv

/-- The probability that condition (L) fails is at most the number of ordered
block pairs times a geometric factor in the common block size. -/
theorem coinProb_not_goodL {r n : ℕ} (D : Param r) (hn : 0 < n)
    (hD : ∀ i j, i < j → 4 ≤ strength D i j)
    (hp : ∀ e, 0 ≤ edgeProb D n e ∧ edgeProb D n e ≤ 1) :
    coinProb (edgeProb D n) (fun ω => ¬ GoodL D (sampleGraph ω)) ≤
      (r : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n := by
  classical
  let tests : Finset (PairTest r n) := Finset.univ
  have hbad : ∀ ω, (¬ GoodL D (sampleGraph ω)) →
      ∃ test ∈ tests, badPairTest D test ω := by
    intro ω h
    by_contra hNone
    apply h
    intro i j hij U V hUi hVj hU hV
    by_contra hNoEdge
    apply hNone
    refine ⟨(i, j, U.image Prod.snd, V.image Prod.snd), Finset.mem_univ _,
      hij, ?_, ?_, ?_⟩
    · simpa only [card_block_coordinates hUi] using hU
    · simpa only [card_block_coordinates hVj] using hV
    · intro a ha b hb
      cases he : ω s((i, a), (j, b)) with
      | false => rfl
      | true =>
        exact (hNoEdge ⟨(i, a), block_mem_of_mem_coordinates hUi ha,
          (j, b), block_mem_of_mem_coordinates hVj hb,
          (sampleGraph_adj ω (i, a) (j, b)).mpr ⟨ne_of_lt hij, he⟩⟩).elim
  have hbound : ∀ test ∈ tests,
      coinProb (edgeProb D n) (badPairTest D test) ≤ (1 / 8 : ℝ) ^ n := by
    rintro ⟨i, j, U, V⟩ _
    by_cases hlarge : i < j ∧ n ≤ strength D i j * U.card ∧
        n ≤ strength D i j * V.card
    · obtain ⟨hij, hU, hV⟩ := hlarge
      let b : Fin n := ⟨0, hn⟩
      have hp' := (hp s(((i, b) : Vertex r n), ((j, b) : Vertex r n))).2
      rw [edgeProb_apply_cross D n (i, b) (j, b) (ne_of_lt hij)] at hp'
      calc
        _ ≤ coinProb (edgeProb D n) (crossAbsent i j U V) :=
          coinProb_mono _ hp (fun _ h => h.2.2.2)
        _ = _ := coinProb_crossAbsent D i j (ne_of_lt hij) U V
        _ ≤ _ := absent_power_le hn (hD i j hij) hU hV hp'
    · have hEmpty : badPairTest D (i, j, U, V) = (fun _ => False) := by
        funext ω
        apply propext
        constructor
        · intro h
          exact hlarge ⟨h.1, h.2.1, h.2.2.1⟩
        · exact False.elim
      rw [hEmpty, coinProb_false]
      positivity
  calc
    _ ≤ coinProb (edgeProb D n) (fun ω => ∃ test ∈ tests, badPairTest D test ω) :=
      coinProb_mono _ hp hbad
    _ ≤ ∑ test ∈ tests, coinProb (edgeProb D n) (badPairTest D test) :=
      coinProb_iUnion_le _ hp _ _
    _ ≤ ∑ _test ∈ tests, (1 / 8 : ℝ) ^ n := Finset.sum_le_sum hbound
    _ = (r : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [tests, Finset.card_univ, PairTest, Fintype.card_prod, Fintype.card_finset,
        Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      calc
        _ = (r : ℝ) ^ 2 * ((2 : ℝ) ^ n * 2 ^ n * (1 / 8) ^ n) := by ring
        _ = _ := by rw [← mul_pow, ← mul_pow]; norm_num

end Erdos1111
