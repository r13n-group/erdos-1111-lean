import Erdos1111.Basic
import Erdos1111.Probability
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Uniform sparsity on weak block pairs

For a fixed vertex set, orient each eligible edge toward an endpoint in the
larger occupied block. Summing these contributions bounds the Bernoulli mass of
the potential weak edges. The factorial-moment estimate then controls all
vertex sets simultaneously.
-/

open scoped BigOperators Classical

namespace Erdos1111

variable {r n : ℕ}

private def sparsePair (D : Param r) (X : Finset (Vertex r n))
    (v u : Vertex r n) : Prop :=
  u.1 ≠ v.1 ∧ load X u.1 ≤ load X v.1 ∧ Weak D X u.1 v.1

private noncomputable def sparsePairs (D : Param r) (X : Finset (Vertex r n)) :
    Finset (Vertex r n × Vertex r n) := by
  classical
  exact (X ×ˢ X).filter fun e => sparsePair D X e.1 e.2

private noncomputable def sparseEdges (D : Param r) (X : Finset (Vertex r n)) :
    Finset (Sym2 (Vertex r n)) := by
  classical
  exact (sparsePairs D X).image fun e => s(e.2, e.1)

private theorem weak_edges_subset (D : Param r) (X : Finset (Vertex r n))
    (ω : Sym2 (Vertex r n) → Bool) :
    (weakGraph D (sampleGraph ω) X).edgeFinset ⊆
      (sparseEdges D X).filter (fun e => ω e = true) := by
  classical
  intro e
  refine e.inductionOn ?_
  intro u v he
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  change (u.1 ≠ v.1 ∧ ω s(u, v) = true) ∧ u ∈ X ∧ v ∈ X ∧ Weak D X u.1 v.1 at he
  rcases he with ⟨⟨hne, hω⟩, hu, hv, hw⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, hω⟩
  unfold sparseEdges
  apply Finset.mem_image.mpr
  rcases le_total (load X u.1) (load X v.1) with hle | hle
  · refine ⟨(v, u), ?_, rfl⟩
    unfold sparsePairs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hv, hu⟩, hne, hle, hw⟩
  · refine ⟨(u, v), ?_, Sym2.eq_swap⟩
    unfold sparsePairs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hne.symm, hle, (weak_comm D X _ _).mp hw⟩

private theorem weak_block_mass_le (D : Param r) (X : Finset (Vertex r n))
    (hr : 0 < r) (hn : 0 < n)
    (hD : ∀ i j : Fin r, i ≠ j → 128 * r ≤ strength D i j ^ 3)
    {a : ℝ} (_ha₀ : 0 ≤ a) (ha : a ^ 3 = (X.card : ℝ) / ↑(r * n))
    (i j : Fin r) (hne : i ≠ j) (hle : load X i ≤ load X j) (hw : Weak D X i j) :
    (load X i : ℝ) * ((strength D i j : ℝ) ^ 3 / n) ≤ a ^ 2 / (128 * r) := by
  let B : ℝ := (strength D i j : ℝ) ^ 3
  let u : ℝ := (load X i : ℝ) / n
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBR : 128 * (r : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast hD i j hne
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hBR
  have h_r_le_B : (r : ℝ) ≤ B := by linarith
  have hu₀ : 0 ≤ u := by dsimp [u]; positivity
  have hu : u ≤ (r : ℝ) * a ^ 3 := by
    rw [ha, Nat.cast_mul]
    calc
      u ≤ (X.card : ℝ) / n := by
        apply div_le_div_of_nonneg_right _ hnR.le
        exact_mod_cast Finset.card_filter_le X (fun v => v.1 = i)
      _ = (r : ℝ) * ((X.card : ℝ) / ((r : ℝ) * n)) := by field_simp
  have hweak : (strength D i j : ℝ) ^ 24 * (load X i : ℝ) ≤ n := by
    change strength D i j ^ 24 * min (load X i) (load X j) ≤ n at hw
    rw [min_eq_left hle] at hw
    exact_mod_cast hw
  have hWeakUnit : B ^ 8 * u ≤ 1 := by
    calc
      B ^ 8 * u = (strength D i j : ℝ) ^ 24 * (load X i : ℝ) / n := by
        dsimp [B, u]
        rw [← pow_mul]
        ring
      _ ≤ n / (n : ℝ) := div_le_div_of_nonneg_right hweak hnR.le
      _ = 1 := div_self hnR.ne'
  have hRatio : (r : ℝ) / B ≤ 1 := (div_le_one hB).mpr h_r_le_B
  have hc : ((128 * (r : ℝ)) * (B * u)) ^ 3 ≤ (a ^ 2) ^ 3 := by
    calc
      ((128 * (r : ℝ)) * (B * u)) ^ 3 = (128 * (r : ℝ)) ^ 3 * (B ^ 3 * u ^ 3) := by ring
      _ ≤ B ^ 3 * (B ^ 3 * u ^ 3) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hBR 3) (by positivity)
      _ = (B ^ 8 * u) * u ^ 2 / B ^ 2 := by
        field_simp [hB.ne']
      _ ≤ 1 * ((r : ℝ) * a ^ 3) ^ 2 / B ^ 2 := by gcongr
      _ = ((r : ℝ) / B) ^ 2 * (a ^ 2) ^ 3 := by
        simp only [div_pow]
        ring
      _ ≤ (a ^ 2) ^ 3 := by
        have hRatioSq : ((r : ℝ) / B) ^ 2 ≤ 1 := by
          simpa using pow_le_pow_left₀ (show 0 ≤ (r : ℝ) / B by positivity) hRatio 2
        simpa using mul_le_mul_of_nonneg_right hRatioSq (show 0 ≤ (a ^ 2) ^ 3 by positivity)
  have hFinal := le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (sq_nonneg a) hc
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 128 * r)).2
  calc
    (load X i : ℝ) * ((strength D i j : ℝ) ^ 3 / n) * (128 * (r : ℝ)) =
        (128 * (r : ℝ)) * (B * u) := by dsimp [B, u]; ring
    _ ≤ a ^ 2 := hFinal

private theorem sparse_mass_le (D : Param r) (X : Finset (Vertex r n))
    (hr : 0 < r) (hn : 0 < n)
    (hD : ∀ i j : Fin r, i ≠ j → 128 * r ≤ strength D i j ^ 3)
    (hp : ∀ e : Sym2 (Vertex r n), 0 ≤ edgeProb D n e ∧ edgeProb D n e ≤ 1)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha : a ^ 3 = (X.card : ℝ) / ↑(r * n)) :
    (∑ e ∈ sparseEdges D X, edgeProb D n e) ≤ (X.card : ℝ) * a ^ 2 / 128 := by
  classical
  let weight (v u : Vertex r n) : ℝ :=
    if sparsePair D X v u then edgeProb D n s(u, v) else 0
  have hBlock (v : Vertex r n) (i : Fin r) :
      (∑ u ∈ X.filter (fun u => u.1 = i), weight v u) ≤ a ^ 2 / (128 * r) := by
    by_cases hi : i ≠ v.1 ∧ load X i ≤ load X v.1 ∧ Weak D X i v.1
    · have hEq : (∑ u ∈ X.filter (fun u => u.1 = i), weight v u) =
          (load X i : ℝ) * ((strength D i v.1 : ℝ) ^ 3 / n) := by
        calc
          _ = ∑ u ∈ X.filter (fun u => u.1 = i), (strength D i v.1 : ℝ) ^ 3 / n := by
            apply Finset.sum_congr rfl
            intro u hu
            have hui := (Finset.mem_filter.mp hu).2
            have hPair : sparsePair D X v u := by simpa only [sparsePair, hui] using hi
            rw [show weight v u = edgeProb D n s(u, v) by simp [weight, hPair]]
            rw [edgeProb_apply_cross D n u v hPair.1, hui]
          _ = _ := by simp [load, Finset.sum_const, nsmul_eq_mul]
      rw [hEq]
      exact weak_block_mass_le D X hr hn hD ha₀ ha i v.1 hi.1 hi.2.1 hi.2.2
    · have hEq : (∑ u ∈ X.filter (fun u => u.1 = i), weight v u) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        have hui := (Finset.mem_filter.mp hu).2
        have hPair : ¬ sparsePair D X v u := by simpa only [sparsePair, hui] using hi
        simp [weight, hPair]
      rw [hEq]
      positivity
  calc
    _ ≤ ∑ uv ∈ sparsePairs D X, edgeProb D n s(uv.2, uv.1) := by
      unfold sparseEdges
      apply Finset.sum_image_le_of_nonneg
      intro e _
      exact (hp e).1
    _ = ∑ v ∈ X, ∑ u ∈ X, weight v u := by
      rw [sparsePairs, Finset.sum_filter, Finset.sum_product]
    _ ≤ ∑ _ ∈ X, (r : ℝ) * (a ^ 2 / (128 * r)) := by
      apply Finset.sum_le_sum
      intro v _
      rw [← Finset.sum_fiberwise X Prod.fst (weight v)]
      calc
        _ ≤ ∑ _ : Fin r, a ^ 2 / (128 * r) :=
          Finset.sum_le_sum fun i _ => hBlock v i
        _ = _ := by simp [nsmul_eq_mul]
    _ = _ := by
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp

private theorem exp_nat_le (m : ℕ) : Real.exp (m : ℝ) ≤ (3 : ℝ) ^ m := by
  rw [← Real.exp_one_pow]
  have h := Real.exp_le_two_add_div_two_sub (x := 1) (by norm_num) (by norm_num)
  norm_num at h
  exact pow_le_pow_left₀ (Real.exp_pos 1).le h m

private theorem pow_div_factorial_le (x : ℝ) (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m) :
    x ^ m / (m.factorial : ℝ) ≤ (3 * x / m) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  calc
    _ = (x / m) ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ (x / m) ^ m * 3 ^ m :=
      mul_le_mul_of_nonneg_left
        ((Real.pow_div_factorial_le_exp (x := (m : ℝ)) hmR.le m).trans (exp_nat_le m)) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

private noncomputable def sparseBound (N m : ℕ) : ℝ :=
  if m = 0 then 0 else ((3 : ℝ) / 128 * (m : ℝ) / N) ^ m

private theorem fixed_set_sparse_bound (D : Param r) (X : Finset (Vertex r n))
    (hr : 0 < r) (hn : 0 < n)
    (hD : ∀ i j : Fin r, i ≠ j → 128 * r ≤ strength D i j ^ 3)
    (hp : ∀ e : Sym2 (Vertex r n), 0 ≤ edgeProb D n e ∧ edgeProb D n e ≤ 1) :
    coinProb (edgeProb D n)
      (fun ω => X.Nonempty ∧ 3 * X.card ≤ 2 * (weakGraph D (sampleGraph ω) X).edgeFinset.card) ≤
      sparseBound (r * n) X.card := by
  classical
  by_cases hX : X.Nonempty
  · let m := X.card
    let N := r * n
    let q := (3 * m + 1) / 2
    let μ := ∑ e ∈ sparseEdges D X, edgeProb D n e
    have hm : 0 < m := hX.card_pos
    have hN : 0 < N := Nat.mul_pos hr hn
    have hmN : m ≤ N := by
      simpa [m, N, Vertex] using (Finset.card_le_univ X)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hmq : m ≤ q := by dsimp [q]; omega
    have hq : 0 < q := hm.trans_le hmq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq
    have hq2 : 3 * m ≤ 2 * q := by dsimp [q]; omega
    let a : ℝ := ((m : ℝ) / N) ^ ((3 : ℝ)⁻¹)
    have ha₀ : 0 ≤ a := by dsimp [a]; positivity
    have ha : a ^ 3 = (m : ℝ) / N := by
      simpa [a] using Real.rpow_inv_natCast_pow
        (show (0 : ℝ) ≤ (m : ℝ) / N by positivity) (by decide : (3 : ℕ) ≠ 0)
    have ha₁ : a ≤ 1 := by
      apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by norm_num)
      rw [ha, one_pow]
      exact (div_le_one hNR).mpr hmNR
    have hμ : μ ≤ (m : ℝ) * a ^ 2 / 128 := sparse_mass_le D X hr hn hD hp ha₀ ha
    have hμ₀ : 0 ≤ μ := Finset.sum_nonneg fun e _ => (hp e).1
    have hBase : 3 * μ / (q : ℝ) ≤ (3 / 128 : ℝ) * a ^ 2 := by
      apply (div_le_iff₀ hqR).2
      calc
        3 * μ ≤ 3 * ((m : ℝ) * a ^ 2 / 128) := by gcongr
        _ = (3 / 128 : ℝ) * a ^ 2 * m := by ring
        _ ≤ (3 / 128 : ℝ) * a ^ 2 * q := by gcongr
    have hP : ((3 / 128 : ℝ) * a ^ 2) ^ q ≤ ((3 / 128 : ℝ) * ((m : ℝ) / N)) ^ m := by
      rw [mul_pow, mul_pow, ← pow_mul, ← ha, ← pow_mul]
      exact mul_le_mul
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmq)
        (pow_le_pow_of_le_one ha₀ ha₁ hq2)
        (pow_nonneg ha₀ _) (by positivity)
    change _ ≤ sparseBound N m
    rw [show sparseBound N m = ((3 / 128 : ℝ) * ((m : ℝ) / N)) ^ m by
      simp only [sparseBound, hm.ne', ite_false, mul_div_assoc]]
    calc
      _ ≤ coinProb (edgeProb D n) (fun ω => q ≤ ((sparseEdges D X).filter fun e => ω e = true).card) := by
        apply coinProb_mono _ hp
        intro ω hω
        have hc := Finset.card_le_card (weak_edges_subset D X ω)
        have h := hω.2
        change 3 * m ≤ _ at h
        dsimp [q]
        omega
      _ ≤ μ ^ q / q.factorial := coinProb_card_ge_le _ hp _ _
      _ ≤ (3 * μ / q) ^ q := pow_div_factorial_le μ hμ₀ hq
      _ ≤ ((3 / 128 : ℝ) * a ^ 2) ^ q := pow_le_pow_left₀ (by positivity) hBase q
      _ ≤ _ := hP
  · have hX0 : X.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hX)
    simp [coinProb, hX, sparseBound, hX0]

private theorem weighted_sparseBound_le (N m : ℕ) (hm : 0 < m) (hN : 0 < N) :
    (N.choose m : ℝ) * sparseBound N m ≤ (1 / 8 : ℝ) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hChoose : (N.choose m : ℝ) ≤ (3 * (N : ℝ) / m) ^ m :=
    (Nat.choose_le_pow_div (α := ℝ) m N).trans (pow_div_factorial_le (N : ℝ) (by positivity) hm)
  simp only [sparseBound, hm.ne', ite_false]
  calc
    _ ≤ (3 * (N : ℝ) / m) ^ m * ((3 / 128 : ℝ) * (m : ℝ) / N) ^ m := by gcongr
    _ = ((9 : ℝ) / 128) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp; ring
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Failure of (S) has probability at most one seventh. -/
theorem coinProb_not_goodS_le (D : Param r) (hr : 0 < r) (hn : 0 < n)
    (hD : ∀ i j : Fin r, i ≠ j → 128 * r ≤ strength D i j ^ 3)
    (hp : ∀ e : Sym2 (Vertex r n), 0 ≤ edgeProb D n e ∧ edgeProb D n e ≤ 1) :
    coinProb (edgeProb D n) (fun ω => ¬ GoodS D (sampleGraph ω)) ≤ 1 / 7 := by
  classical
  let N := r * n
  let Xs := (Finset.univ : Finset (Vertex r n)).powerset
  let bad (X : Finset (Vertex r n)) (ω : Sym2 (Vertex r n) → Bool) :=
    X.Nonempty ∧ 3 * X.card ≤ 2 * (weakGraph D (sampleGraph ω) X).edgeFinset.card
  have hN : 0 < N := Nat.mul_pos hr hn
  have hCard : (Finset.univ : Finset (Vertex r n)).card = N := by simp [N, Vertex]
  have hsum :
      (∑ m ∈ Finset.range (N + 1), (N.choose m : ℝ) * sparseBound N m) =
        ∑ m ∈ Finset.Ico 1 (N + 1), (N.choose m : ℝ) * sparseBound N m := by
    rw [Finset.range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (show 0 < N + 1 by omega)]
    simp only [zero_add]
    have hz : 0 ∉ Finset.Ico 1 (N + 1) := by simp
    rw [Finset.sum_insert hz]
    simp [sparseBound]
  calc
    _ ≤ coinProb (edgeProb D n) (fun ω => ∃ X ∈ Xs, bad X ω) := by
      apply coinProb_mono _ hp
      intro ω h
      unfold GoodS at h
      push Not at h
      obtain ⟨X, hX, hc⟩ := h
      exact ⟨X, by simp [Xs], hX, hc⟩
    _ ≤ ∑ X ∈ Xs, coinProb (edgeProb D n) (bad X) :=
      coinProb_iUnion_le _ hp Xs bad
    _ ≤ ∑ X ∈ Xs, sparseBound N X.card :=
      Finset.sum_le_sum fun X _ => fixed_set_sparse_bound D X hr hn hD hp
    _ = ∑ m ∈ Finset.range (N + 1), (N.choose m : ℝ) * sparseBound N m := by
      unfold Xs
      rw [Finset.sum_powerset_apply_card, hCard]
      simp only [nsmul_eq_mul]
    _ = ∑ m ∈ Finset.Ico 1 (N + 1), (N.choose m : ℝ) * sparseBound N m := hsum
    _ ≤ ∑ m ∈ Finset.Ico 1 (N + 1), (1 / 8 : ℝ) ^ m := by
      apply Finset.sum_le_sum
      intro m hm
      exact weighted_sparseBound_le N m (Finset.mem_Ico.mp hm).1 hN
    _ ≤ 1 / 7 := by
      have hGeom := geom_sum_Ico_le_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)
        (m := 1) (n := N + 1)
      rwa [show (1 / 8 : ℝ) ^ 1 / (1 - 1 / 8) = 1 / 7 by norm_num] at hGeom

end Erdos1111
