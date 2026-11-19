import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Finite product probabilities

The sample space consists of all Boolean assignments to a finite set of edge
coordinates. We work directly with the finite sum of their product weights.
-/

open scoped BigOperators

noncomputable section

namespace Erdos1111

variable {E : Type*} [Fintype E]

private def coinMass (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

/-- Weight of an outcome in the independent Bernoulli product. -/
def coinWeight (p : E → ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, coinMass (p e) (ω e)

/-- Probability of an event in the finite Bernoulli product. -/
def coinProb (p : E → ℝ) (P : (E → Bool) → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then coinWeight p ω else 0

lemma coinWeight_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (ω : E → Bool) : 0 ≤ coinWeight p ω := by
  apply Finset.prod_nonneg
  intro e _
  cases h : ω e
  · simpa [coinMass, h] using sub_nonneg.mpr (hp e).2
  · simpa [coinMass, h] using (hp e).1

lemma coinProb_congr (p : E → ℝ) {P Q : (E → Bool) → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : coinProb p P = coinProb p Q := by
  congr 1
  exact funext fun ω => propext (h ω)

lemma coinProb_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (P : (E → Bool) → Prop) : 0 ≤ coinProb p P := by
  classical
  unfold coinProb
  exact Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact coinWeight_nonneg p hp ω
    · exact le_rfl

lemma coinProb_mono (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    {P Q : (E → Bool) → Prop} (h : ∀ ω, P ω → Q ω) :
    coinProb p P ≤ coinProb p Q := by
  classical
  unfold coinProb
  apply Finset.sum_le_sum
  intro ω _
  by_cases hP : P ω
  · simp [hP, h ω hP]
  · by_cases hQ : Q ω
    · simpa [hP, hQ] using coinWeight_nonneg p hp ω
    · simp [hP, hQ]

/-- The probability that every coordinate of `S` takes a prescribed Boolean value. -/
lemma coinProb_cylinder (p : E → ℝ) (S : Finset E) (b : Bool) :
    coinProb p (fun ω => ∀ e ∈ S, ω e = b) =
      ∏ e ∈ S, (if b then p e else 1 - p e) := by
  classical
  let mass (e : E) (c : Bool) : ℝ :=
    if e ∈ S → c = b then coinMass (p e) c else 0
  have hmass (e : E) :
      (∑ c : Bool, mass e c) = if e ∈ S then coinMass (p e) b else 1 := by
    rw [Fintype.univ_bool]
    by_cases he : e ∈ S
    · cases b <;> simp [mass, coinMass, he]
    · simp [mass, coinMass, he]
  have houtcome (ω : E → Bool) :
      @ite ℝ (∀ e ∈ S, ω e = b) (Classical.propDecidable _) (coinWeight p ω) 0 =
        ∏ e, mass e (ω e) := by
    by_cases hω : ∀ e ∈ S, ω e = b
    · rw [ite_eq_left hω]
      refine Finset.prod_congr rfl fun e _ => ?_
      exact (ite_eq_left (hω e)).symm
    · rw [ite_eq_right hω]
      push Not at hω
      obtain ⟨e, he, hne⟩ := hω
      symm
      apply Finset.prod_eq_zero (i := e) (Finset.mem_univ e)
      exact ite_eq_right (fun h => hne (h he))
  calc
    coinProb p (fun ω => ∀ e ∈ S, ω e = b) =
        ∑ ω : E → Bool, ∏ e, mass e (ω e) := by
      unfold coinProb
      exact Finset.sum_congr rfl fun ω _ => houtcome ω
    _ = ∏ e, ∑ c : Bool, mass e c := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun _ : E => (Finset.univ : Finset Bool)) mass).symm
    _ = ∏ e, if e ∈ S then coinMass (p e) b else 1 :=
      Finset.prod_congr rfl fun e _ => hmass e
    _ = ∏ e ∈ S, (if b then p e else 1 - p e) := by
      rw [← Finset.prod_filter, Finset.filter_univ_mem]
      rfl

lemma coinProb_eq_one (p : E → ℝ) : coinProb p (fun _ => True) = 1 := by
  simpa using coinProb_cylinder p (∅ : Finset E) true

lemma coinProb_false (p : E → ℝ) : coinProb p (fun _ => False) = 0 := by
  simp [coinProb]

lemma exists_of_coinProb_compl_lt_one (p : E → ℝ) (P : (E → Bool) → Prop)
    (h : coinProb p (fun ω => ¬ P ω) < 1) : ∃ ω, P ω := by
  classical
  by_contra hn
  have hEq : coinProb p (fun ω => ¬ P ω) = coinProb p (fun _ => True) :=
    coinProb_congr p fun ω => iff_true_intro (fun hP => hn ⟨ω, hP⟩)
  rw [hEq, coinProb_eq_one] at h
  exact (lt_irrefl _ h)

lemma coinProb_union_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (P Q : (E → Bool) → Prop) :
    coinProb p (fun ω => P ω ∨ Q ω) ≤ coinProb p P + coinProb p Q := by
  classical
  simp only [coinProb, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hω := coinWeight_nonneg p hp ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ, hω]

lemma coinProb_iUnion_le {α : Type*} (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (I : Finset α)
    (P : α → (E → Bool) → Prop) :
    coinProb p (fun ω => ∃ i ∈ I, P i ω) ≤ ∑ i ∈ I, coinProb p (P i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [coinProb]
  | insert a I ha ih =>
    rw [Finset.sum_insert ha]
    have hEq : coinProb p (fun ω => ∃ i ∈ insert a I, P i ω) =
        coinProb p (fun ω => P a ω ∨ ∃ i ∈ I, P i ω) :=
      coinProb_congr p fun ω => by
        constructor
        · rintro ⟨i, hi, hPi⟩
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Or.inl hPi
          · exact Or.inr ⟨i, hi, hPi⟩
        · rintro (hPa | ⟨i, hi, hPi⟩)
          · exact ⟨a, Finset.mem_insert_self _ _, hPa⟩
          · exact ⟨i, Finset.mem_insert_of_mem hi, hPi⟩
    rw [hEq]
    exact (coinProb_union_le p hp _ _).trans (add_le_add_right ih _)

/-- Markov's inequality for the number of events in a finite family that occur. -/
lemma coinProb_count_ge_le {α : Type*} (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (I : Finset α)
    (P : α → (E → Bool) → Prop) [∀ i ω, Decidable (P i ω)] (q : ℕ) (hq : 0 < q) :
    coinProb p (fun ω => q ≤ (I.filter fun i => P i ω).card) ≤
      (∑ i ∈ I, coinProb p (P i)) / q := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [le_div_iff₀ hqR]
  simp only [coinProb, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  have hw := coinWeight_nonneg p hp ω
  have hSum : (∑ i ∈ I, @ite ℝ (P i ω) (Classical.propDecidable _) (coinWeight p ω) 0) =
      coinWeight p ω * (I.filter fun i => P i ω).card := calc
    _ = ∑ i ∈ I, if P i ω then coinWeight p ω else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : P i ω <;> simp [hi]
    _ = _ := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hSum]
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) hw
  · simpa only [zero_mul] using mul_nonneg hw (Nat.cast_nonneg (I.filter fun i => P i ω).card)

/-- The squarefree terms of the multinomial expansion give the factorial-moment bound. -/
private lemma sum_prod_powersetCard_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (S : Finset E) (q : ℕ) :
    (∑ T ∈ S.powersetCard q, ∏ e ∈ T, p e) ≤
      (∑ e ∈ S, p e) ^ q / q.factorial := by
  classical
  have hfac : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  rw [le_div_iff₀ hfac, mul_comm, Finset.mul_sum, Finset.sum_pow_eq_sum_piAntidiag]
  let ind (T : Finset E) (e : E) : ℕ := if e ∈ T then 1 else 0
  let term (k : E → ℕ) : ℝ :=
    (Nat.multinomial S k : ℝ) * ∏ e ∈ S, p e ^ k e
  have hinj : Function.Injective ind := by
    intro A B h
    ext e
    have he := congrFun h e
    by_cases hA : e ∈ A <;> by_cases hB : e ∈ B <;> simp_all [ind]
  have hsub : (S.powersetCard q).image ind ⊆ Finset.piAntidiag S q := by
    intro k hk
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hTS, hq⟩ := Finset.mem_powersetCard.mp hT
    apply Finset.mem_piAntidiag.mpr
    constructor
    · change (∑ e ∈ S, if e ∈ T then 1 else 0 : ℕ) = q
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTS]
      exact hq
    · intro e he
      by_cases hmem : e ∈ T
      · exact hTS hmem
      · exact False.elim (he (by simp [ind, hmem]))
  have hterm (T : Finset E) (hT : T ∈ S.powersetCard q) :
      term (ind T) = (q.factorial : ℝ) * ∏ e ∈ T, p e := by
    obtain ⟨hTS, hq⟩ := Finset.mem_powersetCard.mp hT
    have hsum : (∑ e ∈ S, ind T e) = q :=
      (Finset.mem_piAntidiag.mp (hsub (Finset.mem_image.mpr ⟨T, hT, rfl⟩))).1
    have hprod : (∏ e ∈ S, (ind T e).factorial) = 1 := by
      refine Finset.prod_eq_one fun e _ => ?_
      by_cases he : e ∈ T <;> simp [ind, he]
    have hcoeff : Nat.multinomial S (ind T) = q.factorial := by
      have h := Nat.multinomial_spec S (ind T)
      simpa only [hprod, one_mul, hsum] using h
    have hfilter : (S.filter fun e => e ∈ T) = T := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTS]
    have hpowers : (∏ e ∈ S, p e ^ ind T e) = ∏ e ∈ T, p e := by
      calc
        (∏ e ∈ S, p e ^ ind T e) = ∏ e ∈ S, if e ∈ T then p e else 1 :=
          Finset.prod_congr rfl fun e _ => by
            by_cases he : e ∈ T <;> simp [ind, he]
        _ = ∏ e ∈ T, p e := by rw [← Finset.prod_filter, hfilter]
    simp only [term, hcoeff, hpowers]
  calc
    (∑ T ∈ S.powersetCard q, (q.factorial : ℝ) * ∏ e ∈ T, p e) =
        ∑ k ∈ (S.powersetCard q).image ind, term k := by
      rw [Finset.sum_image (hinj.injOn)]
      exact Finset.sum_congr rfl fun T hT => (hterm T hT).symm
    _ ≤ ∑ k ∈ Finset.piAntidiag S q, term k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun e _ => pow_nonneg (hp e) _)

/-- Upper tail for the number of present coordinates, using a factorial moment. -/
lemma coinProb_card_ge_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (S : Finset E) (q : ℕ) :
    coinProb p (fun ω => q ≤ (S.filter fun e => ω e = true).card) ≤
      (∑ e ∈ S, p e) ^ q / q.factorial := by
  classical
  calc
    coinProb p (fun ω => q ≤ (S.filter fun e => ω e = true).card) ≤
        coinProb p (fun ω => ∃ T ∈ S.powersetCard q, ∀ e ∈ T, ω e = true) := by
      apply coinProb_mono p hp
      intro ω hω
      obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
      refine ⟨T, Finset.mem_powersetCard.mpr ⟨hT.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
      intro e he
      exact (Finset.mem_filter.mp (hT he)).2
    _ ≤ ∑ T ∈ S.powersetCard q, coinProb p (fun ω => ∀ e ∈ T, ω e = true) :=
      coinProb_iUnion_le p hp _ _
    _ = ∑ T ∈ S.powersetCard q, ∏ e ∈ T, p e := by
      refine Finset.sum_congr rfl fun T _ => ?_
      simpa using coinProb_cylinder p T true
    _ ≤ (∑ e ∈ S, p e) ^ q / q.factorial :=
      sum_prod_powersetCard_le p (fun e => (hp e).1) S q

end Erdos1111
