module

public import RequestProject.LeeBall.Bell

/-!
# The one–dimensional moment identity

This file proves the one-variable case of Theorem 3.2 of the manuscript:
```
∑_{a ∈ ℤ} q^{|a|} a^{2j} / (2j)! = (1+q)/(1-q) · [w^{2j}] exp(2 ∑_{i ≥ 1} A_i(q) w^{2i} / (2i)!)
```
with `A_i(q) = ∑_{s ≥ 1} s^{2i-1} q^s`.  The proof checks the differential equation
characterising `bellSeries` (see `LeeBall.eq_C_mul_bellSeries`) coefficientwise.
-/

@[expose] public section

open Finset PowerSeries

namespace LeeBall

/-- `∑_{a ∈ {t, -t}} a^m`, the contribution of `S¹(t)` to the `m`-th moment. -/
def symPow (t m : ℕ) : ℚ := ∑ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ), (a : ℚ) ^ m

/-- The weight `|S¹(t)|`: `1` if `t = 0` and `2` otherwise. -/
def sw (t : ℕ) : ℚ := if t = 0 then 1 else 2

lemma symPow_even (t m : ℕ) : symPow t (2 * m) = sw t * (t : ℚ) ^ (2 * m) := by
  unfold symPow sw
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [Finset.sum_pair (by omega)]
    simp only [if_neg ht.ne', Int.cast_neg, Int.cast_natCast, Even.neg_pow (even_two_mul m)]
    ring

lemma symPow_odd (t m : ℕ) : symPow t (2 * m + 1) = 0 := by
  unfold symPow
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [Finset.sum_pair (by omega)]
    simp [Odd.neg_pow (odd_two_mul_add_one m)]

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ m ∈ range (2 * k), f m = ∑ i ∈ range k, (f (2 * i) + f (2 * i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    abel

lemma add_pow_add_sub_pow_odd (s t : ℚ) (l : ℕ) :
    (s + t) ^ (2 * l + 1) + (s - t) ^ (2 * l + 1) =
      2 * ∑ i ∈ range (l + 1), ((2 * l + 1).choose (2 * i + 1) : ℚ) * s ^ (2 * i + 1) *
        t ^ (2 * (l - i)) := by
  rw [sub_eq_add_neg, add_pow, add_pow, ← Finset.sum_add_distrib,
    show 2 * l + 1 + 1 = 2 * (l + 1) by ring, sum_range_two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have h1 : 2 * l + 1 - 2 * i = 2 * (l - i) + 1 := by omega
  have h2 : 2 * l + 1 - (2 * i + 1) = 2 * (l - i) := by omega
  rw [h1, h2, Odd.neg_pow (odd_two_mul_add_one _), Even.neg_pow (even_two_mul _)]
  ring

/-- `∑_{i=1}^{j} 2i C(2j,2i) s^{2i-1} t^{2j-2i} = j ((s+t)^{2j-1} + (s-t)^{2j-1})`. -/
lemma inner_identity (s t : ℚ) (j : ℕ) :
    ∑ p ∈ antidiagonal j, (2 * p.1 : ℚ) * ((2 * j).choose (2 * p.1) : ℚ) *
      s ^ (2 * p.1 - 1) * t ^ (2 * p.2) =
      j * ((s + t) ^ (2 * j - 1) + (s - t) ^ (2 * j - 1)) := by
  rcases j with _ | l
  · simp
  rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega, add_pow_add_sub_pow_odd,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hc : ((2 * (l + 1)).choose (2 * (i + 1)) : ℚ) * (2 * (i + 1) : ℕ) =
      (2 * (l + 1) : ℕ) * ((2 * l + 1).choose (2 * i + 1) : ℚ) := by
    have := Nat.add_one_mul_choose_eq (2 * l + 1) (2 * i + 1)
    rw [show 2 * (l + 1) = 2 * l + 1 + 1 by ring, show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    exact_mod_cast this.symm
  rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, show l + 1 - (i + 1) = l - i by omega]
  push_cast at hc ⊢
  linear_combination (s ^ (2 * i + 1) * t ^ (2 * (l - i))) * hc

/-- `∑_{s+t=N} sw(t) (N^{2j-1} + (s-t)^{2j-1}) = 2 N^{2j}` for `j ≥ 1`. -/
lemma outer_identity (N j : ℕ) (hj : 1 ≤ j) :
    ∑ q ∈ antidiagonal N, sw q.2 * ((N : ℚ) ^ (2 * j - 1) + ((q.1 : ℚ) - q.2) ^ (2 * j - 1)) =
      2 * (N : ℚ) ^ (2 * j) := by
  have hodd : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
  have hrefl : ∑ q ∈ antidiagonal N, ((q.1 : ℚ) - q.2) ^ (2 * j - 1) = 0 := by
    have h := Finset.Nat.sum_antidiagonal_swap (n := N)
      (f := fun q : ℕ × ℕ => ((q.1 : ℚ) - q.2) ^ (2 * j - 1))
    simp only [Prod.fst_swap, Prod.snd_swap] at h
    have h2 : ∑ q ∈ antidiagonal N, ((q.2 : ℚ) - q.1) ^ (2 * j - 1) =
        - ∑ q ∈ antidiagonal N, ((q.1 : ℚ) - q.2) ^ (2 * j - 1) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← hodd.neg_pow, neg_sub]
    linarith
  have hsw : ∀ q : ℕ × ℕ, sw q.2 = 2 - if q.2 = 0 then 1 else 0 := by
    intro q; unfold sw; split_ifs <;> norm_num
  simp_rw [hsw, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
    hrefl, Finset.sum_const, Finset.Nat.card_antidiagonal, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (N, 0)]
  · simp only [if_true, Nat.cast_zero, sub_zero, nsmul_eq_mul, add_zero]
    obtain ⟨o, ho⟩ : ∃ o, 2 * j = o + 1 := ⟨2 * j - 1, by omega⟩
    rw [ho, show o + 1 - 1 = o by omega]
    push_cast; ring
  · rintro ⟨a, b⟩ hb hne
    rw [Finset.mem_antidiagonal] at hb
    have : b ≠ 0 := by rintro rfl; apply hne; simp at hb; simp [hb]
    simp [this]
  · intro h; exact absurd (by simp) h

lemma key_identity (j N : ℕ) :
    (j : ℚ) * (((2 * j).factorial : ℚ)⁻¹ * symPow N (2 * j)) =
      ∑ p ∈ antidiagonal j, (p.1 : ℚ) * ((2 : ℚ) / (2 * p.1).factorial *
        ∑ q ∈ antidiagonal N, (q.1 : ℚ) ^ (2 * p.1 - 1) *
          (((2 * p.2).factorial : ℚ)⁻¹ * symPow q.2 (2 * p.2))) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hterm : ∀ p ∈ antidiagonal j, (p.1 : ℚ) * ((2 : ℚ) / (2 * p.1).factorial *
        ∑ q ∈ antidiagonal N, (q.1 : ℚ) ^ (2 * p.1 - 1) *
          (((2 * p.2).factorial : ℚ)⁻¹ * symPow q.2 (2 * p.2))) =
      ((2 * j).factorial : ℚ)⁻¹ * ∑ q ∈ antidiagonal N, sw q.2 *
        ((2 * p.1 : ℚ) * ((2 * j).choose (2 * p.1) : ℚ) * (q.1 : ℚ) ^ (2 * p.1 - 1) *
          (q.2 : ℚ) ^ (2 * p.2)) := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    have hc : ((2 * j).choose (2 * p.1) : ℚ) * (2 * p.1).factorial * (2 * p.2).factorial =
        (2 * j).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (show 2 * p.1 ≤ 2 * j by omega)
      rw [show 2 * j - 2 * p.1 = 2 * p.2 by omega] at this
      exact_mod_cast this
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [symPow_even, ← hc]
    have h1 : ((2 * p.1).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * p.2).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((2 * j).choose (2 * p.1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hin : ∀ q ∈ antidiagonal N, ∑ p ∈ antidiagonal j, (2 * p.1 : ℚ) *
      ((2 * j).choose (2 * p.1) : ℚ) * (q.1 : ℚ) ^ (2 * p.1 - 1) * (q.2 : ℚ) ^ (2 * p.2) =
      j * ((N : ℚ) ^ (2 * j - 1) + ((q.1 : ℚ) - q.2) ^ (2 * j - 1)) := by
    intro q hq
    rw [inner_identity]
    rw [Finset.mem_antidiagonal] at hq
    rw [show (q.1 : ℚ) + q.2 = N by exact_mod_cast hq]
  rw [Finset.sum_congr rfl fun q hq => by rw [hin q hq]]
  simp_rw [mul_left_comm (sw _) (j : ℚ), ← Finset.mul_sum, outer_identity N j hj, symPow_even]
  unfold sw
  split_ifs with hN
  · subst hN; simp only [Nat.cast_zero, zero_pow (show 2 * j ≠ 0 by omega)]; ring
  · ring

/-- The series `(1+q)/(1-q) = 1 + 2q + 2q² + ⋯`. -/
noncomputable def pSeriesQ : ℚ⟦X⟧ := mk fun r => sw r

/-- The series `A_j(q) = ∑_{s ≥ 1} s^{2j-1} q^s`. -/
noncomputable def aSeriesQ (j : ℕ) : ℚ⟦X⟧ := mk fun s => (s : ℚ) ^ (2 * j - 1)

/-- The sequence `j ↦ 2 A_j(q) / (2j)!`. -/
noncomputable def zSeqQ (j : ℕ) : ℚ⟦X⟧ := C ((2 : ℚ) / (2 * j).factorial) * aSeriesQ j

/-- The one-dimensional moment series `∑_t (∑_{a = ±t} a^{2j}) q^t / (2j)!`. -/
noncomputable def oneDimQ (j : ℕ) : ℚ⟦X⟧ :=
  mk fun t => ((2 * j).factorial : ℚ)⁻¹ * symPow t (2 * j)

/-- One-dimensional case of Theorem 3.2. -/
theorem oneDimQ_eq (j : ℕ) : oneDimQ j = pSeriesQ * bellPart zSeqQ j := by
  have h := eq_C_mul_bellSeries (F := (mk oneDimQ : PowerSeries ℚ⟦X⟧)) zSeqQ ?_
  · have h2 := congrArg (coeff j) h
    rw [coeff_mk, coeff_C_mul, bellSeries, coeff_mk] at h2
    rw [h2]
    congr 1
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    ext t
    simpa [oneDimQ, pSeriesQ] using symPow_even t 0
  ext j N
  rw [coeff_euler, coeff_mul, coeff_mk, map_sum]
  simp only [logDerSeries, coeff_mk, zSeqQ, smul_mul_assoc, map_smul, smul_eq_mul,
    mul_assoc, coeff_C_mul]
  simp only [coeff_mul, oneDimQ, aSeriesQ, coeff_mk]
  exact key_identity j N

end LeeBall
