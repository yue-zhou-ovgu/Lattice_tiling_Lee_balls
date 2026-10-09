module

public import RequestProject.LeeBall.Ideal

/-!
# Section 4: periodicity, the case `p = 5`, and Corollaries 4.5 and 4.6

* Lemma 4.7: `n ↦ ∑ᵢ aᵢ C(n,i) mod p` has period `p^{⌈log_p (r+1)⌉}`;
* Example 4.4: the two sufficient conditions for `p = 5`;
* Corollaries 4.5 and 4.6: nonexistence for `r = 6, 7` and `n` in certain classes mod `125`.
-/

@[expose] public section

open Finset

namespace LeeBall

/-- If `q ∣ C(P, l)` for `1 ≤ l ≤ i`, then `C(n + P, i) ≡ C(n, i) (mod q)`. -/
lemma choose_add_cast_eq {q P i : ℕ} (hP : ∀ l, 1 ≤ l → l ≤ i → ((P.choose l : ℕ) : ZMod q) = 0)
    (n : ℕ) : (((n + P).choose i : ℕ) : ZMod q) = ((n.choose i : ℕ) : ZMod q) := by
  rw [Nat.add_choose_eq, Nat.cast_sum, Finset.sum_eq_single (i, 0)]
  · simp
  · rintro ⟨j, l⟩ hjl hne
    rw [Finset.mem_antidiagonal] at hjl
    have hl : l ≠ 0 := by
      rintro rfl; apply hne; simp_all
    rw [Nat.cast_mul, hP l (Nat.one_le_iff_ne_zero.2 hl) (by omega), mul_zero]
  · intro h; simp at h

/-- **Lemma 4.7.** Let `p` be prime and `a₀, …, a_r ∈ ℤ`.  Then
`f(n) = ∑_{i=0}^{r} aᵢ C(n, i) mod p` is periodic in `n` with period `p^{⌈log_p (r+1)⌉}`. -/
theorem binom_sum_periodic {p : ℕ} (hp : p.Prime) (r : ℕ) (a : ℕ → ℤ) (n : ℕ) :
    ((∑ i ∈ range (r + 1), a i * ((n + p ^ Nat.clog p (r + 1)).choose i : ℤ) : ℤ) : ZMod p) =
      ((∑ i ∈ range (r + 1), a i * (n.choose i : ℤ) : ℤ) : ZMod p) := by
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have hr : r + 1 ≤ p ^ Nat.clog p (r + 1) := Nat.le_pow_clog hp.one_lt _
  rw [Finset.mem_range] at hi
  exact_mod_cast choose_add_cast_eq (fun l hl1 hli => by
    rw [ZMod.natCast_eq_zero_iff]
    exact hp.dvd_choose_pow (by omega) (by omega)) n

/-! ### Periodicity modulo `25` with period `125` -/

lemma choose_125_cast {l : ℕ} (hl1 : 1 ≤ l) (hl : l ≤ 7) :
    (((125 : ℕ).choose l : ℕ) : ZMod 25) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  rw [Nat.choose_eq_descFactorial_div_factorial]
  interval_cases l <;> decide +kernel

lemma card_leeBall_add_125 {i : ℕ} (hi : i ≤ 7) (n : ℕ) :
    (((leeBall (n + 125) i).card : ℕ) : ZMod 25) = (((leeBall n i).card : ℕ) : ZMod 25) := by
  rw [card_leeBall, card_leeBall, stantonCowan_eq_range, stantonCowan_eq_range]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [choose_add_cast_eq (fun l hl1 hl => choose_125_cast hl1 (by omega)) n]

lemma compSum_add_125 {r : ℕ} (hr : r ≤ 7) (L : List ℕ) (n : ℕ) :
    ((compSum (n + 125) r L : ℕ) : ZMod 25) = ((compSum n r L : ℕ) : ZMod 25) := by
  unfold compSum
  push_cast
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcl : c (Fin.last _) ≤ r := by
    unfold compositions at hc
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hc
    rw [← hc.1]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  rw [card_leeBall_add_125 (hcl.trans hr)]

lemma cInt_add_125 {r : ℕ} (hr : r ≤ 7) {k : ℕ} (q : k.Partition) (n : ℕ) :
    ((cInt (n + 125) r q : ℤ) : ZMod 25) = ((cInt n r q : ℤ) : ZMod 25) := by
  unfold cInt
  push_cast
  rw [compSum_add_125 hr]

lemma card_leeBall_mod_125 {i : ℕ} (hi : i ≤ 7) (n : ℕ) :
    (((leeBall n i).card : ℕ) : ZMod 25) = (((leeBall (n % 125) i).card : ℕ) : ZMod 25) := by
  conv_lhs => rw [← Nat.mod_add_div n 125]
  induction n / 125 with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, card_leeBall_add_125 hi, ih]

lemma cInt_mod_125 {r : ℕ} (hr : r ≤ 7) {k : ℕ} (q : k.Partition) (n : ℕ) :
    ((cInt n r q : ℤ) : ZMod 25) = ((cInt (n % 125) r q : ℤ) : ZMod 25) := by
  conv_lhs => rw [← Nat.mod_add_div n 125]
  induction n / 125 with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, cInt_add_125 hr, ih]

/-! ### Computable forms of `|Bⁿ(r)|` and `c_λ` -/

/-- A fast formula for the Stanton–Cowan number. -/
def scFast (n r : ℕ) : ℕ :=
  ∑ i ∈ range (r + 1), 2 ^ i * (n.descFactorial i / i.factorial) * r.choose i

lemma stantonCowan_eq_scFast (n r : ℕ) : stantonCowan n r = scFast n r := by
  rw [stantonCowan_eq_range, scFast]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.choose_eq_descFactorial_div_factorial]

/-- `compSum` with `|Bⁿ(i)|` replaced by the Stanton–Cowan number (computable). -/
def compSumC (n r : ℕ) (L : List ℕ) : ℕ :=
  ∑ c ∈ compositions L.length r,
    scFast n (c (Fin.last _)) * ∏ j : Fin L.length, (c j.castSucc) ^ (2 * L[j] - 1)

/-- `cInt` with `|Bⁿ(i)|` replaced by the Stanton–Cowan number (computable). -/
def cIntC (n r : ℕ) {k : ℕ} (p : k.Partition) : ℤ :=
  2 ^ p.parts.card * ((p.parts.map (2 * ·)).bell : ℤ) * (compSumC n r (partList p) : ℤ)

lemma cInt_eq_cIntC (n r : ℕ) {k : ℕ} (p : k.Partition) : cInt n r p = cIntC n r p := by
  simp only [cInt, cIntC, compSum, compSumC, card_leeBall, stantonCowan_eq_scFast]

/-! ### Example 4.4: the case `p = 5` -/

/-- The partition `(1, 1)` of `2`. -/
def part11 : Nat.Partition 2 := ⟨{1, 1}, fun h => by simp at h; omega, rfl⟩

lemma partition_two_cases (q : Nat.Partition 2) :
    q = Nat.Partition.indiscrete 2 ∨ q = part11 := by
  by_cases h2 : 2 ∈ q.parts
  · exact Or.inl (partition_eq_indiscrete_of_mem q h2)
  · right
    have h1 : ∀ i ∈ q.parts, i = 1 := fun i hi => by
      have := q.parts_pos hi; have := q.le_of_mem_parts hi
      have : i ≠ 2 := fun h => h2 (h ▸ hi)
      omega
    have hrep := Multiset.eq_replicate_card.2 h1
    have hsum := q.parts_sum
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_one] at hsum
    ext1
    rw [hrep, hsum]
    rfl

/-- **Example 4.4.** Let `p = 5`, with `5 ∣ |Bⁿ(r)|` and `25 ∤ |Bⁿ(r)|`.  If either
`c_{(1)} ≢ 0, c_{(2)} ≡ 0 (mod 5)` or `c_{(1,1)} ≡ 0, c_{(2)} ≡ 0 (mod 5)`, then there is no
lattice tiling of `ℤⁿ` by `Bⁿ(r)`. -/
theorem no_tiling_p5 {n r : ℕ} (h5 : 5 ∣ (leeBall n r).card) (h25 : ¬ 25 ∣ (leeBall n r).card)
    (hc : ((cInt n r (Nat.Partition.indiscrete 1) : ZMod 5) ≠ 0 ∧
        (cInt n r (Nat.Partition.indiscrete 2) : ZMod 5) = 0) ∨
      ((cInt n r part11 : ZMod 5) = 0 ∧ (cInt n r (Nat.Partition.indiscrete 2) : ZMod 5) = 0)) :
    ¬ HasLatticeTiling (leeBall n r) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := h5
  have hB : (leeBall n r).card = m * 5 := by rw [hm, mul_comm]
  have hm5 : ¬ 5 ∣ m := by
    rintro ⟨k, rfl⟩; exact h25 ⟨k, by rw [hm]; ring⟩
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine no_tiling_of_p_condition (p := 5) (by norm_num) hB hm5 (fun k hk1 hk2 => ?_) h2
    have : k = 1 := by norm_num at hk2; omega
    subst this; exact h1
  · refine no_tiling_of_all_c_zero (p := 5) (by norm_num) hB hm5 fun q => ?_
    rcases partition_two_cases q with rfl | rfl
    · exact h2
    · exact h1

/-- `c_{(1)}`, `c_{(2)}` and `c_{(1,1)}` in computable form. -/
def c1C (n r : ℕ) : ℤ := 2 * (compSumC n r [1] : ℤ)
def c2C (n r : ℕ) : ℤ := 2 * (compSumC n r [2] : ℤ)
def c11C (n r : ℕ) : ℤ := 12 * (compSumC n r [1, 1] : ℤ)

lemma cInt_one (n r : ℕ) : cInt n r (Nat.Partition.indiscrete 1) = c1C n r := by
  rw [cInt_eq_cIntC, cIntC, c1C, partList, Nat.Partition.indiscrete_parts one_ne_zero]
  simp [Multiset.bell, Nat.multinomial]

lemma cInt_two (n r : ℕ) : cInt n r (Nat.Partition.indiscrete 2) = c2C n r := by
  rw [cInt_eq_cIntC, cIntC, c2C, partList, Nat.Partition.indiscrete_parts two_ne_zero]
  simp [Multiset.bell, Nat.multinomial, Nat.div_self (Nat.factorial_pos 4)]

lemma cInt_part11 (n r : ℕ) : cInt n r part11 = c11C n r := by
  have hs : (part11.parts.sort (· ≥ ·)) = [1, 1] := by
    rw [show part11.parts = ↑[1, 1] from rfl, Multiset.coe_sort, List.mergeSort_eq_self]
    simp
  rw [cInt_eq_cIntC, cIntC, c11C, partList, hs]
  have hb : (part11.parts.map (2 * ·)).bell = 3 := by
    rw [show part11.parts = {1, 1} from rfl]
    simp [Multiset.bell, Nat.multinomial]; decide
  rw [hb, show part11.parts.card = 2 from rfl]
  norm_num

/-- The (computable) conditions of Example 4.4 at a given `(n, r)`, as residues of integers. -/
def ex44cond (n r : ℕ) : Prop :=
  scFast n r % 25 ≠ 0 ∧ scFast n r % 5 = 0 ∧
    ((c1C n r % 5 ≠ 0 ∧ c2C n r % 5 = 0) ∨ (c11C n r % 5 = 0 ∧ c2C n r % 5 = 0))

instance (n r : ℕ) : Decidable (ex44cond n r) := by unfold ex44cond; infer_instance

lemma cast25_to_5_nat {a b : ℕ} (h : (a : ZMod 25) = b) : (a : ZMod 5) = b := by
  have := congrArg (ZMod.castHom (by norm_num : 5 ∣ 25) (ZMod 5)) h
  simpa using this

lemma cast25_to_5_int {a b : ℤ} (h : (a : ZMod 25) = b) : (a : ZMod 5) = b := by
  have := congrArg (ZMod.castHom (by norm_num : 5 ∣ 25) (ZMod 5)) h
  simpa using this

lemma intCast_zmod5_eq_zero_iff (a : ℤ) : (a : ZMod 5) = 0 ↔ a % 5 = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact Int.dvd_iff_emod_eq_zero

/-- If the conditions of Example 4.4 hold for `(n mod 125, r)` with `r ≤ 7`, then there is no
lattice tiling of `ℤⁿ` by `Bⁿ(r)`. -/
theorem no_tiling_of_ex44cond {n r : ℕ} (hr : r ≤ 7) (h : ex44cond (n % 125) r) :
    ¬ HasLatticeTiling (leeBall n r) := by
  obtain ⟨h25, h5, hc⟩ := h
  have hB := card_leeBall_mod_125 hr n
  rw [card_leeBall (n % 125), stantonCowan_eq_scFast] at hB
  have hc' : ∀ {k : ℕ} (q : k.Partition),
      (cInt n r q : ZMod 5) = (cInt (n % 125) r q : ZMod 5) := fun q =>
    cast25_to_5_int (cInt_mod_125 hr q n)
  refine no_tiling_p5 ?_ ?_ ?_
  · rw [← ZMod.natCast_eq_zero_iff, cast25_to_5_nat hB, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero h5
  · rw [← ZMod.natCast_eq_zero_iff, hB, ZMod.natCast_eq_zero_iff]
    exact fun h => h25 (Nat.mod_eq_zero_of_dvd h)
  · simp only [hc']
    simp only [cInt_one, cInt_two, cInt_part11, ne_eq, intCast_zmod5_eq_zero_iff]
    exact hc

/-- **Corollary 4.5.** If `n ≡ 10, 22, 35, 47, 60, 72, 97, 110, 122 (mod 125)`, there is no lattice
tiling of `ℤⁿ` by `Bⁿ(6)`. -/
theorem no_tiling_r6 (n : ℕ)
    (hn : n % 125 ∈ ({10, 22, 35, 47, 60, 72, 97, 110, 122} : Finset ℕ)) :
    ¬ HasLatticeTiling (leeBall n 6) := by
  have key : ∀ n₀ ∈ ({10, 22, 35, 47, 60, 72, 97, 110, 122} : Finset ℕ), ex44cond n₀ 6 := by
    decide +kernel
  exact no_tiling_of_ex44cond (by norm_num) (key _ hn)

/-- **Corollary 4.6.** If `n ≡ 8, 10, 12, 13, 14, 23, 33, 35, 37, 38, 39, 48, 58, 63, 73, 83, 85,
87, 88, 89, 98, 108, 110, 112, 113, 114, 123 (mod 125)`, there is no lattice tiling of `ℤⁿ` by
`Bⁿ(7)`. -/
theorem no_tiling_r7 (n : ℕ)
    (hn : n % 125 ∈ ({8, 10, 12, 13, 14, 23, 33, 35, 37, 38, 39, 48, 58, 63, 73, 83, 85, 87, 88,
      89, 98, 108, 110, 112, 113, 114, 123} : Finset ℕ)) :
    ¬ HasLatticeTiling (leeBall n 7) := by
  have key : ∀ n₀ ∈ ({8, 10, 12, 13, 14, 23, 33, 35, 37, 38, 39, 48, 58, 63, 73, 83, 85, 87, 88,
      89, 98, 108, 110, 112, 113, 114, 123} : Finset ℕ), ex44cond n₀ 7 := by
    decide +kernel
  exact no_tiling_of_ex44cond (by norm_num) (key _ hn)

end LeeBall
