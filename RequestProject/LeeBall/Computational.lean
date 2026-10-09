module

public import RequestProject.LeeBall.Basic

/-!
# Statements resting on the manuscript's Maple computations (not proved here)

The following results of the manuscript are established there by large computer-algebra
computations (Maple: Gröbner bases, sequences `𝓢`, `𝓖`, exhaustive searches).  As agreed, their
proofs are not reproduced; we only record precise statements, as propositions (definitions of
type `Prop`), so that they can be referred to.  Nothing in the project depends on them.

* `MainComputationalClaim` — Theorem 5.1;
* `Prop512Claim` — Proposition 5.12 (`n = 84, 437, 590, 597, 836`, `r = 3`).
-/

@[expose] public section

namespace LeeBall

/-- **Theorem 5.1** (statement only; proved in the manuscript by computation).  For `n ≥ 3`,
`r ≥ 2` and `|Bⁿ(r)| < 2³⁰` there is no lattice tiling of `ℤⁿ` by `Bⁿ(r)`, except possibly for
`(n, r) = (35, 3)` and `(805, 3)`. -/
def MainComputationalClaim : Prop :=
  ∀ n r : ℕ, 3 ≤ n → 2 ≤ r → (leeBall n r).card < 2 ^ 30 →
    (n, r) ≠ (35, 3) → (n, r) ≠ (805, 3) → ¬ HasLatticeTiling (leeBall n r)

/-- **Proposition 5.12** (statement only; proved in the manuscript by computation).  There is
no lattice tiling of `ℤⁿ` by `Bⁿ(3)` for `n = 84, 437, 590, 597, 836`. -/
def Prop512Claim : Prop :=
  ∀ n ∈ ({84, 437, 590, 597, 836} : Finset ℕ), ¬ HasLatticeTiling (leeBall n 3)

/-! ### The non-computational step of the proof of Theorem 5.1 -/

/-- Monotonicity of `|Bⁿ(r)|` in both `n` and `r`. -/
theorem card_leeBall_mono {n n' r r' : ℕ} (hn : n ≤ n') (hr : r ≤ r') :
    (leeBall n r).card ≤ (leeBall n' r').card := by
  rw [card_leeBall, card_leeBall, stantonCowan_eq_range, stantonCowan_eq_range]
  calc ∑ i ∈ Finset.range (r + 1), 2 ^ i * n.choose i * r.choose i
      ≤ ∑ i ∈ Finset.range (r + 1), 2 ^ i * n'.choose i * r'.choose i :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul (Nat.mul_le_mul_left _
          (Nat.choose_le_choose _ hn)) (Nat.choose_le_choose _ hr)
    _ ≤ ∑ i ∈ Finset.range (r' + 1), 2 ^ i * n'.choose i * r'.choose i :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

/-- `|B¹³(13)| = 1 409 933 619 > 2³⁰`. -/
theorem card_leeBall_13_13 : (leeBall 13 13).card = 1409933619 := by
  rw [card_leeBall]; decide

/-- In the proof of Theorem 5.1: if `n ≥ 13` and `r ≥ 13` then `|Bⁿ(r)| > 2³⁰`. -/
theorem card_leeBall_gt_of_ge_13 {n r : ℕ} (hn : 13 ≤ n) (hr : 13 ≤ r) :
    2 ^ 30 < (leeBall n r).card :=
  lt_of_lt_of_le (by rw [card_leeBall_13_13]; norm_num) (card_leeBall_mono hn hr)

end LeeBall
