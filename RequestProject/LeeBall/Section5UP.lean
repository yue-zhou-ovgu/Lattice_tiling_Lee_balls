module

public import RequestProject.LeeBall.Section5

/-!
# Theorem 5.9: an uncertainty principle for the zeros of `𝓢`

The manuscript derives Theorem 5.9 from the uncertainty principle of Feng–Hollmann–Xiang.  Here
we prove the needed special case directly: a nonzero function on the squares supported on `s`
points cannot have `s` consecutive vanishing "Fourier coefficients" `S_{2k}` (Vandermonde), and a
double-counting argument over cyclic windows then gives `h ≤ s · #{k : S_{2k} ≠ 0}`.
-/

@[expose] public section

open Finset

namespace LeeBall

/-- A nonzero combination of `s` distinct nonzero geometric sequences cannot vanish at `s`
consecutive exponents. -/
lemma vandermonde_window {F : Type*} [Field F] [DecidableEq F] (A : Finset F) (c : F → F)
    (hA0 : ∀ a ∈ A, a ≠ 0) (hc : ∀ a ∈ A, c a ≠ 0) (hne : A.Nonempty) (k₀ : ℕ) :
    ∃ l < A.card, ∑ a ∈ A, c a * a ^ (k₀ + l) ≠ 0 := by
  by_contra H
  push_neg at H
  set s := A.card
  let e : A ≃ Fin s := A.equivFin
  let v : Fin s → F := fun i => (e.symm i : F)
  have hv : Function.Injective v := fun i j h => e.symm.injective (Subtype.ext h)
  let w : Fin s → F := fun i => c (v i) * v i ^ k₀
  have hreidx : ∀ f : F → F, ∑ i, f (v i) = ∑ a ∈ A, f a := by
    intro f
    rw [← Finset.sum_coe_sort A f]
    exact Equiv.sum_comp e.symm (fun a : A => f a)
  have hM : (Matrix.vandermonde v).transpose.mulVec w = 0 := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply, w]
    have := H l l.2
    rw [← hreidx (fun a => c a * a ^ (k₀ + l))] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]; ring
  have hdet : (Matrix.vandermonde v).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact Matrix.det_vandermonde_ne_zero_iff.2 hv
  have hw := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
  obtain ⟨a, ha⟩ := hne
  have := congrFun hw (e ⟨a, ha⟩)
  simp only [w, v, Equiv.symm_apply_apply, Pi.zero_apply] at this
  exact mul_ne_zero (hc a ha) (pow_ne_zero _ (hA0 a ha)) this

/-- Sums of an `h`-periodic sequence over a window of length `h` do not depend on the shift. -/
lemma periodic_sum_shift (F : ℕ → ℕ) (h : ℕ) (hF : ∀ c, F (c + h) = F c) (l : ℕ) :
    ∑ c ∈ range h, F (c + l) = ∑ c ∈ range h, F c := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h1 := Finset.sum_range_succ (fun c => F (c + l)) h
    have h2 := Finset.sum_range_succ' (fun c => F (c + l)) h
    have h3 : F (h + l) = F (0 + l) := by rw [add_comm h l, hF, zero_add]
    simp only [show ∀ c, c + 1 + l = c + (l + 1) by intro c; ring] at h2
    omega

variable {n p : ℕ}

/-- **Theorem 5.9** (in the form valid for every `x ∈ 𝔽_pⁿ`).  Let `h = (p-1)/2` and let `t` be the
number of zeros among `S₂, S₄, …, S_{p-1}`.  Then either all of them vanish (`t = h`), or
`t ≤ (p-1)(n-1)/(2n)`, i.e. `2 n t ≤ (p-1)(n-1)`. -/
theorem zeros_S_up [hp : Fact p.Prime] (hp2 : 2 < p) (x : Fin n → ZMod p) :
    ((Icc 1 ((p - 1) / 2)).filter fun k => ∑ j, x j ^ (2 * k) = 0).card = (p - 1) / 2 ∨
      2 * n * ((Icc 1 ((p - 1) / 2)).filter fun k => ∑ j, x j ^ (2 * k) = 0).card ≤
        (p - 1) * (n - 1) := by
  classical
  have hpodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · omega
    · exact h
  set h := (p - 1) / 2 with hh
  set S : ℕ → ZMod p := fun k => ∑ j, x j ^ (2 * k) with hSdef
  set Z := ((Icc 1 h).filter fun k => S k = 0).card
  let g : ZMod p → ZMod p := fun a => ((univ.filter fun j => x j ^ 2 = a).card : ZMod p)
  let A := (univ.image fun j => x j ^ 2).filter fun a => a ≠ 0 ∧ g a ≠ 0
  have hS : ∀ k, 1 ≤ k → S k = ∑ a ∈ A, g a * a ^ k := by
    intro k hk
    have h1 : S k = ∑ a ∈ univ.image (fun j => x j ^ 2), g a * a ^ k := by
      simp only [hSdef, pow_mul]
      rw [Finset.sum_comp (fun a => a ^ k) (fun j => x j ^ 2)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [nsmul_eq_mul]
    rw [h1]
    refine (Finset.sum_filter_of_ne fun a _ ha => ?_).symm
    refine ⟨fun h0 => ha ?_, fun h0 => ha ?_⟩
    · rw [h0, zero_pow (by omega), mul_zero]
    · rw [h0, zero_mul]
  have hAcard : A.card ≤ n := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    simp
  have hIcc : (Icc 1 h).card = h := by simp
  by_cases hA : A = ∅
  · left
    show ((Icc 1 h).filter fun k => S k = 0).card = h
    rw [Finset.filter_true_of_mem fun k hk => by
      rw [hS k (Finset.mem_Icc.1 hk).1, hA, Finset.sum_empty], hIcc]
  right
  have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.2 hA
  set s := A.card
  have hwin : ∀ k₀, 1 ≤ k₀ → ∃ l < s, S (k₀ + l) ≠ 0 := by
    intro k₀ hk₀
    obtain ⟨l, hl, hne⟩ := vandermonde_window A g (fun a ha => (Finset.mem_filter.1 ha).2.1)
      (fun a ha => (Finset.mem_filter.1 ha).2.2) hAne k₀
    exact ⟨l, hl, by rw [hS _ (by omega)]; exact hne⟩
  let Fs : ℕ → ℕ := fun c => if S (c + 1) = 0 then 0 else 1
  have hper : ∀ c, Fs (c + h) = Fs c := by
    intro c
    have : S (c + h + 1) = S (c + 1) := by
      simp only [hSdef]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hx : x j = 0
      · rw [hx, zero_pow (by omega), zero_pow (by omega)]
      · rw [show 2 * (c + h + 1) = 2 * (c + 1) + (p - 1) by omega, pow_add,
          ZMod.pow_card_sub_one_eq_one hx, mul_one]
    simp only [Fs, show c + h + 1 = c + h + 1 from rfl, this]
  have hsumF : ∑ c ∈ range h, Fs c + Z = h := by
    have : ∑ c ∈ range h, Fs c = ((Icc 1 h).filter fun k => ¬ S k = 0).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
      · intro c hc; simp only [mem_range] at hc; simp only [mem_Icc]; omega
      · intro k hk; simp only [mem_Icc] at hk; simp only [mem_range]; omega
      · intro c _; simp
      · intro k hk; simp only [mem_Icc] at hk; simp only; omega
      · intro c _; simp only [Fs]; split_ifs <;> rfl
    rw [this, add_comm, Finset.filter_card_add_filter_neg_card_eq_card, hIcc]
  have hcount : h ≤ s * ∑ c ∈ range h, Fs c := by
    calc h = ∑ _c ∈ range h, 1 := by simp
      _ ≤ ∑ c ∈ range h, ∑ l ∈ range s, Fs (c + l) := Finset.sum_le_sum fun c _ => by
          obtain ⟨l, hl, hne⟩ := hwin (c + 1) (by omega)
          have : Fs (c + l) = 1 := by
            simp only [Fs, show c + l + 1 = c + 1 + l by ring, if_neg hne]
          rw [← this]
          exact Finset.single_le_sum (f := fun l => Fs (c + l)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.2 hl)
      _ = ∑ l ∈ range s, ∑ c ∈ range h, Fs (c + l) := Finset.sum_comm
      _ = ∑ l ∈ range s, ∑ c ∈ range h, Fs c :=
          Finset.sum_congr rfl fun l _ => periodic_sum_shift Fs h hper l
      _ = s * ∑ c ∈ range h, Fs c := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  set q := ∑ c ∈ range h, Fs c
  have hnq : h ≤ n * q := hcount.trans (Nat.mul_le_mul_right _ hAcard)
  have hp1 : p - 1 = 2 * h := by omega
  rw [hp1]
  rcases n with _ | n'
  · simp
  · have key : (n' + 1) * Z + h ≤ h * (n' + 1) := by nlinarith
    simp only [Nat.add_sub_cancel]
    nlinarith

/-- **Theorem 5.9** as a nonexistence criterion.  If for every solution `Y` of the system of
Theorem 4.3 the number `t` of zeros among `Y₁, …, Y_{(p-1)/2}` (i.e. among `S₂, …, S_{p-1}`)
satisfies `t ≠ (p-1)/2` and `t > (p-1)(n-1)/(2n)`, then there is no lattice tiling. -/
theorem no_tiling_of_up {r m : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p)
    (h : ∀ Y : ℕ → ZMod p, YSystem n r m p Y →
      ((Icc 1 ((p - 1) / 2)).filter fun k => Y k = 0).card ≠ (p - 1) / 2 ∧
      (p - 1) * (n - 1) < 2 * n * ((Icc 1 ((p - 1) / 2)).filter fun k => Y k = 0).card) :
    ¬ HasLatticeTiling (leeBall n r) := by
  intro ht
  obtain ⟨x, hx⟩ := exists_tilingImage_of_tiling hB ht
  obtain ⟨h1, h2⟩ := h _ (hx.ySystem hp2)
  rcases zeros_S_up hp2 x with h3 | h3
  · exact h1 h3
  · exact absurd h3 (not_le.2 h2)

end LeeBall
