module

public import Mathlib

/-!
# Theorem 2.7: characters of a subgroup `H ≤ 𝔽_p^*`

For a subgroup `H` of the multiplicative group `(𝔽_p^*, ×)` the characters are `χ_s(h) = h^s`,
`s = 0, …, |H| - 1`.  We prove
* (a) `∑_{s=0}^{|H|-1} χ_s(a) = 0` for `a ∈ H`, `a ≠ 1`;
* (b) Fourier inversion: `g(x) = |H|⁻¹ ∑_{s=0}^{|H|-1} ĝ(χ_s) χ_s(x)` with
  `ĝ(χ_s) = ∑_{h ∈ H} g(h) h^{-s}`.
-/

@[expose] public section

open Finset

namespace LeeBall

variable {p : ℕ} [Fact p.Prime] (H : Subgroup (ZMod p)ˣ) [Fintype H]

/-- **Theorem 2.7 (a).** For `a ∈ H` with `a ≠ 1`, `∑_{s=0}^{|H|-1} a^s = 0`. -/
theorem sum_char_eq_zero {a : (ZMod p)ˣ} (ha : a ∈ H) (ha1 : a ≠ 1) :
    ∑ s ∈ range (Fintype.card H), ((a : ZMod p)) ^ s = 0 := by
  have hpow : ((a : ZMod p)) ^ Fintype.card H = 1 := by
    have : (⟨a, ha⟩ : H) ^ Fintype.card H = 1 := pow_card_eq_one
    have h2 : a ^ Fintype.card H = 1 := by
      have h3 := congrArg Subtype.val this
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h3
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have hne : (a : ZMod p) ≠ 1 := fun h => ha1 (Units.ext h)
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- `|H|` is invertible in `𝔽_p` (it divides `p - 1`). -/
lemma card_subgroup_units_ne_zero : (Fintype.card H : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hdvd : Fintype.card H ∣ p - 1 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out)] at this
  have hpos : 0 < Fintype.card H := Fintype.card_pos
  have hp := (Fact.out : p.Prime).two_le
  have := Nat.le_of_dvd hpos h
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The Fourier transform `ĝ(χ_s) = ∑_{h ∈ H} g(h) h^{-s}`. -/
noncomputable def fourierUnits (g : H → ZMod p) (s : ℕ) : ZMod p :=
  ∑ h : H, g h * ((((h : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ s

/-- **Theorem 2.7 (b)** (Fourier inversion). For `g : H → 𝔽_p` and `x ∈ H`,
`g(x) = |H|⁻¹ ∑_{s=0}^{|H|-1} ĝ(χ_s) x^s`. -/
theorem fourierUnits_inversion (g : H → ZMod p) (x : H) :
    g x = (Fintype.card H : ZMod p)⁻¹ *
      ∑ s ∈ range (Fintype.card H), fourierUnits H g s * ((x : (ZMod p)ˣ) : ZMod p) ^ s := by
  have key : ∑ s ∈ range (Fintype.card H), fourierUnits H g s * ((x : (ZMod p)ˣ) : ZMod p) ^ s =
      (Fintype.card H : ZMod p) * g x := by
    simp only [fourierUnits, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hterm : ∀ h : H, ∑ s ∈ range (Fintype.card H),
        g h * ((((h : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ s * ((x : (ZMod p)ˣ) : ZMod p) ^ s =
        g h * ∑ s ∈ range (Fintype.card H),
          ((((h : (ZMod p)ˣ)⁻¹ * (x : (ZMod p)ˣ) : (ZMod p)ˣ) : ZMod p)) ^ s := by
      intro h
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Units.val_mul, mul_pow, mul_assoc]
    simp only [hterm]
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro h _ hne
      rw [sum_char_eq_zero H (H.mul_mem (H.inv_mem h.2) x.2), mul_zero]
      intro h1
      apply hne
      ext1
      exact inv_mul_eq_one.1 h1
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [key, ← mul_assoc, inv_mul_cancel₀ (card_subgroup_units_ne_zero H), one_mul]

end LeeBall
