module

public import RequestProject.LeeBall.Ideal

/-!
# Section 5: further necessary conditions

Throughout, `x ∈ 𝔽_pⁿ` and `S_k = ∑ᵢ xᵢ^k`.  A lattice tiling with `|Bⁿ(r)| = m p` produces a
*tiling image* `x` (`IsTilingImage`), and then `(S₂, S₄, …, S_{p-1})` solves the system of
Theorem 4.3.

* Lemma 5.4 (`S_{p-1}` counts the nonzero `xᵢ`);
* Lemma 5.5 (`τ(𝓔_{≤n})` counts the zero `xᵢ²`, and `|B^τ(r)| ≤ m`);
* Newton's identities (equation `eq:Newton`) for `e_k(x²)`;
* the Fourier formula `g(i²) = -2 ∑_k S_{2k} / i^{2k}`;
* Theorem 5.8 (the sum of `𝓖` is at most `n`);
* Theorem 5.9 (uncertainty principle for the zeros of `𝓢`);
* Proposition 5.11 (`c_λ = 0` when `ℓ(λ) > r`, and the reduced recursion).
-/

@[expose] public section

open Finset

namespace LeeBall

variable {n p : ℕ}

/-- A tiling image `x` gives the solution `Y_k = S_{2k}(x)` of the system of Theorem 4.3. -/
theorem IsTilingImage.ySystem {r m : ℕ} [Fact p.Prime] (hp2 : 2 < p) {x : Fin n → ZMod p}
    (hx : IsTilingImage n r m p x) :
    YSystem n r m p (fun k => ∑ i, x i ^ (2 * k)) := by
  obtain ⟨h1, h2⟩ := hx.qSystem hp2
  exact ⟨fun k hk1 hk2 => by rw [← aeval_qPoly_eq_fY]; exact h1 k hk1 hk2,
    by rw [← aeval_qPoly_eq_fY]; exact h2⟩

/-! ### Lemma 5.4 -/

/-- `S_{p-1} = #{i : xᵢ ≠ 0}` in `𝔽_p` (Fermat). -/
theorem psum_card_sub_one [Fact p.Prime] (x : Fin n → ZMod p) :
    ∑ i, x i ^ (p - 1) = ((univ.filter fun i => x i ≠ 0).card : ZMod p) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [ZMod.pow_card_sub_one_eq_one h, Nat.cast_one]
  · push_neg at h
    rw [h, zero_pow (by have := (Fact.out : p.Prime).two_le; omega)]

/-- **Lemma 5.4.** `S_{p-1} ≡ t (mod p)` for some integer `0 ≤ t ≤ n`.  (This holds for every
`x ∈ 𝔽_pⁿ`, in particular for the tiling image `x = Φ ∘ φ(εᵢ)`.) -/
theorem exists_psum_card_sub_one_eq [Fact p.Prime] (x : Fin n → ZMod p) :
    ∃ t ≤ n, ∑ i, x i ^ (p - 1) = (t : ZMod p) :=
  ⟨_, (Finset.card_filter_le _ _).trans (by simp), psum_card_sub_one x⟩

/-- Lemma 5.4 as a nonexistence criterion: if no solution `Y` of the system of Theorem 4.3 has
`Y_{(p-1)/2} ∈ {0, 1, …, n}` (mod `p`), there is no lattice tiling. -/
theorem no_tiling_of_S_pred {r m : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p)
    (h : ∀ Y : ℕ → ZMod p, YSystem n r m p Y → ∀ t ≤ n, Y ((p - 1) / 2) ≠ t) :
    ¬ HasLatticeTiling (leeBall n r) := by
  intro ht
  obtain ⟨x, hx⟩ := exists_tilingImage_of_tiling hB ht
  obtain ⟨t, htn, hteq⟩ := exists_psum_card_sub_one_eq x
  have hpodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  refine h _ (hx.ySystem hp2) t htn ?_
  rw [show 2 * ((p - 1) / 2) = p - 1 by omega, hteq]

/-! ### Lemma 5.5 -/

/-- `e_k(x²) = ∑_{i₁ < ⋯ < i_k} x_{i₁}² ⋯ x_{i_k}²`. -/
def esymmSq (x : Fin n → ZMod p) (k : ℕ) : ZMod p :=
  ∑ s ∈ univ.powersetCard k, ∏ i ∈ s, x i ^ 2

/-- `τ(𝓔_{≤n}) = max {k ≤ n : e_j(x²) = 0 for n - k + 1 ≤ j ≤ n}`. -/
def tauE (x : Fin n → ZMod p) : ℕ :=
  Nat.findGreatest (fun k => ∀ j, n - k + 1 ≤ j → j ≤ n → esymmSq x j = 0) n

lemma esymmSq_eq_zero_of_lt [Fact p.Prime] (x : Fin n → ZMod p) {j : ℕ}
    (hj : (univ.filter fun i => x i ≠ 0).card < j) : esymmSq x j = 0 := by
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [Finset.mem_powersetCard] at hs
  have : ¬ s ⊆ univ.filter fun i => x i ≠ 0 := fun h => by
    have := Finset.card_le_card h; omega
  obtain ⟨i, his, hi⟩ := Finset.not_subset.1 this
  simp only [mem_filter, mem_univ, true_and, not_not] at hi
  exact Finset.prod_eq_zero his (by rw [hi]; ring)

lemma esymmSq_card_ne_zero [Fact p.Prime] (x : Fin n → ZMod p) :
    esymmSq x (univ.filter fun i => x i ≠ 0).card ≠ 0 := by
  set N := univ.filter fun i => x i ≠ 0
  rw [esymmSq, Finset.sum_eq_single N]
  · exact Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (Finset.mem_filter.1 hi).2
  · intro s hs hsN
    rw [Finset.mem_powersetCard] at hs
    have : ¬ s ⊆ N := fun h => hsN (Finset.eq_of_subset_of_card_le h hs.2.ge)
    obtain ⟨i, his, hi⟩ := Finset.not_subset.1 this
    simp only [N, mem_filter, mem_univ, true_and, not_not] at hi
    exact Finset.prod_eq_zero his (by rw [hi]; ring)
  · intro h; exact absurd (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩) h

/-- `τ(𝓔_{≤n})` is the number of zeros in `{x₁², …, xₙ²}` (first part of Lemma 5.5). -/
theorem tauE_eq [Fact p.Prime] (x : Fin n → ZMod p) :
    tauE x = (univ.filter fun i => x i = 0).card := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset (Fin n)))
    (fun i => x i = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  set z := (univ.filter fun i => x i = 0).card
  set t := (univ.filter fun i => ¬ x i = 0).card
  unfold tauE
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ j hj1 _ => esymmSq_eq_zero_of_lt x (by simp only [ne_eq]; omega),
    fun k hk hkn hP => ?_⟩
  have ht0 : t ≠ 0 := by omega
  exact esymmSq_card_ne_zero x (hP t (by simp only [t]; omega) (by omega))

/-- **Lemma 5.5.** For a tiling image `x` (which exists when there is a lattice tiling),
`|B^{τ(𝓔_{≤n})}(r)| ≤ m`. -/
theorem card_leeBall_tauE_le {r m : ℕ} [Fact p.Prime] {x : Fin n → ZMod p}
    (hx : IsTilingImage n r m p x) : (leeBall (tauE x) r).card ≤ m := by
  classical
  rw [tauE_eq]
  set Z := univ.filter fun i => x i = 0
  let e : Fin Z.card ≃ Z := (Finset.equivFin Z).symm
  let emb : (Fin Z.card → ℤ) → (Fin n → ℤ) := fun c i =>
    if h : i ∈ Z then c (e.symm ⟨i, h⟩) else 0
  have hemb_norm : ∀ c, leeNorm (emb c) = leeNorm c := by
    intro c
    unfold leeNorm
    rw [← Finset.sum_filter_add_sum_filter_not univ (· ∈ Z)]
    have h0 : ∑ i ∈ univ.filter (· ∉ Z), (emb c i).natAbs = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [emb, dif_neg (Finset.mem_filter.1 hi).2, Int.natAbs_zero]
    rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [← Finset.sum_coe_sort Z]
    refine (Fintype.sum_equiv e.symm _ _ fun i => ?_)
    simp only [emb, dif_pos i.2]
  have hmap : Set.MapsTo emb (leeBall Z.card r)
      ((leeBall n r).filter fun b => ∑ i, (b i : ZMod p) * x i = 0) := by
    intro c hc
    simp only [coe_filter, mem_leeBall, Set.mem_setOf_eq, mem_coe] at hc ⊢
    refine ⟨by rw [hemb_norm]; exact hc, Finset.sum_eq_zero fun i _ => ?_⟩
    by_cases hi : i ∈ Z
    · rw [(Finset.mem_filter.1 hi).2, mul_zero]
    · simp [emb, dif_neg hi]
  have hinj : Set.InjOn emb (leeBall Z.card r) := by
    intro c _ d _ hcd
    funext k
    have := congrFun hcd (e k).1
    simpa [emb, (e k).2] using this
  have := Finset.card_le_card_of_injOn emb hmap hinj
  rwa [hx 0] at this

/-! ### Newton's identities for `e_k(x²)` -/

/-- **Newton's identities** (equation `Newton`):
`k e_k(x²) = ∑_{i=1}^{k} (-1)^{i-1} S_{2i} e_{k-i}(x²)`. -/
theorem newton_esymmSq (x : Fin n → ZMod p) (k : ℕ) :
    (k : ZMod p) * esymmSq x k =
      ∑ i ∈ Icc 1 k, (-1) ^ (i - 1) * (∑ j, x j ^ (2 * i)) * esymmSq x (k - i) := by
  have h := congrArg (MvPolynomial.aeval fun j => x j ^ 2)
    (MvPolynomial.mul_esymm_eq_sum (Fin n) (ZMod p) k)
  have hes : ∀ l, MvPolynomial.aeval (fun j => x j ^ 2) (MvPolynomial.esymm (Fin n) (ZMod p) l) =
      esymmSq x l := by
    intro l
    simp [MvPolynomial.esymm, esymmSq, map_sum, map_prod]
  have hps : ∀ l, MvPolynomial.aeval (fun j => x j ^ 2) (MvPolynomial.psum (Fin n) (ZMod p) l) =
      ∑ j, x j ^ (2 * l) := by
    intro l
    simp [MvPolynomial.psum, map_sum, ← pow_mul]
  simp only [map_mul, map_natCast, hes, map_pow, map_neg, map_one, map_sum, hps] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_nbij' (fun a => a.2) (fun i => (k - i, i)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_antidiagonal] at ha
    simp only [mem_Icc]; omega
  · intro i hi
    simp only [mem_Icc] at hi
    simp only [mem_filter, mem_antidiagonal]; omega
  · intro a ha
    simp only [mem_filter, mem_antidiagonal] at ha
    ext <;> simp; omega
  · intro i _; rfl
  · rintro ⟨a1, a2⟩ ha
    simp only [mem_filter, mem_antidiagonal] at ha
    obtain ⟨hsum, hlt⟩ := ha
    have hk : k - a2 = a1 := by omega
    rw [hk]
    have hsign : (-1 : ZMod p) ^ (k + 1) * (-1) ^ a1 = (-1) ^ (a2 - 1) := by
      rw [← pow_add]
      have : k + 1 + a1 = (a2 - 1) + 2 * (a1 + 1) := by omega
      rw [this, pow_add, pow_mul]; simp
    rw [← hsign]; ring

/-! ### The Fourier formula for `𝓖` -/

lemma geom_sum_Icc_of_pow_eq_one {F : Type*} [Field F] {a : F} {h : ℕ} (ha : a ^ h = 1)
    (ha1 : a ≠ 1) : ∑ k ∈ Icc 1 h, a ^ k = 0 := by
  have : ∑ k ∈ Icc 1 h, a ^ k = a * ∑ k ∈ range h, a ^ k := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr (by simp) fun k _ => ?_
    rw [add_comm, pow_succ']
  rw [this, geom_sum_eq ha1, ha, sub_self, zero_div, mul_zero]

/-- **Fourier formula** (equation `P6-computegi`): for `1 ≤ i ≤ (p-1)/2`,
`g(i²) = -2 ∑_{k=1}^{(p-1)/2} S_{2k} / i^{2k}`, where `g(i²)` is the number of `j` with
`xⱼ² = i²`, reduced mod `p`. -/
theorem count_sq_eq_fourier [Fact p.Prime] (hp2 : 2 < p) (x : Fin n → ZMod p) {i : ℕ}
    (hi1 : 1 ≤ i) (hi : i ≤ (p - 1) / 2) :
    ((univ.filter fun j => x j ^ 2 = (i : ZMod p) ^ 2).card : ZMod p) =
      -2 * ∑ k ∈ Icc 1 ((p - 1) / 2), (∑ j, x j ^ (2 * k)) / (i : ZMod p) ^ (2 * k) := by
  have hpodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  set h := (p - 1) / 2
  have hi0 : (i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hi1 (by omega)
  -- swap the sums and evaluate each geometric sum
  have hj : ∀ j, ∑ k ∈ Icc 1 h, x j ^ (2 * k) / (i : ZMod p) ^ (2 * k) =
      if x j ^ 2 = (i : ZMod p) ^ 2 then (h : ZMod p) else 0 := by
    intro j
    set a := x j ^ 2 / (i : ZMod p) ^ 2
    have hterm : ∀ k, x j ^ (2 * k) / (i : ZMod p) ^ (2 * k) = a ^ k := by
      intro k; simp only [a, div_pow, ← pow_mul]
    simp only [hterm]
    split_ifs with hx
    · have : a = 1 := by simp only [a, hx, div_self (pow_ne_zero 2 hi0)]
      simp [this]
    · by_cases hx0 : x j = 0
      · rw [Finset.sum_eq_zero fun k hk => by
          simp only [a, hx0, zero_pow two_ne_zero, zero_div]
          exact zero_pow (by simp only [mem_Icc] at hk; omega)]
      · refine geom_sum_Icc_of_pow_eq_one ?_ ?_
        · simp only [a, div_pow, ← pow_mul]
          rw [show 2 * h = p - 1 by omega, ZMod.pow_card_sub_one_eq_one hx0,
            ZMod.pow_card_sub_one_eq_one hi0, div_one]
        · intro ha; apply hx
          simp only [a] at ha
          rwa [div_eq_one_iff_eq (pow_ne_zero 2 hi0)] at ha
  have hsw : ∑ k ∈ Icc 1 h, (∑ j, x j ^ (2 * k)) / (i : ZMod p) ^ (2 * k) =
      ∑ j, ∑ k ∈ Icc 1 h, x j ^ (2 * k) / (i : ZMod p) ^ (2 * k) := by
    simp only [Finset.sum_div]; exact Finset.sum_comm
  rw [hsw, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  have h2h : (2 : ZMod p) * h = -1 := by
    have : ((2 * h + 1 : ℕ) : ZMod p) = 0 := by
      rw [show 2 * h + 1 = p by omega, ZMod.natCast_self]
    push_cast at this
    linear_combination this
  linear_combination (((univ.filter fun j => x j ^ 2 = (i : ZMod p) ^ 2).card : ZMod p)) * h2h

/-! ### Theorem 5.8 -/

/-- The sequence `𝓖`: `g(i²) = -2 ∑_{k=1}^{(p-1)/2} Y_k / i^{2k}` computed from `Y_k = S_{2k}`. -/
def gSeq (p : ℕ) [Fact p.Prime] (Y : ℕ → ZMod p) (i : ℕ) : ZMod p :=
  -2 * ∑ k ∈ Icc 1 ((p - 1) / 2), Y k / (i : ZMod p) ^ (2 * k)

lemma card_sq_eq_le_one [Fact p.Prime] (hp2 : 2 < p) (c : ZMod p) :
    ((Icc 1 ((p - 1) / 2)).filter fun i : ℕ => (i : ZMod p) ^ 2 = c).card ≤ 1 := by
  have hpodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [mem_filter, mem_Icc] at ha hb
  have hab : (a : ZMod p) ^ 2 = (b : ZMod p) ^ 2 := ha.2.trans hb.2.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hab with h | h
  · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h
    exact h
  · exfalso
    have : ((a + b : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
    rw [ZMod.natCast_eq_zero_iff] at this
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) this

/-- For every `x ∈ 𝔽_pⁿ`, the canonical representatives of `𝓖` (computed from `S_{2k}(x)`) sum to
at most `n`. -/
theorem sum_gSeq_val_le [Fact p.Prime] (hp2 : 2 < p) (x : Fin n → ZMod p) :
    ∑ i ∈ Icc 1 ((p - 1) / 2), (gSeq p (fun k => ∑ j, x j ^ (2 * k)) i).val ≤ n := by
  classical
  have h1 : ∀ i ∈ Icc 1 ((p - 1) / 2), (gSeq p (fun k => ∑ j, x j ^ (2 * k)) i).val ≤
      (univ.filter fun j => x j ^ 2 = (i : ZMod p) ^ 2).card := by
    intro i hi
    rw [mem_Icc] at hi
    rw [gSeq, ← count_sq_eq_fourier hp2 x hi.1 hi.2, ZMod.val_natCast]
    exact Nat.mod_le _ _
  refine (Finset.sum_le_sum h1).trans ?_
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc ∑ j : Fin n, ∑ i ∈ Icc 1 ((p - 1) / 2), (if x j ^ 2 = (i : ZMod p) ^ 2 then 1 else 0)
      ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        have := card_sq_eq_le_one hp2 (x j ^ 2)
        simpa only [eq_comm] using this
    _ = n := by simp

/-- **Theorem 5.8.** If for every solution `Y` of the system of Theorem 4.3 the canonical
representatives of `𝓖 = (g(1²), …, g(((p-1)/2)²))` sum to more than `n`, then there is no lattice
tiling of `ℤⁿ` by `Bⁿ(r)`. -/
theorem no_tiling_of_sum_gSeq {r m : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p)
    (h : ∀ Y : ℕ → ZMod p, YSystem n r m p Y →
      n < ∑ i ∈ Icc 1 ((p - 1) / 2), (gSeq p Y i).val) :
    ¬ HasLatticeTiling (leeBall n r) := by
  intro ht
  obtain ⟨x, hx⟩ := exists_tilingImage_of_tiling hB ht
  exact absurd (sum_gSeq_val_le hp2 x) (not_le.2 (h _ (hx.ySystem hp2)))

end LeeBall
