module

public import RequestProject.LeeBall.GroupRing

/-!
# Consequences of the group-ring characterisation

* the scalar specialisation (equation `P5-generate_groupring`):
  `∑_{λ ⊢ r} k^{ℓ(λ)} / (∏ᵢ λᵢ ∏ⱼ m_λ(j)!) = C(k+r-1, r)`;
* the size of a Lee ball as an alternating sum;
* Lemma 1.3 (Zhang–Zhou), the case `r = 2` of Theorem 1.8;
* Theorems 5.15 and 5.16 (uniform square-multiplicity configurations), Remark 5.17 ("bad" primes)
  and Example 5.14 (`(n, r) = (35, 3)`, `p = 29, 71`).
-/

@[expose] public section

open Finset

namespace LeeBall

section bell

variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma bellPart_congr {y y' : ℕ → R} {k : ℕ} (h : ∀ j, 1 ≤ j → j ≤ k → y j = y' j) :
    bellPart y k = bellPart y' k := by
  unfold bellPart bellTerm
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  refine Multiset.map_congr rfl fun j hj => h j (p.parts_pos hj) (p.le_of_mem_parts hj)

lemma multiset_prod_idem {E : R} (hE : E * E = E) (s : Multiset ℕ) (c d : ℕ → ℚ) :
    (s.map fun j => c j • E + d j • (1 - E)).prod =
      (s.map c).prod • E + (s.map d).prod • (1 - E) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
    have h2 : (1 - E) * (1 - E) = 1 - E := by
      rw [sub_mul, one_mul, h1, sub_zero]
    have h3 : (1 - E) * E = 0 := by rw [mul_comm, h1]
    simp only [add_mul, mul_add, smul_mul_smul_comm, hE, h1, h2, h3, smul_zero, add_zero,
      zero_add, mul_smul]

/-- Splitting a Bell sum along an idempotent. -/
lemma bellPart_idem {E : R} (hE : E * E = E) (c d : ℕ → ℚ) (k : ℕ) :
    bellPart (fun j => c j • E + d j • (1 - E)) k =
      bellPart c k • E + bellPart d k • (1 - E) := by
  unfold bellPart bellTerm
  simp only [multiset_prod_idem hE, smul_add, Finset.sum_add_distrib, Finset.sum_smul,
    smul_smul, smul_eq_mul]

end bell

/-- `D_k(j ↦ c/j) = C(c+k-1, k)` over `ℚ`. -/
lemma bellPart_const_rat (c k : ℕ) :
    bellPart (fun j => (j : ℚ)⁻¹ * c) k = ((c + k - 1).choose k : ℚ) := by
  have := bellPart_const (R := ℚ) c k
  simpa using this

/-- **Equation (P5-generate_groupring).**
`∑_{λ ⊢ r} k^{ℓ(λ)} / (∏ᵢ λᵢ ∏_{j=1}^{r} m_λ(j)!) = C(k+r-1, r)`. -/
theorem sum_partition_pow_length (k r : ℕ) :
    ∑ p : r.Partition, ((k : ℚ) ^ p.parts.card /
        (((p.parts.prod : ℕ) : ℚ) * ∏ j ∈ Icc 1 r, ((p.parts.count j).factorial : ℚ))) =
      ((k + r - 1).choose r : ℚ) := by
  rw [← bellPart_const_rat]
  unfold bellPart bellTerm
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← multFact_eq_prod_Icc, smul_eq_mul, Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate, Multiset.prod_map_inv, Nat.cast_multiset_prod]
  field_simp

/-- The size of a Lee ball as the alternating sum obtained by specialising the group-ring
identity at the trivial group:
`|Bⁿ(r)| = ∑_{t ≤ r/2} (-1)^t C(n,t) C(2n+1 + (r-2t) - 1, r-2t)`. -/
theorem card_leeBall_eq_alt_sum (n r : ℕ) :
    ((leeBall n r).card : ℚ) = ∑ t ∈ range (r / 2 + 1),
      (-1) ^ t * (n.choose t : ℚ) * ((2 * n + 1 + (r - 2 * t) - 1).choose (r - 2 * t) : ℚ) := by
  let x : Fin n → Unit := fun _ => 1
  have h := ball_groupRing_identity x r
  have hof : ∀ g : Unit, MonoidAlgebra.of ℚ Unit g = 1 := fun g => by
    rw [Subsingleton.elim g 1, map_one]
  have hpw : ∀ (j : ℕ) (A : MonoidAlgebra ℚ Unit), pw j A = A := fun j A => by
    have : (fun g : Unit => g ^ j) = id := funext fun g => Subsingleton.elim _ _
    simp only [pw, this, Finsupp.mapDomain_id]
  have hT : tElem x = (((2 * n + 1 : ℕ) : ℚ)) • (1 : MonoidAlgebra ℚ Unit) := by
    simp only [tElem, hof, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
  have hy : (fun j : ℕ => (j : ℚ)⁻¹ • pw j (tElem x)) =
      fun j : ℕ => ((j : ℚ)⁻¹ * ((2 * n + 1 : ℕ) : ℚ)) • (1 : MonoidAlgebra ℚ Unit) := by
    funext j; rw [hpw, hT, smul_smul]
  rw [hy] at h
  simp only [bellPart_const, hof, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  apply (algebraMap ℚ (MonoidAlgebra ℚ Unit)).injective
  rw [map_natCast, h, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

section uniform

variable {G : Type*} [CommGroup G] [Fintype G]

local notation "ofG" => MonoidAlgebra.of ℚ G

lemma pw_smul (t : ℕ) (c : ℚ) (A : MonoidAlgebra ℚ G) : pw t (c • A) = c • pw t A :=
  Finsupp.mapDomain_smul _ _

lemma pw_one_elem (t : ℕ) : pw t (1 : MonoidAlgebra ℚ G) = 1 := by
  have := pw_of (G := G) t 1
  rwa [one_pow, map_one] at this

lemma setElem_univ_mul_self :
    setElem (univ : Finset G) * setElem (univ : Finset G) =
      (Fintype.card G : ℚ) • setElem (univ : Finset G) := by
  simp only [setElem, Finset.sum_mul, Finset.mul_sum, ← map_mul]
  have hg : ∀ g : G, ∑ h, ofG (h * g) = ∑ h, ofG h := fun g =>
    Equiv.sum_comp (Equiv.mulRight g) (fun h => ofG h)
  rw [Finset.sum_congr rfl fun g _ => hg g,
    Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

lemma pw_setElem_univ {t : ℕ} (ht : (Nat.card G).Coprime t) :
    pw t (setElem (univ : Finset G)) = setElem (univ : Finset G) := by
  rw [setElem, pw_sum]
  simp only [pw_of]
  exact (powCoprime ht).sum_comp (fun h => ofG h)

/-- **Theorem 5.16.** Let `G` be a group of prime order `p > r` with `|Bⁿ(r)| = m p`, let
`a ≥ 0` with `p a ≤ 2n+1` and put `T = a·G + (2n+1-pa)·e`.  If
`∑_{t ≤ r/2} (-1)^t C(n,t) C((2n+1-pa) + (r-2t) - 1, r-2t) = 0`, then `m·G` equals the right-hand
side of the group-ring equation of Theorem 1.8 evaluated at `T`. -/
theorem mCp_eq_grRHS {n r m p a : ℕ} (hp : p.Prime) (hG : Fintype.card G = p)
    (hB : (leeBall n r).card = m * p) (hpr : r < p) (hpa : p * a ≤ 2 * n + 1)
    (heq : ∑ t ∈ range (r / 2 + 1), (-1 : ℤ) ^ t * (n.choose t : ℤ) *
      (((2 * n + 1 - p * a) + (r - 2 * t) - 1).choose (r - 2 * t) : ℤ) = 0) :
    (m : ℚ) • setElem (univ : Finset G) =
      grRHS n r ((a : ℚ) • setElem (univ : Finset G) + ((2 * n + 1 - p * a : ℕ) : ℚ) • 1) := by
  set U := setElem (univ : Finset G)
  set b := 2 * n + 1 - p * a
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set E : MonoidAlgebra ℚ G := (p : ℚ)⁻¹ • U
  have hE : E * E = E := by
    show ((p : ℚ)⁻¹ • U) * ((p : ℚ)⁻¹ • U) = (p : ℚ)⁻¹ • U
    rw [smul_mul_smul_comm, setElem_univ_mul_self, hG, smul_smul]
    congr 1; field_simp
  have hab : (a * p + b : ℕ) = 2 * n + 1 := by
    simp only [b]; rw [mul_comm a p]; omega
  have hT : (a : ℚ) • U + (b : ℚ) • 1 =
      ((2 * n + 1 : ℕ) : ℚ) • E + (b : ℚ) • (1 - E) := by
    rw [← hab]; simp only [E, smul_sub, smul_smul]; push_cast
    rw [add_mul, mul_assoc, mul_inv_cancel₀ hp0, mul_one]
    module
  have hy : ∀ s ≤ r, bellPart (fun j => (j : ℚ)⁻¹ • pw j ((a : ℚ) • U + (b : ℚ) • 1)) s =
      ((2 * n + 1 + s - 1).choose s : ℚ) • E + ((b + s - 1).choose s : ℚ) • (1 - E) := by
    intro s hs
    rw [bellPart_congr (y' := fun j => ((j : ℚ)⁻¹ * ((2 * n + 1 : ℕ) : ℚ)) • E +
      ((j : ℚ)⁻¹ * (b : ℚ)) • (1 - E)), bellPart_idem hE, bellPart_const_rat, bellPart_const_rat]
    intro j hj hjs
    have hcop : (Nat.card G).Coprime j := by
      rw [Nat.card_eq_fintype_card, hG, Nat.Prime.coprime_iff_not_dvd hp]
      exact Nat.not_dvd_of_pos_of_lt hj (by omega)
    rw [pw_add, pw_smul, pw_smul, pw_setElem_univ hcop, pw_one_elem, hT]
    simp only [smul_add, smul_smul]
  rw [grRHS]
  have : ∀ t ∈ range (r / 2 + 1), (((-1) ^ t * n.choose t : ℚ)) •
      ∑ p : (r - 2 * t).Partition, grTerm ((a : ℚ) • U + (b : ℚ) • 1) p =
      ((-1) ^ t * n.choose t * ((2 * n + 1 + (r - 2 * t) - 1).choose (r - 2 * t) : ℚ)) • E +
      ((-1) ^ t * n.choose t * ((b + (r - 2 * t) - 1).choose (r - 2 * t) : ℚ)) • (1 - E) := by
    intro t _
    rw [← bellPart_pw, hy _ (Nat.sub_le _ _)]
    simp only [E, smul_add, smul_smul, mul_assoc]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
    ← card_leeBall_eq_alt_sum, hB]
  have heq' : ∑ t ∈ range (r / 2 + 1), (-1 : ℚ) ^ t * (n.choose t : ℚ) *
      ((b + (r - 2 * t) - 1).choose (r - 2 * t) : ℚ) = 0 := by exact_mod_cast heq
  rw [heq', zero_smul, add_zero]
  simp only [E, smul_smul]
  congr 1; push_cast; field_simp

end uniform

section coeff
variable {G : Type*} [CommGroup G]
lemma ma_add_apply (A B : MonoidAlgebra ℚ G) (g : G) : (A + B) g = A g + B g :=
  Finsupp.add_apply _ _ _
lemma ma_sub_apply (A B : MonoidAlgebra ℚ G) (g : G) : (A - B) g = A g - B g :=
  Finsupp.sub_apply _ _ _
lemma ma_smul_apply (c : ℚ) (A : MonoidAlgebra ℚ G) (g : G) : (c • A) g = c * A g :=
  Finsupp.smul_apply _ _ _
lemma ma_sum_apply {ι : Type*} (s : Finset ι) (A : ι → MonoidAlgebra ℚ G) (g : G) :
    (∑ i ∈ s, A i) g = ∑ i ∈ s, A i g :=
  Finsupp.finset_sum_apply _ _ _
lemma ma_of_apply [DecidableEq G] (h g : G) : MonoidAlgebra.of ℚ G h g = if h = g then 1 else 0 := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_apply]
lemma ma_one_apply [DecidableEq G] (g : G) : (1 : MonoidAlgebra ℚ G) g = if 1 = g then 1 else 0 := by
  rw [MonoidAlgebra.one_def, MonoidAlgebra.single_apply]
end coeff

lemma sum_of_apply {G : Type*} [CommGroup G] [DecidableEq G] {ι : Type*} (B : Finset ι)
    (f : ι → G) (g : G) :
    (∑ b ∈ B, MonoidAlgebra.of ℚ G (f b)) g = ((B.filter fun b => f b = g).card : ℚ) := by
  rw [Finsupp.finset_sum_apply]
  simp [MonoidAlgebra.single_apply]

lemma exists_half_rep {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (y : ZMod p) (hy : y ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ (p - 1) / 2 ∧ (y = k ∨ y = -k) := by
  have hpodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hv : y.val < p := ZMod.val_lt y
  have hv0 : y.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  by_cases h : y.val ≤ (p - 1) / 2
  · exact ⟨y.val, by omega, h, Or.inl (ZMod.natCast_zmod_val y).symm⟩
  · refine ⟨p - y.val, by omega, by omega, Or.inr ?_⟩
    rw [Nat.cast_sub hv.le, ZMod.natCast_self, zero_sub, neg_neg, ZMod.natCast_zmod_val]

/-- **Theorem 5.15.** Let `|Bⁿ(r)| = m p` with `p > r` prime, and let `x₁, …, xₙ ∈ 𝔽_p`.  Suppose
that every nonzero square `k²` (`1 ≤ k ≤ (p-1)/2`) occurs exactly `a` times among
`x₁², …, xₙ²`, that `p a ≤ 2n+1`, and that
`∑_{t ≤ r/2} (-1)^t C(n,t) C((2n+1-pa) + (r-2t) - 1, r-2t) = 0`.  Then every element of `𝔽_p`
is represented exactly `m` times as `a₁x₁ + ⋯ + aₙxₙ` with `|a₁| + ⋯ + |aₙ| ≤ r`. -/
theorem uniform_squares_tiling_identity {n r m p a : ℕ} [hp : Fact p.Prime]
    (hB : (leeBall n r).card = m * p) (hpr : r < p) (x : Fin n → ZMod p)
    (hsq : ∀ k : ℕ, 1 ≤ k → k ≤ (p - 1) / 2 →
      (univ.filter fun i => x i ^ 2 = (k : ZMod p) ^ 2).card = a)
    (hpa : p * a ≤ 2 * n + 1)
    (heq : ∑ t ∈ range (r / 2 + 1), (-1 : ℤ) ^ t * (n.choose t : ℤ) *
      (((2 * n + 1 - p * a) + (r - 2 * t) - 1).choose (r - 2 * t) : ℤ) = 0) (y : ZMod p) :
    ((leeBall n r).filter fun b => ∑ i, (b i : ZMod p) * x i = y).card = m := by
  classical
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := card_leeBall_odd n r
    rw [hB, Nat.odd_mul] at this
    exact absurd this.2 (by decide)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    rcases (Nat.dvd_prime Nat.prime_two).1 h' with h1 | h1
    · exact hp.out.one_lt.ne' h1
    · exact hp2 h1
  -- each nonzero `y` is hit `a` times by `±xᵢ`
  have hpair : ∀ z : ZMod p, z ≠ 0 →
      (univ.filter fun i => x i = z).card + (univ.filter fun i => x i = -z).card = a := by
    intro z hz
    obtain ⟨k, hk1, hk2, hk⟩ := exists_half_rep hp2 z hz
    have hzk : z ^ 2 = (k : ZMod p) ^ 2 := by rcases hk with h | h <;> rw [h]; ring
    rw [← hsq k hk1 hk2, ← hzk, ← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp [sq_eq_sq_iff_eq_or_eq_neg]
    · rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [mem_filter, mem_univ, true_and] at hi hi'
      have : (2 : ZMod p) * z = 0 := by linear_combination -(hi'.symm.trans hi)
      rcases mul_eq_zero.1 this with h | h
      · exact htwo h
      · exact hz h
  let x' : Fin n → (Multiplicative (ZMod p)) := fun i => Multiplicative.ofAdd (x i)
  set b := 2 * n + 1 - p * a
  have hT : tElem x' = (a : ℚ) • setElem (univ : Finset (Multiplicative (ZMod p))) + (b : ℚ) • 1 := by
    set D := tElem x' - ((a : ℚ) • setElem (univ : Finset (Multiplicative (ZMod p))) + (b : ℚ) • 1)
    have hD : ∀ g : (Multiplicative (ZMod p)), g ≠ 1 → D g = 0 := by
      intro g hg
      have hg' : Multiplicative.toAdd g ≠ 0 := hg
      simp only [D, tElem, setElem, ma_sub_apply, ma_add_apply, ma_smul_apply, ma_sum_apply,
        ma_of_apply, ma_one_apply, Finset.sum_add_distrib, Finset.sum_boole, if_neg hg.symm,
        Finset.sum_ite_eq', Finset.filter_eq', mem_univ, if_true, Finset.card_singleton]
      have h1 : (univ.filter fun i => x' i = g) = univ.filter fun i => x i = Multiplicative.toAdd g :=
        by ext i; simp [x']; rfl
      have h2 : (univ.filter fun i => (x' i)⁻¹ = g) =
          univ.filter fun i => x i = -Multiplicative.toAdd g := by
        ext i; simp only [mem_filter, mem_univ, true_and, x']
        constructor
        · intro h; rw [← h]; simp
        · intro h; rw [h]; simp
      rw [h1, h2]
      have := hpair _ hg'
      rw [← this]; push_cast; ring
    let ε := MonoidAlgebra.lift ℚ ℚ (Multiplicative (ZMod p)) 1
    have hε : ε D = 0 := by
      simp only [D, map_sub, map_add, map_smul, tElem, setElem, map_sum, ε,
        MonoidAlgebra.lift_of, map_one, MonoidHom.one_apply, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
      simp only [nsmul_eq_mul, mul_one, Fintype.card_multiplicative, ZMod.card]
      have : ((b : ℕ) : ℚ) = 2 * n + 1 - p * a := by
        simp only [b]; push_cast [hpa]; ring
      rw [this]; push_cast; ring
    have hD1 : D = MonoidAlgebra.single 1 (D 1) := by
      ext g
      rw [MonoidAlgebra.single_apply]
      split_ifs with h
      · rw [h]
      · exact hD g (Ne.symm h)
    have : D 1 = 0 := by
      rw [hD1, MonoidAlgebra.lift_single] at hε
      simpa using hε
    rw [this] at hD1
    simp only [Finsupp.single_zero] at hD1
    exact sub_eq_zero.1 hD1
  have hmain := mCp_eq_grRHS (G := (Multiplicative (ZMod p))) hp.out (by simp [ZMod.card]) hB hpr hpa heq
  rw [← hT, ← sum_leeBall_gpow_eq_grRHS] at hmain
  have := congrArg (fun A : MonoidAlgebra ℚ (Multiplicative (ZMod p)) => A (Multiplicative.ofAdd y)) hmain
  simp only [sum_of_apply] at this
  have hgp : ∀ c : Fin n → ℤ, gpow x' c = Multiplicative.ofAdd (∑ i, (c i : ZMod p) * x i) := by
    intro c
    simp only [gpow, x']
    rw [ofAdd_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zsmul_eq_mul, ofAdd_zsmul]
  simp only [hgp, Multiplicative.ofAdd.injective.eq_iff] at this
  rw [setElem, Finsupp.smul_apply, sum_of_apply] at this
  have h1 : (univ.filter fun g : (Multiplicative (ZMod p)) => g = Multiplicative.ofAdd y).card = 1 := by
    rw [Finset.filter_eq' univ, if_pos (mem_univ _), Finset.card_singleton]
  rw [h1] at this
  exact_mod_cast (by simpa using this.symm)

/-! ### Lemma 1.3: the case `r = 2` -/

section rtwo

variable {G : Type*} [CommGroup G]

lemma grRHS_two (n : ℕ) (T : MonoidAlgebra ℚ G) :
    grRHS n 2 T = (2⁻¹ : ℚ) • (T * T) + (2⁻¹ : ℚ) • pw 2 T - (n : ℚ) • 1 := by
  rw [grRHS, show 2 / 2 + 1 = 2 by rfl, Finset.sum_range_succ, Finset.sum_range_one,
    ← bellPart_pw, ← bellPart_pw]
  simp only [Nat.sub_zero, mul_one, Nat.sub_self, bellPart_zero, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, one_smul, pow_one, Nat.choose_one_right, neg_mul, one_mul]
  have h2 := bellPart_rec (fun j => (j : ℚ)⁻¹ • pw j T) 2
  rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.sum_pair (by norm_num), bellPart_one,
    bellPart_zero] at h2
  simp only [Nat.cast_one, inv_one, one_smul, pw_one, Nat.cast_ofNat, mul_one,
    show 2 - 1 = 1 by rfl, show 2 - 2 = 0 by rfl] at h2
  rw [neg_smul]
  linear_combination (norm := module) (2⁻¹ : ℚ) • h2

end rtwo

/-- **Lemma 1.3** (Zhang–Zhou), obtained here as the case `r = 2` of Theorem 1.8.  There is a
lattice tiling of `ℤⁿ` by `Bⁿ(2)` iff there are an abelian group `G` of order `2n² + 2n + 1` and
a subset `T ⊆ G` of size `2n+1` with `e ∈ T`, `T = T^{(-1)}` and `T² = 2G - T^{(2)} + 2n`. -/
theorem hasLatticeTiling_leeBall_two_iff (n : ℕ) :
    HasLatticeTiling (leeBall n 2) ↔
      ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G), Fintype.card G = 2 * n ^ 2 + 2 * n + 1 ∧
        ∃ T : Finset G, T.card = 2 * n + 1 ∧ (1 : G) ∈ T ∧ (∀ g ∈ T, g⁻¹ ∈ T) ∧
          setElem T * setElem T =
            (2 : ℚ) • setElem (univ : Finset G) - pw 2 (setElem T) + ((2 * n : ℕ) : ℚ) • 1 := by
  have hcard : (leeBall n 2).card = 2 * n ^ 2 + 2 * n + 1 := by
    rw [card_leeBall, stantonCowan_eq_range]
    simp [Finset.sum_range_succ, Nat.choose_two_right]
    have : n * (n - 1) = n ^ 2 - n := by
      rw [Nat.mul_sub, mul_one, sq]
    rcases n with _ | n
    · simp
    · simp [Nat.succ_sub_one]
      have : (n + 1) * n / 2 * 4 = 2 * ((n + 1) * n) := by
        have h := Nat.even_mul_pred_self (n + 1)
        simp only [Nat.add_sub_cancel] at h
        obtain ⟨k, hk⟩ := h
        rw [hk]; omega
      nlinarith
  rw [hasLatticeTiling_leeBall_iff_groupRing n 2 (by norm_num), hcard]
  refine exists_congr fun G => exists_congr fun _ => exists_congr fun _ =>
    and_congr_right fun _ => exists_congr fun T => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [grRHS_two]
  push_cast
  constructor
  · intro h; linear_combination (norm := module) (-2 : ℚ) • h
  · intro h; linear_combination (norm := module) (-2⁻¹ : ℚ) • h

/-! ### "Bad" primes and the example `(n, r) = (35, 3)` -/

/-- The set `D` of Remark 5.17 ("bad" primes): the admissible `a ≥ 0` for Theorem 5.15. -/
def badSet (n r p : ℕ) : Set ℕ :=
  {a | p * a ≤ 2 * n + 1 ∧ ∑ t ∈ range (r / 2 + 1), (-1 : ℤ) ^ t * (n.choose t : ℤ) *
      (((2 * n + 1 - p * a) + (r - 2 * t) - 1).choose (r - 2 * t) : ℤ) = 0}

/-- If `p = 2n+1` and `r` is odd then `a = 1` lies in `D`; in particular `p = 2n+1` is a bad
prime for every odd radius `2 < r < p` when it is prime. -/
theorem one_mem_badSet {n r : ℕ} (hr : Odd r) : 1 ∈ badSet n r (2 * n + 1) := by
  refine ⟨le_of_eq (mul_one _), Finset.sum_eq_zero fun t ht => ?_⟩
  have hts : 1 ≤ r - 2 * t := by
    obtain ⟨k, rfl⟩ := hr
    rw [Finset.mem_range] at ht
    have : t ≤ k := by omega
    omega
  rw [mul_one, Nat.sub_self, zero_add, Nat.choose_eq_zero_of_lt (n := r - 2 * t - 1) (k := r - 2 * t) (by omega)]
  simp

/-- `|B³⁵(3)| = 59711 = 71 · 29²`. -/
theorem card_leeBall_35_3 : (leeBall 35 3).card = 59711 ∧ 59711 = 71 * 29 ^ 2 := by
  rw [card_leeBall]; decide

/-- For `(n, r, p) = (35, 3, 29)` the only admissible value is `a = 2`. -/
theorem badSet_35_3_29 : badSet 35 3 29 = {2} := by
  ext a
  simp only [badSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hsum⟩
    have : a ≤ 2 := by omega
    interval_cases a <;> first | rfl | (exfalso; revert hsum; decide)
  · rintro rfl; refine ⟨by norm_num, by decide⟩

/-- For `(n, r, p) = (35, 3, 71)` the only admissible value is `a = 1`. -/
theorem badSet_35_3_71 : badSet 35 3 71 = {1} := by
  ext a
  simp only [badSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ha, hsum⟩
    have : a ≤ 1 := by omega
    interval_cases a <;> first | rfl | (exfalso; revert hsum; decide)
  · rintro rfl; refine ⟨by norm_num, by decide⟩

/-- **Example 5.14** (`(n, r) = (35, 3)`, prime `p = 71`).  With `xᵢ = i` (`i = 1, …, 35`), so that
`{xᵢ²} = {1·1², …, 1·35²}`, every element of `𝔽₇₁` is represented exactly `m = 29² = 841`
times as `∑ aᵢxᵢ` with `∑|aᵢ| ≤ 3`. -/
theorem example_35_3_p71 (y : ZMod 71) :
    ((leeBall 35 3).filter fun b =>
      ∑ i : Fin 35, (b i : ZMod 71) * (((i : ℕ) + 1 : ℕ) : ZMod 71) = y).card = 841 := by
  have hsq : ∀ k : ℕ, 1 ≤ k → k ≤ (71 - 1) / 2 → (univ.filter fun i : Fin 35 =>
      (((i : ℕ) + 1 : ℕ) : ZMod 71) ^ 2 = (k : ZMod 71) ^ 2).card = 1 := by
    intro k hk1 hk2
    norm_num at hk2
    interval_cases k <;> decide
  haveI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
  have hB : (leeBall 35 3).card = 841 * 71 := by rw [card_leeBall_35_3.1]
  have hD : 1 ∈ badSet 35 3 71 := by rw [badSet_35_3_71]; rfl
  exact uniform_squares_tiling_identity (a := 1) hB (by norm_num) _ hsq hD.1 hD.2 y

/-- **Example 5.14** (`(n, r) = (35, 3)`, prime `p = 29`).  With `{xᵢ²} = {7·0, 2·1², …, 2·14²}`, every element of
`𝔽₂₉` is represented exactly `m = 59711 / 29 = 2059` times as `∑ aᵢxᵢ` with `∑|aᵢ| ≤ 3`. -/
theorem example_35_3_p29 (y : ZMod 29) :
    ((leeBall 35 3).filter fun b =>
      ∑ i : Fin 35, (b i : ZMod 29) *
        ((if (i : ℕ) < 7 then 0 else ((i : ℕ) - 7) / 2 + 1 : ℕ) : ZMod 29) = y).card = 2059 := by
  have hsq : ∀ k : ℕ, 1 ≤ k → k ≤ (29 - 1) / 2 → (univ.filter fun i : Fin 35 =>
      ((if (i : ℕ) < 7 then 0 else ((i : ℕ) - 7) / 2 + 1 : ℕ) : ZMod 29) ^ 2 =
        (k : ZMod 29) ^ 2).card = 2 := by
    intro k hk1 hk2
    norm_num at hk2
    interval_cases k <;> decide
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  have hB : (leeBall 35 3).card = 2059 * 29 := by rw [card_leeBall_35_3.1]
  have hD : 2 ∈ badSet 35 3 29 := by rw [badSet_35_3_29]; rfl
  exact uniform_squares_tiling_identity (a := 2) hB (by norm_num) _ hsq hD.1 hD.2 y

end LeeBall
