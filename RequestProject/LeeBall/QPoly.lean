module

public import RequestProject.LeeBall.Moments

/-!
# Q-polynomials of Lee balls: the explicit formula (Theorem 1.7)

* `qPoly B k = ∑_{b ∈ B} ⟨X, b⟩^{2k}` (Definition 3.1, with integer coefficients);
* `cLam n r λ` is the coefficient `c_λ` of equation `eq:P3-cor_Q-poly_explicit_formula` of the manuscript;
* `qPoly_leeBall_explicit` is Theorem 1.7: `Q^k_{Bⁿ(r)} = ∑_{λ ⊢ k} c_λ s_{2λ}`;
* `cLam_eq_cInt` shows that every `c_λ` is an integer.
-/

@[expose] public section

open Finset PowerSeries

namespace LeeBall

/-- **Definition 3.1.** The Q-polynomial `Q^k_B(X) = ∑_{b ∈ B} ⟨X, b⟩^{2k}`. -/
noncomputable def qPoly {n : ℕ} (B : Finset (Fin n → ℤ)) (k : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∑ b ∈ B, (∑ i, MvPolynomial.C (b i) * MvPolynomial.X i) ^ (2 * k)

/-- The parts of a partition listed in weakly decreasing order `λ₁ ≥ λ₂ ≥ ⋯ ≥ λ_ℓ`. -/
def partList {k : ℕ} (p : k.Partition) : List ℕ := p.parts.sort (· ≥ ·)

lemma partList_coe {k : ℕ} (p : k.Partition) : ((partList p : List ℕ) : Multiset ℕ) = p.parts :=
  Multiset.sort_eq _ _

lemma length_partList {k : ℕ} (p : k.Partition) : (partList p).length = p.parts.card :=
  Multiset.length_sort _

lemma mem_partList {k : ℕ} (p : k.Partition) {i : ℕ} : i ∈ partList p ↔ i ∈ p.parts :=
  Multiset.mem_sort _

/-- The set of compositions `r₁ + ⋯ + r_ℓ + r_{ℓ+1} = r` with `r₁, …, r_ℓ ≥ 1`, `r_{ℓ+1} ≥ 0`. -/
def compositions (ℓ r : ℕ) : Finset (Fin (ℓ + 1) → ℕ) :=
  (Finset.Nat.antidiagonalTuple (ℓ + 1) r).filter fun c => ∀ j : Fin ℓ, 1 ≤ c j.castSucc

/-- The sum `∑_{r₁+⋯+r_{ℓ+1}=r, rᵢ ≥ 1} |Bⁿ(r_{ℓ+1})| ∏ᵢ rᵢ^{2λᵢ-1}` of equation `eq:P3-cor_Q-poly_explicit_formula`. -/
def compSum (n r : ℕ) (L : List ℕ) : ℕ :=
  ∑ c ∈ compositions L.length r,
    (leeBall n (c (Fin.last _))).card * ∏ j : Fin L.length, (c j.castSucc) ^ (2 * L[j] - 1)

/-- **Equation `eq:P3-cor_Q-poly_explicit_formula`.** The coefficient
`c_λ = (2k)!/∏ᵢ(2λᵢ)! · 2^ℓ/∏ⱼ m_λ(j)! · ∑_{r₁+⋯+r_{ℓ+1}=r, r₁,…,r_ℓ ≥ 1} |Bⁿ(r_{ℓ+1})| ∏ᵢ rᵢ^{2λᵢ-1}`. -/
noncomputable def cLam (n r : ℕ) {k : ℕ} (p : k.Partition) : ℚ :=
  ((2 * k).factorial : ℚ) / (p.parts.map fun i => ((2 * i).factorial : ℚ)).prod *
    ((2 : ℚ) ^ (partList p).length / ∏ j ∈ Finset.Icc 1 k, ((p.parts.count j).factorial : ℚ)) *
    ∑ c ∈ compositions (partList p).length r,
      ((leeBall n (c (Fin.last _))).card : ℚ) *
        ∏ j : Fin (partList p).length, ((c j.castSucc : ℕ) : ℚ) ^ (2 * (partList p)[j] - 1)

/-- Integer form of `c_λ`: `2^ℓ · bell(2λ) · compSum`, where `bell(2λ)` is the number of set
partitions of a `2k`-set into blocks of sizes `2λ₁, …, 2λ_ℓ`. -/
def cInt (n r : ℕ) {k : ℕ} (p : k.Partition) : ℤ :=
  2 ^ p.parts.card * ((p.parts.map (2 * ·)).bell : ℤ) * (compSum n r (partList p) : ℤ)

/-- `s_{2λ} = s_{2λ₁} ⋯ s_{2λ_ℓ}`. -/
noncomputable def psumTwo (σ R : Type*) [CommSemiring R] [Fintype σ] {k : ℕ} (p : k.Partition) :
    MvPolynomial σ R :=
  (p.parts.map fun i => MvPolynomial.psum σ R (2 * i)).prod

/-! ### Coefficients of products of power series -/

lemma sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (k n : ℕ)
    (f : (Fin (k + 1) → ℕ) → M) :
    ∑ c ∈ Finset.Nat.antidiagonalTuple (k + 1) n, f c =
      ∑ p ∈ antidiagonal n, ∑ c ∈ Finset.Nat.antidiagonalTuple k p.2, f (Fin.cons p.1 c) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun c _ => ⟨(c 0, n - c 0), Fin.tail c⟩)
    (fun x _ => Fin.cons x.1.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hc
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple]
    constructor
    · omega
    · simp only [Fin.tail]; omega
  · rintro ⟨⟨a, b⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple] at h
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]; omega
  · intro c _; simp
  · rintro ⟨⟨a, b⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple] at h
    simp only [Fin.cons_zero, Fin.tail_cons, Sigma.mk.injEq, Prod.mk.injEq, true_and,
      heq_eq_eq, and_true]
    omega
  · intro c _; simp

/-- `coeff n (∏ⱼ Fⱼ) = ∑_{c₀+⋯+c_{k-1} = n} ∏ⱼ coeff cⱼ Fⱼ`. -/
lemma coeff_prod_fin {R : Type*} [CommSemiring R] (k n : ℕ) (F : Fin k → R⟦X⟧) :
    coeff n (∏ j, F j) = ∑ c ∈ Finset.Nat.antidiagonalTuple k n, ∏ j, coeff (c j) (F j) := by
  induction k generalizing n with
  | zero =>
    rcases n with _ | n
    · simp
    · simp [coeff_one]
  | succ k ih =>
    rw [Fin.prod_univ_succ, coeff_mul, sum_antidiagonalTuple_succ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fin.prod_univ_succ]
    simp

section general

variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma coeff_mul_prod_aSeries (G : R⟦X⟧) (L : List ℕ) (r : ℕ) :
    coeff r (G * ∏ j : Fin L.length, PowerSeries.map (algebraMap ℚ R) (aSeriesQ L[j])) =
      ∑ c ∈ Finset.Nat.antidiagonalTuple (L.length + 1) r, coeff (c (Fin.last _)) G *
        ∏ j : Fin L.length, ((c j.castSucc : ℕ) : R) ^ (2 * L[j] - 1) := by
  have : G * ∏ j : Fin L.length, PowerSeries.map (algebraMap ℚ R) (aSeriesQ L[j]) =
      ∏ i : Fin (L.length + 1), (Fin.snoc (fun j : Fin L.length =>
        PowerSeries.map (algebraMap ℚ R) (aSeriesQ L[j])) G : Fin (L.length + 1) → R⟦X⟧) i := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring
  rw [this, coeff_prod_fin]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, coeff_map, aSeriesQ, coeff_mk, map_pow,
    map_natCast]
  ring

lemma prod_map_ySeq {n : ℕ} (x : Fin n → R) (s : Multiset ℕ) :
    (s.map (ySeq x)).prod =
      C ((s.map fun i => psumR x (2 * i) *
          algebraMap ℚ R ((2 : ℚ) / (2 * i).factorial)).prod) *
        (s.map fun i => PowerSeries.map (algebraMap ℚ R) (aSeriesQ i)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, map_mul]
    simp only [ySeq, zSeqQ, map_mul, PowerSeries.map_C]
    ring

end general

lemma multFact_eq_prod_Icc {k : ℕ} (p : k.Partition) :
    (multFact p.parts : ℚ) = ∏ j ∈ Finset.Icc 1 k, ((p.parts.count j).factorial : ℚ) := by
  unfold multFact
  push_cast
  refine Finset.prod_subset (fun j hj => ?_) (fun j _ hj => ?_)
  · rw [Multiset.mem_toFinset] at hj
    exact Finset.mem_Icc.2 ⟨p.parts_pos hj, p.le_of_mem_parts hj⟩
  · rw [Multiset.mem_toFinset] at hj
    simp [Multiset.count_eq_zero.2 hj]

lemma sum_compositions_eq {M : Type*} [CommRing M] (n r : ℕ) (L : List ℕ)
    (hL : ∀ i ∈ L, 1 ≤ i) :
    ∑ c ∈ compositions L.length r, ((leeBall n (c (Fin.last _))).card : M) *
        ∏ j : Fin L.length, ((c j.castSucc : ℕ) : M) ^ (2 * L[j] - 1) =
      ∑ c ∈ Finset.Nat.antidiagonalTuple (L.length + 1) r,
        ((leeBall n (c (Fin.last _))).card : M) *
          ∏ j : Fin L.length, ((c j.castSucc : ℕ) : M) ^ (2 * L[j] - 1) := by
  unfold compositions
  refine Finset.sum_filter_of_ne fun c _ hc => ?_
  intro j
  by_contra h
  push_neg at h
  apply hc
  have hj : 1 ≤ L[j] := hL _ (List.getElem_mem _)
  rw [Finset.prod_eq_zero (Finset.mem_univ j)]
  · ring
  · rw [show c j.castSucc = 0 by omega]
    simp only [Nat.cast_zero]
    exact zero_pow (by omega)

lemma cLam_eq_aux (n r : ℕ) {k : ℕ} (p : k.Partition) :
    ((2 * k).factorial : ℚ) * ((multFact p.parts : ℕ) : ℚ)⁻¹ *
      ((∏ j : Fin (partList p).length, (2 : ℚ) / ((2 * (partList p)[j]).factorial : ℚ)) *
      ∑ c ∈ compositions (partList p).length r,
        ((leeBall n (c (Fin.last _))).card : ℚ) *
          ∏ j : Fin (partList p).length,
            ((c j.castSucc : ℕ) : ℚ) ^ (2 * (partList p)[j] - 1)) = cLam n r p := by
  rw [cLam, multFact_eq_prod_Icc, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have : (p.parts.map fun i => ((2 * i).factorial : ℚ)).prod =
      ∏ j : Fin (partList p).length, ((2 * (partList p)[j]).factorial : ℚ) := by
    conv_lhs => rw [← partList_coe]
    rw [Multiset.map_coe, Multiset.prod_coe]; exact (Fin.prod_univ_fun_getElem _ _).symm
  rw [this]
  ring

/-- **Theorem 1.7** (explicit formula for the Q-polynomials of Lee balls).
For all `n, r, k`, `Q^k_{Bⁿ(r)}(X) = ∑_{λ ⊢ k} c_λ s_{2λ}` with `c_λ` given by equation `eq:P3-cor_Q-poly_explicit_formula`.
(The manuscript assumes `n ≥ 1`, `k ≥ 1`; the identity holds for all `n, k ≥ 0`.) -/
theorem qPoly_leeBall_explicit (n r k : ℕ) :
    (qPoly (leeBall n r) k).map (Int.castRingHom ℚ) =
      ∑ p : k.Partition, MvPolynomial.C (cLam n r p) * psumTwo (Fin n) ℚ p := by
  set x : Fin n → MvPolynomial (Fin n) ℚ := MvPolynomial.X
  have h1 : (qPoly (leeBall n r) k).map (Int.castRingHom ℚ) =
      ((2 * k).factorial : ℚ) • coeff r (ballMoment x k) := by
    rw [ballMoment, coeff_mk, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    simp [qPoly, x]
  rw [h1, ballMoment_eq, ← ballSize_series, bellPart, Finset.mul_sum, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hL : ∀ i ∈ partList p, 1 ≤ i := fun i hi => p.parts_pos ((mem_partList p).1 hi)
  have hlist : ∀ {M : Type _} [CommMonoid M] (f : ℕ → M),
      (p.parts.map f).prod = ∏ j : Fin (partList p).length, f (partList p)[j] := by
    intro M _ f
    conv_lhs => rw [← partList_coe]
    rw [Multiset.map_coe, Multiset.prod_coe]; exact (Fin.prod_univ_fun_getElem _ _).symm
  rw [bellTerm, mul_smul_comm, prod_map_ySeq, hlist, hlist, mul_left_comm, map_rat_smul,
    coeff_C_mul, coeff_mul_prod_aSeries]
  simp only [coeff_mk]
  rw [← sum_compositions_eq n r _ hL]
  set SQ : ℚ := ∑ c ∈ compositions (partList p).length r,
      ((leeBall n (c (Fin.last _))).card : ℚ) *
        ∏ j : Fin (partList p).length, ((c j.castSucc : ℕ) : ℚ) ^ (2 * (partList p)[j] - 1)
    with hSQ
  have hS : ∑ c ∈ compositions (partList p).length r,
      ((leeBall n (c (Fin.last _))).card : MvPolynomial (Fin n) ℚ) *
        ∏ j : Fin (partList p).length,
          ((c j.castSucc : ℕ) : MvPolynomial (Fin n) ℚ) ^ (2 * (partList p)[j] - 1) =
      algebraMap ℚ _ SQ := by
    simp [hSQ, map_sum, map_prod]
  have hpsum : psumTwo (Fin n) ℚ p =
      ∏ j : Fin (partList p).length, psumR x (2 * (partList p)[j]) := by
    rw [psumTwo, hlist]; rfl
  rw [hS, hpsum, Finset.prod_mul_distrib, ← map_prod, ← MvPolynomial.algebraMap_eq]
  rw [← cLam_eq_aux n r p]
  simp only [Algebra.smul_def, map_mul, map_natCast]
  ring

lemma bell_two_mul_parts {k : ℕ} (p : k.Partition) :
    (((p.parts.map (2 * ·)).bell : ℕ) : ℚ) =
      ((2 * k).factorial : ℚ) / ((p.parts.map fun i => ((2 * i).factorial : ℚ)).prod *
        (multFact p.parts : ℚ)) := by
  have h := Multiset.bell_mul_eq (p.parts.map (2 * ·))
  have hsum : (p.parts.map (2 * ·)).sum = 2 * k := by
    rw [Multiset.sum_map_mul_left, Multiset.map_id', p.parts_sum]
  have hfac : ((p.parts.map (2 * ·)).map fun j => j.factorial).prod =
      (p.parts.map fun i => (2 * i).factorial).prod := by
    rw [Multiset.map_map]; rfl
  have hinj : Function.Injective (fun i : ℕ => 2 * i) := fun a b h => by simpa using h
  have hmf : ∏ j ∈ (p.parts.map (2 * ·)).toFinset.erase 0,
      ((p.parts.map (2 * ·)).count j).factorial = multFact p.parts := by
    have h0 : (0 : ℕ) ∉ (p.parts.map (2 * ·)).toFinset := by
      simp only [Multiset.mem_toFinset, Multiset.mem_map, not_exists, not_and]
      intro i hi h2; have := p.parts_pos hi; omega
    rw [Finset.erase_eq_of_notMem h0, Multiset.toFinset_map, Finset.prod_image
      (fun a _ b _ h => hinj h), multFact]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Multiset.count_map_eq_count' _ _ hinj]
  rw [hsum, hfac, hmf] at h
  have hpos1 : ((p.parts.map fun i => ((2 * i).factorial : ℚ)).prod) ≠ 0 := by
    refine Multiset.prod_ne_zero ?_; simp [Nat.factorial_ne_zero]
  have hpos2 : (multFact p.parts : ℚ) ≠ 0 := by exact_mod_cast (multFact_pos _).ne'
  rw [eq_div_iff (mul_ne_zero hpos1 hpos2)]
  have h' : (((p.parts.map (2 * ·)).bell : ℕ) : ℚ) *
      (((p.parts.map fun i => (2 * i).factorial).prod : ℕ) : ℚ) * (multFact p.parts : ℚ) =
      ((2 * k).factorial : ℚ) := by exact_mod_cast h
  have hP : (((p.parts.map fun i => (2 * i).factorial).prod : ℕ) : ℚ) =
      (p.parts.map fun i => ((2 * i).factorial : ℚ)).prod := by
    rw [Nat.cast_multiset_prod, Multiset.map_map]; rfl
  rw [hP] at h'
  rw [← h']; ring

/-- Every coefficient `c_λ` of equation `eq:P3-cor_Q-poly_explicit_formula` is an integer. -/
theorem cLam_eq_cInt (n r : ℕ) {k : ℕ} (p : k.Partition) : cLam n r p = cInt n r p := by
  rw [← cLam_eq_aux, cInt, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← length_partList]
  have : (p.parts.map fun i => ((2 * i).factorial : ℚ)).prod =
      ∏ j : Fin (partList p).length, ((2 * (partList p)[j]).factorial : ℚ) := by
    conv_lhs => rw [← partList_coe]
    rw [Multiset.map_coe, Multiset.prod_coe]; exact (Fin.prod_univ_fun_getElem _ _).symm
  have hc : ((compSum n r (partList p) : ℕ) : ℚ) = ∑ c ∈ compositions (partList p).length r,
      ((leeBall n (c (Fin.last _))).card : ℚ) *
        ∏ j : Fin (partList p).length, ((c j.castSucc : ℕ) : ℚ) ^ (2 * (partList p)[j] - 1) := by
    rw [compSum]; push_cast; rfl
  have hcast : ((2 ^ (partList p).length * ((p.parts.map (2 * ·)).bell : ℤ) *
      (compSum n r (partList p) : ℤ) : ℤ) : ℚ) = 2 ^ (partList p).length *
      (((p.parts.map (2 * ·)).bell : ℕ) : ℚ) * ((compSum n r (partList p) : ℕ) : ℚ) := by
    push_cast; ring
  rw [hcast, hc, bell_two_mul_parts, ← this]
  have hpos1 : ((p.parts.map fun i => ((2 * i).factorial : ℚ)).prod) ≠ 0 := by
    refine Multiset.prod_ne_zero ?_; simp [Nat.factorial_ne_zero]
  have hpos2 : (multFact p.parts : ℚ) ≠ 0 := by exact_mod_cast (multFact_pos _).ne'
  generalize (∑ c ∈ compositions (partList p).length r,
      ((leeBall n (c (Fin.last _))).card : ℚ) *
        ∏ j : Fin (partList p).length, ((c j.castSucc : ℕ) : ℚ) ^ (2 * (partList p)[j] - 1)) = S
  generalize ((p.parts.map fun i => ((2 * i).factorial : ℚ)).prod) = P at hpos1 ⊢
  generalize (multFact p.parts : ℚ) = M at hpos2 ⊢
  field_simp

/-- **Theorem 1.7**, integer form: `Q^k_{Bⁿ(r)}(X) = ∑_{λ ⊢ k} c_λ s_{2λ}` in `ℤ[X₁,…,Xₙ]`. -/
theorem qPoly_leeBall_explicit_int (n r k : ℕ) :
    qPoly (leeBall n r) k = ∑ p : k.Partition, MvPolynomial.C (cInt n r p) * psumTwo (Fin n) ℤ p := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [qPoly_leeBall_explicit, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, MvPolynomial.map_C, cLam_eq_cInt, psumTwo, psumTwo, map_multiset_prod,
    Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [MvPolynomial.psum]

end LeeBall
