module

public import Mathlib

/-!
# Partition sums of exponential type (complete Bell polynomials)

For a sequence `y : ℕ → R` in a commutative `ℚ`-algebra we define
`bellPart y k = ∑_{λ ⊢ k} (∏ᵢ y_{λᵢ}) / ∏ⱼ m_λ(j)!`.
This is the coefficient of `t^k` in `exp (∑ⱼ yⱼ tʲ)`; it is the normalised complete Bell
polynomial used throughout the manuscript (equation `ExpandBellPoly`).

We prove the basic recursion `k • D_k = ∑_{j=1}^k j • y_j D_{k-j}` and derive from it all the
algebraic properties needed later (uniqueness, multiplicativity, homogeneity, special values).
-/

@[expose] public section

open Finset

namespace LeeBall

/-- The product `∏_j m(j)!` of the factorials of the multiplicities of a multiset. -/
def multFact (s : Multiset ℕ) : ℕ := ∏ j ∈ s.toFinset, (s.count j).factorial

lemma multFact_pos (s : Multiset ℕ) : 0 < multFact s :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

lemma multFact_zero : multFact 0 = 1 := rfl

lemma multFact_cons (j : ℕ) (s : Multiset ℕ) :
    multFact (j ::ₘ s) = (s.count j + 1) * multFact s := by
  unfold multFact
  by_cases hj : j ∈ s
  · have ht : (j ::ₘ s).toFinset = s.toFinset := by
      ext a; simp only [Multiset.mem_toFinset, Multiset.mem_cons]
      constructor
      · rintro (rfl | h) <;> assumption
      · exact fun h => Or.inr h
    rw [ht, ← Finset.mul_prod_erase _ _ (Multiset.mem_toFinset.2 hj),
      ← Finset.mul_prod_erase _ _ (Multiset.mem_toFinset.2 hj)]
    rw [Multiset.count_cons_self, Nat.factorial_succ, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase ha)]
  · have ht : (j ::ₘ s).toFinset = insert j s.toFinset := by
      ext a; simp
    rw [ht, Finset.prod_insert (by simpa using hj), Multiset.count_cons_self,
      Multiset.count_eq_zero.2 hj]
    simp only [zero_add, Nat.factorial_one, one_mul]
    refine Finset.prod_congr rfl fun a ha => ?_
    have : a ≠ j := by rintro rfl; exact hj (Multiset.mem_toFinset.1 ha)
    rw [Multiset.count_cons_of_ne this]

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The weight `(∏ᵢ y_{sᵢ}) / ∏ⱼ m_s(j)!` of a multiset `s` of parts. -/
def bellTerm (y : ℕ → R) (s : Multiset ℕ) : R := ((multFact s : ℚ)⁻¹) • (s.map y).prod

/-- `bellPart y k = ∑_{λ ⊢ k} (∏ᵢ y_{λᵢ}) / ∏ⱼ m_λ(j)!`, the coefficient of `t^k` in
`exp (∑ⱼ yⱼ tʲ)`. -/
def bellPart (y : ℕ → R) (k : ℕ) : R := ∑ p : k.Partition, bellTerm y p.parts

lemma bellTerm_cons (y : ℕ → R) (j : ℕ) (s : Multiset ℕ) :
    ((s.count j + 1 : ℕ) : ℚ) • bellTerm y (j ::ₘ s) = y j * bellTerm y s := by
  unfold bellTerm
  rw [multFact_cons, Multiset.map_cons, Multiset.prod_cons, smul_smul, mul_smul_comm]
  congr 1
  have h1 : ((s.count j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma bellPart_zero (y : ℕ → R) : bellPart y 0 = 1 := by
  unfold bellPart
  rw [Fintype.sum_unique]
  have : (default : (0 : ℕ).Partition).parts = 0 := by
    rcases (default : (0 : ℕ).Partition) with ⟨s, hpos, hsum⟩
    simp only
    exact Multiset.eq_zero_of_forall_notMem fun i hi => by
      have := Multiset.le_sum_of_mem hi; have := hpos hi; omega
  rw [this]; simp [bellTerm, multFact_zero]

/-- Removing a part from a partition. -/
def erasePart {k : ℕ} (p : k.Partition) (j : ℕ) (hj : j ∈ p.parts) : (k - j).Partition where
  parts := p.parts.erase j
  parts_pos hi := p.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    have := Multiset.sum_erase hj
    rw [p.parts_sum] at this; omega

/-- Adding a part to a partition. -/
def consPart {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (q : (k - j).Partition) : k.Partition where
  parts := j ::ₘ q.parts
  parts_pos hi := by
    rcases Multiset.mem_cons.1 hi with rfl | h
    · omega
    · exact q.parts_pos h
  parts_sum := by rw [Multiset.sum_cons, q.parts_sum]; omega

/-- The fundamental recursion `k • D_k = ∑_{j=1}^{k} j • y_j D_{k-j}`. -/
theorem bellPart_rec (y : ℕ → R) (k : ℕ) :
    (k : ℚ) • bellPart y k = ∑ j ∈ Icc 1 k, (j : ℚ) • (y j * bellPart y (k - j)) := by
  -- left-hand side as a sum over pairs (partition, distinct part)
  have hL : (k : ℚ) • bellPart y k =
      ∑ p : k.Partition, ∑ j ∈ p.parts.toFinset,
        (j : ℚ) • (((p.parts.count j : ℕ) : ℚ) • bellTerm y p.parts) := by
    unfold bellPart
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp_rw [smul_smul, ← Finset.sum_smul]
    congr 1
    have h := Finset.sum_multiset_count p.parts
    rw [p.parts_sum] at h
    have h2 : (k : ℚ) = ((∑ m ∈ p.parts.toFinset, Multiset.count m p.parts • m : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [h2]; push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have hR : ∑ j ∈ Icc 1 k, (j : ℚ) • (y j * bellPart y (k - j)) =
      ∑ j ∈ Icc 1 k, ∑ q : (k - j).Partition, (j : ℚ) • (y j * bellTerm y q.parts) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold bellPart
    rw [Finset.mul_sum, Finset.smul_sum]
  rw [hL, hR, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun a ha => ⟨a.2, erasePart a.1 a.2
      (Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2)⟩)
    (fun b hb => ⟨consPart (Finset.mem_Icc.1 (Finset.mem_sigma.1 hb).1).1
      (Finset.mem_Icc.1 (Finset.mem_sigma.1 hb).1).2 b.2, b.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, j⟩ ha
    have hj := Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2
    simp only [Finset.mem_sigma, Finset.mem_univ, and_true, Finset.mem_Icc]
    exact ⟨p.parts_pos hj, p.le_of_mem_parts hj⟩
  · rintro ⟨j, q⟩ hb
    simp [consPart]
  · rintro ⟨p, j⟩ ha
    have hj := Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2
    simp only
    congr 1
    ext1
    simp [consPart, erasePart, Multiset.cons_erase hj]
  · rintro ⟨j, q⟩ hb
    simp only
    congr 1
    ext1
    simp [consPart, erasePart]
  · rintro ⟨p, j⟩ ha
    have hj := Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2
    simp only [erasePart]
    congr 1
    have hc : p.parts = j ::ₘ p.parts.erase j := (Multiset.cons_erase hj).symm
    have := bellTerm_cons y j (p.parts.erase j)
    rw [← hc] at this
    rw [← this]
    congr 2
    conv_lhs => rw [hc]
    rw [Multiset.count_cons_self]

/-! ### The Euler operator `t d/dt` on power series and uniqueness -/

open PowerSeries

/-- The Euler operator `F ↦ t F'(t)`, i.e. `coeff k (euler F) = k • coeff k F`. -/
noncomputable def euler (F : PowerSeries R) : PowerSeries R := mk fun k => (k : ℚ) • coeff k F

@[simp] lemma coeff_euler (F : PowerSeries R) (k : ℕ) :
    coeff k (euler F) = (k : ℚ) • coeff k F := by simp [euler]

lemma euler_mul (F G : PowerSeries R) : euler (F * G) = euler F * G + F * euler G := by
  ext k
  simp only [coeff_euler, coeff_mul, map_add, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [smul_mul_assoc, mul_smul_comm, ← add_smul, ← hx]
  push_cast; ring

lemma euler_add (F G : PowerSeries R) : euler (F + G) = euler F + euler G := by
  ext k; simp [smul_add]

/-- The generating power series `∑ₖ bellPart y k tᵏ`. -/
noncomputable def bellSeries (y : ℕ → R) : PowerSeries R := mk (bellPart y)

/-- The "logarithmic derivative" series `∑ⱼ j yⱼ tʲ`. -/
noncomputable def logDerSeries (y : ℕ → R) : PowerSeries R := mk fun j => (j : ℚ) • y j

@[simp] lemma constantCoeff_logDerSeries (y : ℕ → R) : constantCoeff (logDerSeries y) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [logDerSeries]

lemma euler_bellSeries (y : ℕ → R) :
    euler (bellSeries y) = logDerSeries y * bellSeries y := by
  ext k
  rw [coeff_euler, coeff_mul, bellSeries, coeff_mk, bellPart_rec]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [logDerSeries, coeff_mk, Nat.cast_zero, zero_smul, zero_mul, zero_add]
  refine Finset.sum_congr (by ext; simp) fun j _ => ?_
  rw [smul_mul_assoc]

/-- Uniqueness of solutions of `t F' = Z F` with prescribed constant term. -/
lemma euler_unique {Z F G : PowerSeries R} (hZ : constantCoeff Z = 0)
    (hF : euler F = Z * F) (hG : euler G = Z * G) (h0 : constantCoeff F = constantCoeff G) :
    F = G := by
  ext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using h0
    · have e1 := congrArg (coeff k) hF
      have e2 := congrArg (coeff k) hG
      rw [coeff_euler, coeff_mul] at e1 e2
      have : ∑ p ∈ antidiagonal k, coeff p.1 Z * coeff p.2 F =
          ∑ p ∈ antidiagonal k, coeff p.1 Z * coeff p.2 G := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_antidiagonal] at hp
        rcases Nat.eq_zero_or_pos p.1 with h | h
        · rw [h, coeff_zero_eq_constantCoeff_apply, hZ, zero_mul, zero_mul]
        · rw [ih p.2 (by omega)]
      have hk' : (k : ℚ) ≠ 0 := by positivity
      have := e1.trans (this.trans e2.symm)
      have := congrArg (fun x => (k : ℚ)⁻¹ • x) this
      simpa [smul_smul, hk'] using this

lemma constantCoeff_bellSeries (y : ℕ → R) : constantCoeff (bellSeries y) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, bellSeries, coeff_mk, bellPart_zero]

/-- Characterisation of `bellSeries` by the differential equation. -/
lemma eq_bellSeries {F : PowerSeries R} (y : ℕ → R) (hF : euler F = logDerSeries y * F)
    (h0 : constantCoeff F = 1) : F = bellSeries y :=
  euler_unique (constantCoeff_logDerSeries y) hF (euler_bellSeries y)
    (by rw [h0, constantCoeff_bellSeries])

lemma eq_C_mul_bellSeries {F : PowerSeries R} (y : ℕ → R) (hF : euler F = logDerSeries y * F) :
    F = C (constantCoeff F) * bellSeries y := by
  refine euler_unique (constantCoeff_logDerSeries y) hF ?_ (by simp [constantCoeff_bellSeries])
  rw [euler_mul, euler_bellSeries]
  have : euler (C (constantCoeff F)) = 0 := by
    ext k; rcases k with _ | k <;> simp [coeff_C]
  rw [this]; ring

/-- Multiplicativity: `exp (A + B) = exp A * exp B`. -/
theorem bellSeries_add (y y' : ℕ → R) :
    bellSeries (y + y') = bellSeries y * bellSeries y' := by
  symm
  refine eq_bellSeries _ ?_ ?_
  · rw [euler_mul, euler_bellSeries, euler_bellSeries]
    have : logDerSeries (y + y') = logDerSeries y + logDerSeries y' := by
      ext k; simp [logDerSeries, smul_add]
    rw [this]; ring
  · simp [constantCoeff_bellSeries]

theorem bellPart_add (y y' : ℕ → R) (k : ℕ) :
    bellPart (y + y') k = ∑ p ∈ antidiagonal k, bellPart y p.1 * bellPart y' p.2 := by
  have := congrArg (coeff k) (bellSeries_add y y')
  simpa [bellSeries, coeff_mul] using this

theorem bellSeries_sum {ι : Type*} (s : Finset ι) (y : ι → ℕ → R) :
    bellSeries (∑ i ∈ s, y i) = ∏ i ∈ s, bellSeries (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    symm; refine eq_bellSeries _ ?_ (by simp)
    ext k; simp [logDerSeries, coeff_one]; tauto
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, bellSeries_add, ih]

/-- Compatibility with algebra homomorphisms. -/
theorem map_bellPart {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →ₐ[ℚ] S) (y : ℕ → R)
    (k : ℕ) : f (bellPart y k) = bellPart (fun j => f (y j)) k := by
  simp only [bellPart, bellTerm, map_sum, map_smul, map_multiset_prod, Multiset.map_map]
  rfl

/-- Homogeneity: `D_k(cʲ yⱼ) = cᵏ D_k(y)`. -/
theorem bellPart_homog (c : R) (y : ℕ → R) (k : ℕ) :
    bellPart (fun j => c ^ j * y j) k = c ^ k * bellPart y k := by
  simp only [bellPart, bellTerm, Finset.mul_sum, mul_smul_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [Multiset.prod_map_mul, show c ^ k = c ^ p.parts.sum by rw [p.parts_sum]]
  congr 1
  induction p.parts using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, pow_add]

/-- `exp (∑ⱼ xʲ tʲ / j) = 1 / (1 - x t)`. -/
theorem bellPart_geom (x : R) (s : ℕ) :
    bellPart (fun j => ((j : ℚ)⁻¹) • x ^ j) s = x ^ s := by
  have h := eq_bellSeries (F := mk fun s => x ^ s) (fun j => ((j : ℚ)⁻¹) • x ^ j) ?_ (by simp)
  · have := congrArg (coeff s) h
    simpa [bellSeries] using this.symm
  ext k
  rw [coeff_euler, coeff_mul, coeff_mk]
  simp only [logDerSeries, coeff_mk, smul_smul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have : ∀ i ∈ Finset.range (k + 1), (((i : ℚ) * (i : ℚ)⁻¹) • x ^ i) * x ^ (k - i) =
      if i = 0 then 0 else x ^ k := by
    intro i hi
    rw [Finset.mem_range] at hi
    split_ifs with h
    · simp [h]
    · rw [mul_inv_cancel₀ (by exact_mod_cast h), one_smul, ← pow_add]
      congr 1; omega
  rw [Finset.sum_congr rfl this, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const]
  have : ((Finset.range (k + 1)).filter (fun i => ¬ i = 0)).card = k := by
    rw [Finset.filter_ne' , Finset.card_erase_of_mem (by simp)]; simp
  rw [this, Nat.cast_smul_eq_nsmul]

/-- `exp (c ∑ⱼ tʲ / j) = (1 - t)^{-c}`, so `D_s(c/j) = binom(c + s - 1, s)`. -/
theorem bellPart_const (c s : ℕ) :
    bellPart (fun j => ((j : ℚ)⁻¹ * c) • (1 : R)) s = ((c + s - 1).choose s : R) := by
  have key : bellSeries (fun j => ((j : ℚ)⁻¹ * c) • (1 : R)) = (mk 1 : PowerSeries R) ^ c := by
    induction c with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, zero_smul, pow_zero]
      symm; refine eq_bellSeries _ ?_ (by simp)
      ext k; simp [logDerSeries, coeff_one]; tauto
    | succ c ih =>
      have : (fun j : ℕ => ((j : ℚ)⁻¹ * ((c + 1 : ℕ) : ℚ)) • (1 : R)) =
          (fun j : ℕ => ((j : ℚ)⁻¹ * c) • (1 : R)) + (fun j : ℕ => ((j : ℚ)⁻¹) • (1 : R) ^ j) := by
        funext j; simp only [Pi.add_apply, one_pow]; push_cast; rw [← add_smul]; ring_nf
      rw [this, bellSeries_add, ih, pow_succ]
      congr 1
      ext k; simpa [bellSeries] using bellPart_geom (1 : R) k
  have := congrArg (coeff s) key
  rw [bellSeries, coeff_mk] at this
  rw [this]
  rcases c with _ | c
  · rcases s with _ | s <;> simp [coeff_one]
  · rw [mk_one_pow_eq_mk_choose_add, coeff_mk]
    congr 1
    rw [show c + 1 + s - 1 = c + s by omega, Nat.choose_symm_add]

end LeeBall
