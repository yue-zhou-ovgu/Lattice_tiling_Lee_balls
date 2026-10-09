module

public import RequestProject.LeeBall.Basic
public import RequestProject.LeeBall.OneDim

/-!
# Generating functions of the moments of Lee spheres and Lee balls

For `x : Fin n → R` (`R` a commutative `ℚ`-algebra) we prove
```
∑_r (∑_{b ∈ Sⁿ(r)} ⟨x,b⟩^{2k} / (2k)!) q^r = ((1+q)/(1-q))ⁿ · D_k(y),
```
where `D_k` is `bellPart` and `y_j = 2 s_{2j}(x) A_j(q) / (2j)!`.  This is the content of
Theorems 3.2 and 3.3 of the manuscript (in a form valid in any commutative `ℚ`-algebra).
-/

@[expose] public section

open Finset PowerSeries

namespace LeeBall

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Power sums `s_m(x) = ∑ᵢ xᵢ^m`. -/
def psumR {n : ℕ} (x : Fin n → R) (m : ℕ) : R := ∑ i, x i ^ m

/-- The sequence `y_j = 2 s_{2j}(x) A_j(q) / (2j)!` of power series. -/
noncomputable def ySeq {n : ℕ} (x : Fin n → R) (j : ℕ) : R⟦X⟧ :=
  C (psumR x (2 * j)) * map (algebraMap ℚ R) (zSeqQ j)

/-- The normalised moment series of the Lee spheres:
`∑_r (∑_{b ∈ Sⁿ(r)} ⟨x,b⟩^{2k} / (2k)!) q^r`. -/
noncomputable def sphereMoment {n : ℕ} (x : Fin n → R) (k : ℕ) : R⟦X⟧ :=
  mk fun r => ((2 * k).factorial : ℚ)⁻¹ • ∑ b ∈ leeSphere n r, (∑ i, (b i : R) * x i) ^ (2 * k)

/-- Grouping a sum over `[-r, r]` according to `|a|`. -/
lemma sum_Icc_eq_sum_pair {M : Type*} [AddCommMonoid M] (r : ℕ) (G : ℤ → M) :
    ∑ a ∈ Finset.Icc (-(r : ℤ)) r, G a =
      ∑ t ∈ range (r + 1), ∑ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ), G a := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hI : Finset.Icc (-((r + 1 : ℕ) : ℤ)) ((r + 1 : ℕ) : ℤ) =
        ({((r + 1 : ℕ) : ℤ), -((r + 1 : ℕ) : ℤ)} : Finset ℤ) ∪ Finset.Icc (-(r : ℤ)) r := by
      ext a; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_Icc]; push_cast; omega
    have hdisj : Disjoint ({((r + 1 : ℕ) : ℤ), -((r + 1 : ℕ) : ℤ)} : Finset ℤ)
        (Finset.Icc (-(r : ℤ)) r) := by
      rw [Finset.disjoint_left]
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [Finset.mem_Icc]; push_cast at ha; omega
    rw [hI, Finset.sum_union hdisj, ih, Finset.sum_range_succ _ (r + 1), add_comm]

lemma sum_pair_intCast_pow (t m : ℕ) :
    ∑ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ), ((a : R)) ^ m = algebraMap ℚ R (symPow t m) := by
  unfold symPow
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_pow, map_intCast]

lemma sum_range_succ_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ m ∈ range (2 * k + 1), f m =
      ∑ i ∈ range (k + 1), f (2 * i) + ∑ i ∈ range k, f (2 * i + 1) := by
  rw [Finset.sum_range_succ, sum_range_two_mul, Finset.sum_add_distrib, Finset.sum_range_succ]
  abel

/-- Binomial expansion summed over `a = ±t`; odd powers cancel. -/
lemma binom_sym (c u : R) (t k : ℕ) :
    ((2 * k).factorial : ℚ)⁻¹ • ∑ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ), ((a : R) * c + u) ^ (2 * k)
      = ∑ p ∈ antidiagonal k, (((2 * p.1).factorial : ℚ)⁻¹ • u ^ (2 * p.1)) *
          (c ^ (2 * p.2) * algebraMap ℚ R (((2 * p.2).factorial : ℚ)⁻¹ * symPow t (2 * p.2))) := by
  have e : ∑ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ), ((a : R) * c + u) ^ (2 * k) =
      ∑ m ∈ range (2 * k + 1), algebraMap ℚ R (symPow t m) * c ^ m * u ^ (2 * k - m) *
        ((2 * k).choose m : R) := by
    simp_rw [add_pow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← sum_pair_intCast_pow]
    simp_rw [mul_pow]
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [e, sum_range_succ_two_mul]
  simp only [symPow_odd, map_zero, zero_mul, Finset.sum_const_zero, add_zero, Finset.smul_sum]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [Prod.swap_prod_mk]
  have hc : ((2 * k).choose (2 * i) : ℚ) * (2 * i).factorial * (2 * (k - i)).factorial =
      (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show 2 * i ≤ 2 * k by omega)
    rw [show 2 * k - 2 * i = 2 * (k - i) by omega] at this
    exact_mod_cast this
  rw [show 2 * k - 2 * i = 2 * (k - i) by omega]
  have h1 : ((2 * i).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * (k - i)).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * k).choose (2 * i) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have key : ((2 * k).factorial : ℚ)⁻¹ * ((2 * k).choose (2 * i) : ℚ) =
      ((2 * (k - i)).factorial : ℚ)⁻¹ * ((2 * i).factorial : ℚ)⁻¹ := by
    rw [← hc]; field_simp
  rw [Algebra.smul_def, Algebra.smul_def,
    show ((2 * k).choose (2 * i) : R) = algebraMap ℚ R ((2 * k).choose (2 * i) : ℚ) by simp]
  calc _ = algebraMap ℚ R (((2 * k).factorial : ℚ)⁻¹ * ((2 * k).choose (2 * i) : ℚ)) *
        algebraMap ℚ R (symPow t (2 * i)) * c ^ (2 * i) * u ^ (2 * (k - i)) := by
          rw [map_mul]; ring
    _ = _ := by rw [key]; simp only [map_mul]; ring

/-- `bellPart` commutes with ring homomorphisms between `ℚ`-algebras. -/
theorem map_bellPart' {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) (y : ℕ → R)
    (k : ℕ) : f (bellPart y k) = bellPart (fun j => f (y j)) k := by
  simp only [bellPart, bellTerm, map_sum, map_rat_smul, map_multiset_prod, Multiset.map_map]
  rfl

lemma bellSeries_zero : bellSeries (0 : ℕ → R) = 1 := by
  symm; refine eq_bellSeries _ ?_ (by simp)
  ext k; simp [logDerSeries, coeff_one]; tauto

lemma bellPart_zero_seq (k : ℕ) : bellPart (0 : ℕ → R) k = if k = 0 then 1 else 0 := by
  have := congrArg (coeff k) (bellSeries_zero (R := R))
  simpa [bellSeries, coeff_one] using this

/-- The one-dimensional moment series `∑_t (∑_{a=±t} (a c)^{2j}) q^t / (2j)!`. -/
noncomputable def oneDimR (c : R) (j : ℕ) : R⟦X⟧ :=
  C (c ^ (2 * j)) * map (algebraMap ℚ R) (oneDimQ j)

lemma coeff_oneDimR (c : R) (j t : ℕ) :
    coeff t (oneDimR c j) =
      c ^ (2 * j) * algebraMap ℚ R (((2 * j).factorial : ℚ)⁻¹ * symPow t (2 * j)) := by
  rw [oneDimR, coeff_C_mul, coeff_map, oneDimQ, coeff_mk]

/-- Splitting off the first coordinate: the moment series of `S^{n+1}` is a binomial
convolution of the moment series of `S^n` and of `S^1`. -/
theorem sphereMoment_cons {n : ℕ} (c : R) (x : Fin n → R) (k : ℕ) :
    sphereMoment (Fin.cons c x : Fin (n + 1) → R) k =
      ∑ p ∈ antidiagonal k, sphereMoment x p.1 * oneDimR c p.2 := by
  ext r
  have hL : coeff r (sphereMoment (Fin.cons c x : Fin (n + 1) → R) k) =
      ∑ t ∈ range (r + 1), ∑ b ∈ leeSphere n (r - t),
        ((2 * k).factorial : ℚ)⁻¹ • ∑ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ),
          ((a : R) * c + ∑ i, (b i : R) * x i) ^ (2 * k) := by
    rw [sphereMoment, coeff_mk, sum_leeSphere_succ, sum_Icc_eq_sum_pair, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hat : ∀ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ), a.natAbs = t := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp
    rw [Finset.sum_congr rfl fun a ha => by rw [hat a ha]]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp [Fin.sum_univ_succ]
  have hR : coeff r (∑ p ∈ antidiagonal k, sphereMoment x p.1 * oneDimR c p.2) =
      ∑ t ∈ range (r + 1), ∑ b ∈ leeSphere n (r - t), ∑ p ∈ antidiagonal k,
        (((2 * p.1).factorial : ℚ)⁻¹ • (∑ i, (b i : R) * x i) ^ (2 * p.1)) *
          (c ^ (2 * p.2) * algebraMap ℚ R (((2 * p.2).factorial : ℚ)⁻¹ *
            symPow t (2 * p.2))) := by
    rw [map_sum]
    simp_rw [coeff_mul]
    rw [Finset.sum_comm, ← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Prod.swap_prod_mk, sphereMoment, coeff_mk, coeff_oneDimR, Finset.smul_sum,
      Finset.sum_mul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun b _ => binom_sym _ _ _ _

/-- The series `(1+q)/(1-q)` in `R⟦q⟧`. -/
noncomputable def pSeries : R⟦X⟧ := map (algebraMap ℚ R) pSeriesQ

lemma oneDimR_eq (c : R) (j : ℕ) : oneDimR c j =
    pSeries * bellPart (fun i => C (c ^ (2 * i)) * PowerSeries.map (algebraMap ℚ R) (zSeqQ i)) j := by
  rw [oneDimR, oneDimQ_eq, map_mul, map_bellPart']
  have := bellPart_homog (C (c ^ 2)) (fun i => map (algebraMap ℚ R) (zSeqQ i)) j
  simp only [← map_pow, ← pow_mul] at this
  rw [this, pSeries]; ring

/-- **Theorem 3.2** (general form). The moment generating series of the Lee spheres:
`∑_r (∑_{b ∈ Sⁿ(r)} ⟨x,b⟩^{2k}/(2k)!) q^r = ((1+q)/(1-q))ⁿ · D_k(y)` with
`y_j = 2 s_{2j}(x) A_j(q)/(2j)!`. -/
theorem sphereMoment_eq {n : ℕ} (x : Fin n → R) (k : ℕ) :
    sphereMoment x k = pSeries ^ n * bellPart (ySeq x) k := by
  induction n generalizing k with
  | zero =>
    have hy : ySeq x = 0 := by funext j; simp [ySeq, psumR]
    rw [hy, bellPart_zero_seq, pow_zero, one_mul]
    ext r
    simp only [sphereMoment, coeff_mk, leeSphere_dim_zero, Finset.univ_eq_empty,
      Finset.sum_empty]
    split_ifs with hr hk hk <;> simp [hr, hk, coeff_one]
  | succ n ih =>
    conv_lhs => rw [← Fin.cons_self_tail x]
    rw [sphereMoment_cons]
    simp_rw [ih, oneDimR_eq]
    have hy : ySeq x = ySeq (Fin.tail x) +
        fun i => C (x 0 ^ (2 * i)) * PowerSeries.map (algebraMap ℚ R) (zSeqQ i) := by
      funext i
      simp only [ySeq, psumR, Pi.add_apply, Fin.sum_univ_succ, map_add, add_mul, Fin.tail]
      ring
    rw [hy, bellPart_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring

/-- The normalised moment series of the Lee balls:
`∑_r (∑_{b ∈ Bⁿ(r)} ⟨x,b⟩^{2k} / (2k)!) q^r`. -/
noncomputable def ballMoment {n : ℕ} (x : Fin n → R) (k : ℕ) : R⟦X⟧ :=
  mk fun r => ((2 * k).factorial : ℚ)⁻¹ • ∑ b ∈ leeBall n r, (∑ i, (b i : R) * x i) ^ (2 * k)

lemma ballMoment_eq_sphereMoment_mul {n : ℕ} (x : Fin n → R) (k : ℕ) :
    ballMoment x k = sphereMoment x k * PowerSeries.mk 1 := by
  ext r
  rw [ballMoment, coeff_mk, coeff_mul, sum_leeBall_eq_sum_leeSphere, Finset.smul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (sphereMoment x k) *
      coeff j (PowerSeries.mk 1 : R⟦X⟧))]
  simp [sphereMoment]

/-- **Theorem 3.3** (general form). The moment generating series of the Lee balls:
`∑_r (∑_{b ∈ Bⁿ(r)} ⟨x,b⟩^{2k}/(2k)!) q^r = (1+q)ⁿ/(1-q)^{n+1} · D_k(y)`. -/
theorem ballMoment_eq {n : ℕ} (x : Fin n → R) (k : ℕ) :
    ballMoment x k = pSeries ^ n * PowerSeries.mk 1 * bellPart (ySeq x) k := by
  rw [ballMoment_eq_sphereMoment_mul, sphereMoment_eq]; ring

/-- The generating function of the sizes of Lee balls, `∑_r |Bⁿ(r)| q^r = Pⁿ/(1-q)`. -/
theorem ballSize_series (n : ℕ) :
    (PowerSeries.mk fun r => ((leeBall n r).card : R)) = pSeries ^ n * PowerSeries.mk 1 := by
  have h := ballMoment_eq (R := R) (fun _ : Fin n => (0 : R)) 0
  rw [bellPart_zero, mul_one] at h
  rw [← h]
  ext r
  simp [ballMoment]

/-- The generating function of the sizes of Lee spheres, `∑_r |Sⁿ(r)| q^r = Pⁿ`. -/
theorem sphereSize_series (n : ℕ) :
    (PowerSeries.mk fun r => ((leeSphere n r).card : R)) = pSeries ^ n := by
  have h := sphereMoment_eq (R := R) (fun _ : Fin n => (0 : R)) 0
  rw [bellPart_zero, mul_one] at h
  rw [← h]
  ext r
  simp [sphereMoment]

end LeeBall
