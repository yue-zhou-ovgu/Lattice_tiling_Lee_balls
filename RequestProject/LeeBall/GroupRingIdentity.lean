module

public import RequestProject.LeeBall.Moments

/-!
# The formal group-ring identity for Lee balls

For a commutative group `G` and `x₁, …, xₙ ∈ G` put `T = e + ∑ᵢ (xᵢ + xᵢ⁻¹) ∈ ℚ[G]`.  Then
```
∑_{b ∈ Bⁿ(r)} x^b = ∑_{t=0}^{⌊r/2⌋} (-1)^t C(n,t) · D_{r-2t}(j ↦ T^{(j)}/j)
```
where `D_s` is `bellPart`.  This is the identity established in the proof of Theorem 1.8.
-/

@[expose] public section

open Finset PowerSeries

namespace LeeBall

variable {G : Type*} [CommGroup G]

/-- `A^{(t)} = ∑_g a_g g^t` for `A = ∑_g a_g g ∈ ℚ[G]`. -/
noncomputable def pw (t : ℕ) (A : MonoidAlgebra ℚ G) : MonoidAlgebra ℚ G :=
  Finsupp.mapDomain (fun g => g ^ t) A

lemma pw_of (t : ℕ) (g : G) : pw t (MonoidAlgebra.of ℚ G g) = MonoidAlgebra.of ℚ G (g ^ t) := by
  simp [pw, MonoidAlgebra.of_apply, Finsupp.mapDomain_single]

lemma pw_add (t : ℕ) (A B : MonoidAlgebra ℚ G) : pw t (A + B) = pw t A + pw t B :=
  Finsupp.mapDomain_add

lemma pw_sum {ι : Type*} (s : Finset ι) (t : ℕ) (A : ι → MonoidAlgebra ℚ G) :
    pw t (∑ i ∈ s, A i) = ∑ i ∈ s, pw t (A i) :=
  Finsupp.mapDomain_finset_sum

/-- The element `T = e + ∑ᵢ (xᵢ + xᵢ⁻¹)` of `ℚ[G]`. -/
noncomputable def tElem {n : ℕ} (x : Fin n → G) : MonoidAlgebra ℚ G :=
  MonoidAlgebra.of ℚ G 1 + ∑ i, (MonoidAlgebra.of ℚ G (x i) + MonoidAlgebra.of ℚ G (x i)⁻¹)

/-- `x^b = ∏ᵢ xᵢ^{bᵢ}`. -/
def gpow {n : ℕ} (x : Fin n → G) (b : Fin n → ℤ) : G := ∏ i, x i ^ b i

local notation "ofG" => MonoidAlgebra.of ℚ G

lemma geom_mul_one_sub (u : MonoidAlgebra ℚ G) :
    (mk fun a => u ^ a) * (1 - C u * X) = 1 := by
  ext s
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm _ (C u), mul_assoc]
  rcases s with _ | s
  · simp
  · rw [coeff_C_mul, coeff_succ_mul_X]; simp [pow_succ, mul_comm]

/-- `∑_{a = ±t} g^a`. -/
noncomputable def sphere1 (g : G) (t : ℕ) : MonoidAlgebra ℚ G :=
  ∑ a ∈ ({(t : ℤ), -(t : ℤ)} : Finset ℤ), ofG (g ^ a)

lemma sphere1_mul (g : G) :
    (mk (sphere1 g)) * ((1 - C (ofG g) * X) * (1 - C (ofG g⁻¹) * X)) = 1 - X ^ 2 := by
  have huv : ofG g * ofG g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hfac : (1 - C (ofG g) * X) * (1 - C (ofG g⁻¹) * X) =
      1 - C (ofG g + ofG g⁻¹) * X + X ^ 2 := by
    have : (C (ofG g) * X) * (C (ofG g⁻¹) * X) = (X ^ 2 : (MonoidAlgebra ℚ G)⟦X⟧) := by
      rw [mul_mul_mul_comm, ← map_mul, huv, map_one, one_mul, sq]
    rw [map_add]; linear_combination this
  rw [hfac]
  set u := ofG g
  set v := ofG g⁻¹
  have hs : ∀ t : ℕ, 1 ≤ t → sphere1 g t = u ^ t + v ^ t := by
    intro t ht
    rw [sphere1, Finset.sum_pair (by omega)]
    simp [u, v, zpow_neg, ← map_pow]
  have h0 : sphere1 g 0 = 1 := by simp [sphere1]; rfl
  refine PowerSeries.ext fun s => ?_
  have e : ∀ F : (MonoidAlgebra ℚ G)⟦X⟧, coeff s (F * (1 - C (u + v) * X + X ^ 2)) =
      coeff s F - (u + v) * (if 1 ≤ s then coeff (s - 1) F else 0) +
        (if 2 ≤ s then coeff (s - 2) F else 0) := by
    intro F
    rw [mul_add, mul_sub, mul_one, map_add, map_sub, ← mul_assoc, mul_comm F (C _), mul_assoc,
      coeff_C_mul, show F * X = F * X ^ 1 by rw [pow_one], coeff_mul_X_pow',
      coeff_mul_X_pow']
  rw [e]
  rcases s with _ | _ | _ | s
  · simp [h0]
  · simp only [coeff_mk, map_sub, coeff_one, coeff_X_pow, hs 1 le_rfl, h0]
    simp
  · simp only [coeff_mk, map_sub, coeff_one, coeff_X_pow, hs 2 (by omega), hs 1 le_rfl, h0]
    simp only [show (1 : ℕ) ≤ 0 + 1 + 1 by omega, show 2 ≤ 0 + 1 + 1 by omega, if_true,
      show 0 + 1 + 1 - 1 = 1 by omega, show 0 + 1 + 1 - 2 = 0 by omega, h0,
      show (0 + 1 + 1 : ℕ) ≠ 0 by omega, if_false, show (0 + 1 + 1 : ℕ) = 2 by omega,
      hs 1 le_rfl, hs 2 (by omega)]
    linear_combination (-2 : MonoidAlgebra ℚ G) * huv
  · simp only [coeff_mk, map_sub, coeff_one, coeff_X_pow,
      show (1 : ℕ) ≤ s + 1 + 1 + 1 by omega, show 2 ≤ s + 1 + 1 + 1 by omega, if_true,
      show s + 1 + 1 + 1 - 1 = s + 2 by omega, show s + 1 + 1 + 1 - 2 = s + 1 by omega,
      hs (s + 1 + 1 + 1) (by omega), hs (s + 2) (by omega), hs (s + 1) (by omega),
      show (s + 1 + 1 + 1 : ℕ) ≠ 0 by omega, show s + 1 + 1 + 1 ≠ 2 by omega, if_false]
    linear_combination (-(u ^ (s + 1) + v ^ (s + 1))) * huv

lemma bellSeries_of (g : G) :
    bellSeries (fun j : ℕ => (j : ℚ)⁻¹ • ofG (g ^ j)) = mk fun a => (ofG g) ^ a := by
  ext1 s
  simp only [bellSeries, coeff_mk, map_pow]
  exact bellPart_geom _ s

/-- One-dimensional case: `∑_a g^a q^{|a|} = (1 - q²) exp(∑ⱼ (gʲ + g⁻ʲ) qʲ / j)`. -/
lemma sphere1_eq (g : G) :
    mk (sphere1 g) = (1 - X ^ 2) *
      bellSeries (fun j : ℕ => (j : ℚ)⁻¹ • (ofG (g ^ j) + ofG (g⁻¹ ^ j))) := by
  have hsplit : (fun j : ℕ => (j : ℚ)⁻¹ • (ofG (g ^ j) + ofG (g⁻¹ ^ j))) =
      (fun j : ℕ => (j : ℚ)⁻¹ • ofG (g ^ j)) +
        (fun j : ℕ => (j : ℚ)⁻¹ • ofG (g⁻¹ ^ j)) := by
    funext j; simp [smul_add]
  rw [hsplit, bellSeries_add, bellSeries_of, bellSeries_of, ← sphere1_mul g]
  have h1 := geom_mul_one_sub (G := G) (ofG g)
  have h2 := geom_mul_one_sub (G := G) (ofG g⁻¹)
  linear_combination (-(mk (sphere1 g))) * h1 +
    (-(mk (sphere1 g)) * (mk fun a => ofG g ^ a) * (1 - C (ofG g) * X)) * h2

lemma gpow_cons {n : ℕ} (x : Fin (n + 1) → G) (a : ℤ) (b : Fin n → ℤ) :
    gpow x (Fin.cons a b) = x 0 ^ a * gpow (Fin.tail x) b := by
  simp [gpow, Fin.prod_univ_succ, Fin.tail]

/-- `∑_t (∑_{b ∈ Sⁿ(t)} x^b) q^t = ∏ᵢ ∑_a xᵢ^a q^{|a|}`. -/
lemma sphereG_eq {n : ℕ} (x : Fin n → G) :
    (mk fun t => ∑ b ∈ leeSphere n t, ofG (gpow x b)) = ∏ i, mk (sphere1 (x i)) := by
  induction n with
  | zero =>
    ext1 t
    rw [Finset.univ_eq_empty, Finset.prod_empty, coeff_mk, leeSphere_dim_zero]
    split_ifs with h <;> simp [h, gpow, coeff_one]; rfl
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hih := ih (Fin.tail x)
    simp only [Fin.tail] at hih
    rw [← hih]
    ext1 t
    rw [coeff_mk, sum_leeSphere_succ, sum_Icc_eq_sum_pair, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (mk (sphere1 (x 0))) *
        coeff j (mk fun t => ∑ b ∈ leeSphere n t, ofG (gpow (Fin.tail x) b)))]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [coeff_mk, sphere1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hat : a.natAbs = s := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> simp
    rw [hat, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gpow_cons, map_mul]

/-- The coefficient of `q^r` in `(1 - q²)ⁿ F`. -/
lemma coeff_one_sub_X_sq_pow_mul {R : Type*} [CommRing R] (n r : ℕ) (F : R⟦X⟧) :
    coeff r ((1 - X ^ 2) ^ n * F) =
      ∑ t ∈ range (r / 2 + 1), ((-1) ^ t * (n.choose t : R)) * coeff (r - 2 * t) F := by
  have h : (1 - X ^ 2 : R⟦X⟧) ^ n =
      ∑ t ∈ range (n + 1), C ((-1) ^ t * (n.choose t : R)) * X ^ (2 * t) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [one_pow, mul_one, neg_pow, ← pow_mul, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [h, Finset.sum_mul, map_sum]
  simp_rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp_rw [mul_assoc]
  rw [show ∑ t ∈ range (r / 2 + 1), (-1) ^ t * ((n.choose t : R) * coeff (r - 2 * t) F) =
    ∑ t ∈ (range (r / 2 + 1)).filter (fun t => 2 * t ≤ r),
      (-1) ^ t * ((n.choose t : R) * coeff (r - 2 * t) F) by
    rw [Finset.filter_true_of_mem]; intro t ht; simp at ht; omega]
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · intro t; simp only [Finset.mem_filter, Finset.mem_range]; omega
  · intro t ht
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at ht
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro t _; rfl

/-- **The formal ball identity** (proof of Theorem 1.8).  For `x₁,…,xₙ` in a commutative group
and `T = e + ∑ᵢ (xᵢ + xᵢ⁻¹)`:
`∑_{b ∈ Bⁿ(r)} x^b = ∑_{t ≤ r/2} (-1)^t C(n,t) D_{r-2t}(j ↦ T^{(j)}/j)`. -/
theorem ball_groupRing_identity {n : ℕ} (x : Fin n → G) (r : ℕ) :
    ∑ b ∈ leeBall n r, ofG (gpow x b) =
      ∑ t ∈ range (r / 2 + 1), ((-1) ^ t * (n.choose t : MonoidAlgebra ℚ G)) *
        bellPart (fun j => (j : ℚ)⁻¹ • pw j (tElem x)) (r - 2 * t) := by
  have hball : (mk fun t => ∑ b ∈ leeBall n t, ofG (gpow x b)) =
      (mk fun t => ∑ b ∈ leeSphere n t, ofG (gpow x b)) * PowerSeries.mk 1 := by
    ext1 t
    rw [coeff_mk, coeff_mul, sum_leeBall_eq_sum_leeSphere,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        coeff i (mk fun t => ∑ b ∈ leeSphere n t, ofG (gpow x b)) *
        coeff j (mk 1 : (MonoidAlgebra ℚ G)⟦X⟧))]
    simp
  have hone : (mk 1 : (MonoidAlgebra ℚ G)⟦X⟧) =
      bellSeries (fun j : ℕ => (j : ℚ)⁻¹ • ofG ((1 : G) ^ j)) := by
    rw [bellSeries_of, map_one]; ext1 s; simp
  have hT : (fun j : ℕ => (j : ℚ)⁻¹ • pw j (tElem x)) =
      (fun j : ℕ => (j : ℚ)⁻¹ • ofG ((1 : G) ^ j)) + ∑ i, (fun j : ℕ =>
        (j : ℚ)⁻¹ • (ofG (x i ^ j) + ofG ((x i)⁻¹ ^ j))) := by
    funext j
    simp only [tElem, pw_add, pw_sum, pw_of, Pi.add_apply, Finset.sum_apply, smul_add,
      Finset.smul_sum, inv_pow]
  have hser : (mk fun t => ∑ b ∈ leeBall n t, ofG (gpow x b)) =
      (1 - X ^ 2) ^ n * bellSeries (fun j => (j : ℚ)⁻¹ • pw j (tElem x)) := by
    rw [hball, sphereG_eq, hT, bellSeries_add, bellSeries_sum, ← hone]
    simp_rw [sphere1_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have := congrArg (coeff r) hser
  rw [coeff_mk, coeff_one_sub_X_sq_pow_mul] at this
  rw [this]
  simp [bellSeries]

end LeeBall
