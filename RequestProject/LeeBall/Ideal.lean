module

public import RequestProject.LeeBall.QPoly
public import RequestProject.LeeBall.GroupRing

/-!
# Section 4: ideal-theoretic nonexistence criteria

* Lemma 2.6: a finite abelian group of order `p m` maps onto `(𝔽_p, +)` with fibres of size `m`;
* equation `eq:power_sum_value`: power sums over `𝔽_p`;
* Lemma 4.2, Theorem 4.3, Theorem 1.9 and Theorem 4.1 (Qureshi's `p`-condition).
-/

@[expose] public section

open Finset

namespace LeeBall

lemma exists_surj_addHom_of_ne_zero {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {v : V} (hv : v ≠ 0) : ∃ f : V →+ ZMod p, Function.Surjective f := by
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ZMod p] ZMod p, f v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod p) v).1 hcon)
  refine ⟨f.toAddMonoidHom, fun a => ⟨(a * (f v)⁻¹) • v, ?_⟩⟩
  simp only [LinearMap.toAddMonoidHom_coe, map_smul, smul_eq_mul]
  rw [mul_assoc, inv_mul_cancel₀ hf, mul_one]

/-- **Lemma 2.6.** If `G` is a finite abelian group of order `p m` with `p` prime, then there is a
surjective homomorphism `Φ : G → (𝔽_p, +)`, and every fibre of `Φ` has exactly `m` elements. -/
theorem exists_surj_hom_zmod {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {p m : ℕ}
    [hp : Fact p.Prime] (hG : Fintype.card G = p * m) :
    ∃ Φ : G →+ ZMod p, Function.Surjective Φ ∧
      ∀ a : ZMod p, (univ.filter fun g => Φ g = a).card = m := by
  -- the subgroup `pG` and the quotient `G / pG`, an `𝔽_p`-vector space
  let K : AddSubgroup G := (nsmulAddMonoidHom p : G →+ G).range
  have hQ : ∀ x : (G ⧸ K), p • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H g =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨g, rfl⟩
  letI : Module (ZMod p) (G ⧸ K) := AddCommGroup.zmodModule hQ
  -- `(G ⧸ K)` is nontrivial: otherwise multiplication by `p` would be bijective
  obtain ⟨g0, hg0⟩ := exists_prime_addOrderOf_dvd_card p (G := G) ⟨m, hG⟩
  have hne : (QuotientAddGroup.mk g0 : (G ⧸ K)) ≠ 0 ∨ ∃ v : (G ⧸ K), v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsurj : Function.Surjective (nsmulAddMonoidHom p : G →+ G) := by
      intro g
      have : (QuotientAddGroup.mk g : (G ⧸ K)) = 0 := hcon.2 _
      rw [QuotientAddGroup.eq_zero_iff] at this
      exact this
    have hinj := Finite.injective_iff_surjective.2 hsurj
    have h1 : (nsmulAddMonoidHom p : G →+ G) g0 = (nsmulAddMonoidHom p : G →+ G) 0 := by
      simp [← hg0, addOrderOf_nsmul_eq_zero]
    have := hinj h1
    rw [this, addOrderOf_zero] at hg0
    exact hp.out.one_lt.ne hg0
  obtain ⟨v, hv⟩ : ∃ v : (G ⧸ K), v ≠ 0 := by
    rcases hne with h | h
    · exact ⟨_, h⟩
    · exact h
  obtain ⟨f, hf⟩ := exists_surj_addHom_of_ne_zero (p := p) (V := G ⧸ K) hv
  let Φ : G →+ ZMod p := f.comp (QuotientAddGroup.mk' K)
  have hΦ : Function.Surjective Φ :=
    hf.comp (QuotientAddGroup.mk'_surjective K)
  refine ⟨Φ, hΦ, ?_⟩
  -- every fibre is a translate of the kernel
  have hfib : ∀ a : ZMod p, (univ.filter fun g => Φ g = a).card =
      (univ.filter fun g => Φ g = 0).card := by
    intro a
    obtain ⟨g, hg⟩ := hΦ a
    refine Finset.card_bij (fun x _ => x - g) (fun x hx => ?_) (fun x _ y _ h => ?_)
      (fun y hy => ⟨y + g, ?_, ?_⟩)
    · simp only [mem_filter, mem_univ, true_and] at hx ⊢
      rw [map_sub, hx, hg, sub_self]
    · simpa using h
    · simp only [mem_filter, mem_univ, true_and] at hy ⊢
      rw [map_add, hy, hg, zero_add]
    · simp
  have htot : ∑ a : ZMod p, (univ.filter fun g => Φ g = a).card = Fintype.card G := by
    rw [← Finset.card_univ, ← Finset.card_eq_sum_card_fiberwise (fun g _ => mem_univ (Φ g))]
  simp only [hfib, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, hG] at htot
  intro a
  rw [hfib]
  exact Nat.eq_of_mul_eq_mul_left hp.out.pos htot

/-- **Equation `eq:power_sum_value`.** For `k ≥ 1`, `∑_{α ∈ 𝔽_p} α^k = -1` if `p - 1 ∣ k` and `0` otherwise. -/
theorem sum_zmod_pow (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    ∑ a : ZMod p, a ^ k = if p - 1 ∣ k then -1 else 0 := by
  have h := FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card] at h
  rw [← h]
  have : ∑ a : ZMod p, a ^ k = ∑ a ∈ univ.erase 0, a ^ k := by
    rw [← Finset.add_sum_erase _ _ (mem_univ 0), zero_pow (by omega), zero_add]
  rw [this]
  refine Finset.sum_bij' (fun a ha => Units.mk0 a (by simpa using ha)) (fun u _ => (u : ZMod p))
    ?_ ?_ ?_ ?_ ?_ <;> simp

/-- Evaluating `Q^k_B` at a point of `𝔽_pⁿ`. -/
lemma aeval_qPoly {n p : ℕ} (B : Finset (Fin n → ℤ)) (k : ℕ) (x : Fin n → ZMod p) :
    MvPolynomial.aeval x (qPoly B k) = ∑ b ∈ B, (∑ i, (b i : ZMod p) * x i) ^ (2 * k) := by
  simp [qPoly, map_sum, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]

/-- The system of equations of Lemma 4.2:
`Q^k_{Bⁿ(r)}(x) = 0` for `1 ≤ k < (p-1)/2` and `Q^{(p-1)/2}_{Bⁿ(r)}(x) = -m` in `𝔽_p`. -/
def QSystem (n r m p : ℕ) (x : Fin n → ZMod p) : Prop :=
  (∀ k, 1 ≤ k → k < (p - 1) / 2 → MvPolynomial.aeval x (qPoly (leeBall n r) k) = 0) ∧
    MvPolynomial.aeval x (qPoly (leeBall n r) ((p - 1) / 2)) = -(m : ZMod p)

/-- `x ∈ 𝔽_pⁿ` is a *tiling image*: the multiset `{⟨x, b⟩ : b ∈ Bⁿ(r)}` equals `m·𝔽_p`, i.e. every
element of `𝔽_p` is hit exactly `m` times.  This is the situation `x = Φ ∘ φ(εᵢ)` arising from
a lattice tiling (proof of Lemma 4.2). -/
def IsTilingImage (n r m p : ℕ) (x : Fin n → ZMod p) : Prop :=
  ∀ y : ZMod p, ((leeBall n r).filter fun b => ∑ i, (b i : ZMod p) * x i = y).card = m

/-- A lattice tiling with `|Bⁿ(r)| = m p` yields a tiling image `x = Φ ∘ φ(εᵢ) ∈ 𝔽_pⁿ`. -/
theorem exists_tilingImage_of_tiling {n r m p : ℕ} [hp : Fact p.Prime]
    (hB : (leeBall n r).card = m * p) (ht : HasLatticeTiling (leeBall n r)) :
    ∃ x : Fin n → ZMod p, IsTilingImage n r m p x := by
  classical
  obtain ⟨A, _, _, hcard, φ, hφ⟩ := (hasLatticeTiling_leeBall_iff n r).1 ht
  obtain ⟨Φ, -, hfib⟩ := exists_surj_hom_zmod (G := A) (p := p) (m := m)
    (by rw [hcard, hB, mul_comm])
  let x : Fin n → ZMod p := fun i => Φ (φ (Pi.single i 1))
  have hx : ∀ b : Fin n → ℤ, ∑ i, (b i : ZMod p) * x i = Φ (φ b) := by
    intro b
    conv_rhs => rw [← Finset.univ_sum_single b]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Pi.single i (b i) = b i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j; simp [Pi.single_apply]
    rw [this, map_zsmul, map_zsmul, zsmul_eq_mul]
  refine ⟨x, fun y => ?_⟩
  rw [← hfib y]
  simp only [hx]
  refine Finset.card_bij (fun b _ => φ b) (fun b hb => ?_) (fun a ha b hb h => ?_)
    (fun g hg => ?_)
  · simp only [Finset.mem_filter] at hb ⊢; exact ⟨Finset.mem_univ _, hb.2⟩
  · exact hφ.injOn (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1 h
  · obtain ⟨b, hb, rfl⟩ := hφ.surjOn (Set.mem_univ g)
    exact ⟨b, Finset.mem_filter.2 ⟨hb, (Finset.mem_filter.1 hg).2⟩, rfl⟩

/-- For a tiling image, `∑_{b ∈ Bⁿ(r)} F(⟨x, b⟩) = m ∑_{α ∈ 𝔽_p} F(α)`. -/
lemma IsTilingImage.sum_eq {n r m p : ℕ} [NeZero p] {x : Fin n → ZMod p} (hx : IsTilingImage n r m p x)
    {M : Type*} [AddCommMonoid M] (F : ZMod p → M) :
    ∑ b ∈ leeBall n r, F (∑ i, (b i : ZMod p) * x i) = m • ∑ a : ZMod p, F a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun b => ∑ i, (b i : ZMod p) * x i)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _), Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F a) (fun b hb => by
    rw [(Finset.mem_filter.1 hb).2]), Finset.sum_const, hx a]

/-- A tiling image solves the system of Lemma 4.2. -/
theorem IsTilingImage.qSystem {n r m p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p)
    {x : Fin n → ZMod p} (hx : IsTilingImage n r m p x) : QSystem n r m p x := by
  have key : ∀ j, 1 ≤ j → MvPolynomial.aeval x (qPoly (leeBall n r) j) =
      (m : ZMod p) * (if p - 1 ∣ 2 * j then -1 else 0) := by
    intro j hj
    rw [aeval_qPoly, ← sum_zmod_pow p (by omega : 1 ≤ 2 * j), hx.sum_eq (fun a => a ^ (2 * j)),
      nsmul_eq_mul]
  have hpodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · omega
    · exact h
  refine ⟨fun k hk1 hk2 => ?_, ?_⟩
  · rw [key k hk1, if_neg, mul_zero]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · rw [key _ (by omega), if_pos (by rw [show 2 * ((p - 1) / 2) = p - 1 by omega]), mul_neg,
      mul_one]

/-- A lattice tiling yields a solution of the system of Lemma 4.2. -/
theorem exists_QSystem_of_tiling {n r m p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p) (ht : HasLatticeTiling (leeBall n r)) :
    ∃ x : Fin n → ZMod p, QSystem n r m p x := by
  obtain ⟨x, hx⟩ := exists_tilingImage_of_tiling hB ht
  exact ⟨x, hx.qSystem hp2⟩

/-- **Lemma 4.2.** Let `p > 2` be prime and `|Bⁿ(r)| = m p`.  If there is no `x ∈ 𝔽_pⁿ` with
`Q^k_{Bⁿ(r)}(x) = 0` for `1 ≤ k < (p-1)/2` and `Q^{(p-1)/2}_{Bⁿ(r)}(x) = -m`, then there is no
lattice tiling of `ℤⁿ` by `Bⁿ(r)`. -/
theorem no_tiling_of_no_QSystem {n r m p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p) (h : ¬ ∃ x : Fin n → ZMod p, QSystem n r m p x) :
    ¬ HasLatticeTiling (leeBall n r) :=
  fun ht => h (exists_QSystem_of_tiling hp2 hB ht)

/-- `f_k(Y) = ∑_{λ ⊢ k} c_λ Y_λ` with `Y_λ = Y_{λ₁} ⋯ Y_{λ_ℓ}`, evaluated in `𝔽_p`. -/
def fY (n r p k : ℕ) (Y : ℕ → ZMod p) : ZMod p :=
  ∑ q : k.Partition, (cInt n r q : ZMod p) * (q.parts.map Y).prod

/-- The system of equations of Theorem 4.3:
`f_k(Y) = 0` for `1 ≤ k < (p-1)/2` and `f_{(p-1)/2}(Y) = -m` in `𝔽_p`.  (Only the values
`Y₁, …, Y_{(p-1)/2}` enter.) -/
def YSystem (n r m p : ℕ) (Y : ℕ → ZMod p) : Prop :=
  (∀ k, 1 ≤ k → k < (p - 1) / 2 → fY n r p k Y = 0) ∧ fY n r p ((p - 1) / 2) Y = -(m : ZMod p)

lemma aeval_qPoly_eq_fY {n r p : ℕ} (k : ℕ) (x : Fin n → ZMod p) :
    MvPolynomial.aeval x (qPoly (leeBall n r) k) = fY n r p k (fun j => ∑ i, x i ^ (2 * j)) := by
  rw [qPoly_leeBall_explicit_int, fY, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, MvPolynomial.aeval_C, psumTwo, map_multiset_prod, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [MvPolynomial.psum, map_sum]

/-- A lattice tiling yields a solution of the system of Theorem 4.3. -/
theorem exists_YSystem_of_tiling {n r m p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p) (ht : HasLatticeTiling (leeBall n r)) :
    ∃ Y : ℕ → ZMod p, YSystem n r m p Y := by
  obtain ⟨x, hx1, hx2⟩ := exists_QSystem_of_tiling hp2 hB ht
  refine ⟨fun j => ∑ i, x i ^ (2 * j), fun k hk1 hk2 => ?_, ?_⟩
  · rw [← aeval_qPoly_eq_fY]; exact hx1 k hk1 hk2
  · rw [← aeval_qPoly_eq_fY]; exact hx2

/-- **Theorem 4.3.** Let `p > 2` be prime and `|Bⁿ(r)| = m p`.  If there are no
`Y₁, …, Y_{(p-1)/2} ∈ 𝔽_p` with `∑_{λ ⊢ k} c_λ Y_λ = 0` for `1 ≤ k < (p-1)/2` and
`∑_{λ ⊢ (p-1)/2} c_λ Y_λ = -m`, then there is no lattice tiling of `ℤⁿ` by `Bⁿ(r)`. -/
theorem no_tiling_of_no_YSystem {n r m p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p) (h : ¬ ∃ Y : ℕ → ZMod p, YSystem n r m p Y) :
    ¬ HasLatticeTiling (leeBall n r) :=
  fun ht => h (exists_YSystem_of_tiling hp2 hB ht)

/-! ### Theorem 1.9: the ideal-membership criterion -/

/-- The variable `Y_j` (`1 ≤ j ≤ h`) of `𝔽_p[Y₁, …, Y_h]`, indexed by `Fin h` via `j ↦ j - 1`
(and `0` for indices out of range, which never occur below). -/
noncomputable def yVar (p h : ℕ) (j : ℕ) : MvPolynomial (Fin h) (ZMod p) :=
  if hj : j - 1 < h then MvPolynomial.X ⟨j - 1, hj⟩ else 0

/-- The polynomial `∑_{λ ⊢ k} c_λ Y_λ ∈ 𝔽_p[Y₁, …, Y_h]`. -/
noncomputable def fPoly (n r p h k : ℕ) : MvPolynomial (Fin h) (ZMod p) :=
  ∑ q : k.Partition, MvPolynomial.C (cInt n r q : ZMod p) * (q.parts.map (yVar p h)).prod

lemma eval_fPoly {n r p h k : ℕ} (hk : k ≤ h) (Y : ℕ → ZMod p) :
    MvPolynomial.eval (fun i : Fin h => Y (i + 1)) (fPoly n r p h k) = fY n r p k Y := by
  rw [fPoly, fY, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, MvPolynomial.eval_C, map_multiset_prod, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun j hj => ?_
  have h1 := q.parts_pos hj
  have h2 := q.le_of_mem_parts hj
  simp only [Function.comp_apply, yVar, dif_pos (show j - 1 < h by omega), MvPolynomial.eval_X]
  congr 1; omega

/-- **Theorem 1.9.** Let `p > 2` be prime, `h = (p-1)/2`, and `|Bⁿ(r)| = p m` with `p ∤ m`.  If, in
`𝔽_p[Y₁, …, Y_h]`, the polynomial `∑_{λ ⊢ h} c_λ Y_λ` lies in the ideal generated by
`∑_{λ ⊢ k} c_λ Y_λ` for `1 ≤ k < h`, then there is no lattice tiling of `ℤⁿ` by `Bⁿ(r)`. -/
theorem no_tiling_of_mem_ideal {n r m p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = p * m) (hm : ¬ p ∣ m)
    (hI : fPoly n r p ((p - 1) / 2) ((p - 1) / 2) ∈
      Ideal.span ((fun k => fPoly n r p ((p - 1) / 2) k) '' Set.Ico 1 ((p - 1) / 2))) :
    ¬ HasLatticeTiling (leeBall n r) := by
  intro ht
  obtain ⟨Y, hY1, hY2⟩ := exists_YSystem_of_tiling hp2 (by rw [hB, mul_comm]) ht
  set h := (p - 1) / 2
  let ev := MvPolynomial.eval (R := ZMod p) (fun i : Fin h => Y (i + 1))
  have hle : Ideal.span ((fun k => fPoly n r p h k) '' Set.Ico 1 h) ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    rintro _ ⟨k, ⟨hk1, hk2⟩, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, eval_fPoly hk2.le]
    exact hY1 k hk1 hk2
  have h0 := hle hI
  rw [RingHom.mem_ker, eval_fPoly le_rfl, hY2, neg_eq_zero, ZMod.natCast_eq_zero_iff] at h0
  exact hm h0

/-! ### Theorem 4.1: Qureshi's `p`-condition -/

lemma partition_eq_indiscrete_of_mem {k : ℕ} (q : k.Partition) (hk : k ∈ q.parts) :
    q = Nat.Partition.indiscrete k := by
  have hk0 : k ≠ 0 := fun h => by have := q.parts_pos hk; omega
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hk
  have hsum := q.parts_sum
  rw [hs, Multiset.sum_cons] at hsum
  have hs0 : s = 0 := Multiset.eq_zero_of_forall_notMem fun i hi => by
    have := Multiset.le_sum_of_mem hi
    have := q.parts_pos (hs ▸ Multiset.mem_cons_of_mem hi)
    omega
  ext1
  rw [hs, hs0, Nat.Partition.indiscrete_parts hk0]
  rfl

lemma fY_eq_of_vanish {n r p k : ℕ} (hk : 1 ≤ k) (Y : ℕ → ZMod p)
    (hY : ∀ j, 1 ≤ j → j < k → Y j = 0) :
    fY n r p k Y = (cInt n r (Nat.Partition.indiscrete k) : ZMod p) * Y k := by
  rw [fY, Finset.sum_eq_single (Nat.Partition.indiscrete k)]
  · rw [Nat.Partition.indiscrete_parts (by omega)]; simp
  · intro q _ hq
    have hne : q.parts ≠ 0 := by
      intro h; have := q.parts_sum; rw [h] at this; simp at this; omega
    obtain ⟨j, hj⟩ := Multiset.exists_mem_of_ne_zero hne
    have hjk : j < k := lt_of_le_of_ne (q.le_of_mem_parts hj)
      (fun h => hq (partition_eq_indiscrete_of_mem q (h ▸ hj)))
    rw [Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨j, hj, hY j (q.parts_pos hj) hjk⟩), mul_zero]
  · simp

/-- **Theorem 4.1** (Qureshi's `p`-condition).  Let `p > 2` be prime and `|Bⁿ(r)| = m p` with
`p ∤ m`.  If `c_{(k)} ≢ 0 (mod p)` for `1 ≤ k < (p-1)/2` and `c_{((p-1)/2)} ≡ 0 (mod p)`, then
there is no lattice tiling of `ℤⁿ` by `Bⁿ(r)`. -/
theorem no_tiling_of_p_condition {n r m p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p) (hm : ¬ p ∣ m)
    (hc : ∀ k, 1 ≤ k → k < (p - 1) / 2 →
      (cInt n r (Nat.Partition.indiscrete k) : ZMod p) ≠ 0)
    (hch : (cInt n r (Nat.Partition.indiscrete ((p - 1) / 2)) : ZMod p) = 0) :
    ¬ HasLatticeTiling (leeBall n r) := by
  refine no_tiling_of_no_YSystem hp2 hB ?_
  rintro ⟨Y, hY1, hY2⟩
  have hvan : ∀ k, 1 ≤ k → k < (p - 1) / 2 → Y k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk1 hk2
      have := hY1 k hk1 hk2
      rw [fY_eq_of_vanish hk1 Y fun j hj1 hj2 => ih j hj2 hj1 (by omega)] at this
      exact (mul_eq_zero.1 this).resolve_left (hc k hk1 hk2)
  rw [fY_eq_of_vanish (by omega) Y hvan, hch, zero_mul, eq_comm, neg_eq_zero,
    ZMod.natCast_eq_zero_iff] at hY2
  exact hm hY2

/-- A variant used in Example 4.4: if `c_λ ≡ 0 (mod p)` for every `λ ⊢ (p-1)/2`, then (with
`p ∤ m`) there is no lattice tiling. -/
theorem no_tiling_of_all_c_zero {n r m p : ℕ} [hp : Fact p.Prime] (hp2 : 2 < p)
    (hB : (leeBall n r).card = m * p) (hm : ¬ p ∣ m)
    (hc : ∀ q : ((p - 1) / 2).Partition, (cInt n r q : ZMod p) = 0) :
    ¬ HasLatticeTiling (leeBall n r) := by
  refine no_tiling_of_no_YSystem hp2 hB ?_
  rintro ⟨Y, -, hY2⟩
  rw [fY, Finset.sum_eq_zero fun q _ => by rw [hc q, zero_mul], eq_comm, neg_eq_zero,
    ZMod.natCast_eq_zero_iff] at hY2
  exact hm hY2

end LeeBall
