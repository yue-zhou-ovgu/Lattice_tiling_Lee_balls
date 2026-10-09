module

public import Mathlib

/-!
# Lee balls, Lee spheres and lattice tilings

Basic definitions of the manuscript (Section 1 and Section 2.1):

* the Lee (ℓ¹) norm on `ℤⁿ`, the Lee ball `Bⁿ(r)` and the Lee sphere `Sⁿ(r)`;
* lattice tilings of `ℤⁿ` by a finite set;
* the homomorphism criterion of Horak–AlBdaiwi (Lemma 2.1 / Corollary 2.2);
* the size formula of Stanton–Cowan (equation `eq:P2-size_ball`) and the oddness of `|Bⁿ(r)|`.
-/

@[expose] public section

open Finset

namespace LeeBall

/-- The Lee (Manhattan, ℓ¹) norm `∑ᵢ |bᵢ|` of a vector of `ℤⁿ`. -/
def leeNorm {n : ℕ} (b : Fin n → ℤ) : ℕ := ∑ i, (b i).natAbs

/-- The Lee ball `Bⁿ(r) = {x ∈ ℤⁿ : ∑ᵢ |xᵢ| ≤ r}`. -/
def leeBall (n r : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r).filter fun b => leeNorm b ≤ r

/-- The Lee sphere `Sⁿ(r) = {x ∈ ℤⁿ : ∑ᵢ |xᵢ| = r}`. -/
def leeSphere (n r : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(r : ℤ)) r).filter fun b => leeNorm b = r

lemma natAbs_le_leeNorm {n : ℕ} (b : Fin n → ℤ) (i : Fin n) : (b i).natAbs ≤ leeNorm b :=
  Finset.single_le_sum (f := fun i => (b i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

@[simp] lemma mem_leeBall {n r : ℕ} {b : Fin n → ℤ} : b ∈ leeBall n r ↔ leeNorm b ≤ r := by
  unfold leeBall
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
  intro h i
  have := (natAbs_le_leeNorm b i).trans h
  omega

@[simp] lemma mem_leeSphere {n r : ℕ} {b : Fin n → ℤ} : b ∈ leeSphere n r ↔ leeNorm b = r := by
  unfold leeSphere
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
  intro h i
  have := (natAbs_le_leeNorm b i).trans h.le
  omega

lemma leeNorm_cons {n : ℕ} (a : ℤ) (b : Fin n → ℤ) :
    leeNorm (Fin.cons a b : Fin (n + 1) → ℤ) = a.natAbs + leeNorm b := by
  simp [leeNorm, Fin.sum_univ_succ]

lemma leeNorm_neg {n : ℕ} (b : Fin n → ℤ) : leeNorm (-b) = leeNorm b := by
  simp [leeNorm]

@[simp] lemma leeNorm_zero {n : ℕ} : leeNorm (0 : Fin n → ℤ) = 0 := by simp [leeNorm]

lemma leeNorm_eq_zero {n : ℕ} {b : Fin n → ℤ} : leeNorm b = 0 ↔ b = 0 := by
  constructor
  · intro h; funext i
    have := natAbs_le_leeNorm b i
    simp only [Pi.zero_apply]; omega
  · rintro rfl; simp

lemma zero_mem_leeBall (n r : ℕ) : (0 : Fin n → ℤ) ∈ leeBall n r := by simp

lemma leeSphere_zero (n : ℕ) : leeSphere n 0 = {0} := by
  ext b; simp [leeNorm_eq_zero]

lemma leeSphere_dim_zero (r : ℕ) : leeSphere 0 r = if r = 0 then {0} else ∅ := by
  ext b
  have : leeNorm b = 0 := by simp [leeNorm]
  split_ifs with h <;> simp [this, h, eq_comm]
  · exact Subsingleton.elim _ _

/-- Decomposition of a sum over `S^{n+1}(r)` according to the first coordinate. -/
lemma sum_leeSphere_succ {M : Type*} [AddCommMonoid M] (n r : ℕ) (F : (Fin (n + 1) → ℤ) → M) :
    ∑ b ∈ leeSphere (n + 1) r, F b =
      ∑ a ∈ Finset.Icc (-(r : ℤ)) r, ∑ b ∈ leeSphere n (r - a.natAbs), F (Fin.cons a b) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun b _ => ⟨b 0, Fin.tail b⟩) (fun x _ => Fin.cons x.1 x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rw [mem_leeSphere] at hb
    have h0 := natAbs_le_leeNorm b 0
    have hc : leeNorm b = (b 0).natAbs + leeNorm (Fin.tail b) := by
      rw [← leeNorm_cons, Fin.cons_self_tail]
    simp only [Finset.mem_sigma, Finset.mem_Icc, mem_leeSphere]
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, mem_leeSphere] at h ⊢
    rw [leeNorm_cons]; omega
  · intro b _; simp
  · rintro ⟨a, b⟩ _; simp
  · intro b _; simp

/-- Decomposition of a sum over `B^{n+1}(r)` according to the first coordinate. -/
lemma sum_leeBall_succ {M : Type*} [AddCommMonoid M] (n r : ℕ) (F : (Fin (n + 1) → ℤ) → M) :
    ∑ b ∈ leeBall (n + 1) r, F b =
      ∑ a ∈ Finset.Icc (-(r : ℤ)) r, ∑ b ∈ leeBall n (r - a.natAbs), F (Fin.cons a b) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun b _ => ⟨b 0, Fin.tail b⟩) (fun x _ => Fin.cons x.1 x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro b hb
    rw [mem_leeBall] at hb
    have h0 := natAbs_le_leeNorm b 0
    have hc : leeNorm b = (b 0).natAbs + leeNorm (Fin.tail b) := by
      rw [← leeNorm_cons, Fin.cons_self_tail]
    simp only [Finset.mem_sigma, Finset.mem_Icc, mem_leeBall]
    omega
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_sigma, Finset.mem_Icc, mem_leeBall] at h ⊢
    rw [leeNorm_cons]; omega
  · intro b _; simp
  · rintro ⟨a, b⟩ _; simp
  · intro b _; simp

/-- A sum over the Lee ball is the sum of the sums over the Lee spheres `Sⁿ(j)`, `j ≤ r`. -/
lemma sum_leeBall_eq_sum_leeSphere {M : Type*} [AddCommMonoid M] (n r : ℕ)
    (F : (Fin n → ℤ) → M) :
    ∑ b ∈ leeBall n r, F b = ∑ j ∈ Finset.range (r + 1), ∑ b ∈ leeSphere n j, F b := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := leeNorm) (t := Finset.range (r + 1))]
  · refine Finset.sum_congr rfl fun j hj => Finset.sum_congr ?_ fun _ _ => rfl
    ext b
    simp only [Finset.mem_filter, mem_leeBall, mem_leeSphere, Finset.mem_range] at hj ⊢
    omega
  · intro b hb; simp only [mem_leeBall] at hb; simp only [Finset.mem_range]; omega

/-- Folding a symmetric sum over `[-r, r]` onto `[0, r]`. -/
lemma sum_Icc_natAbs {M : Type*} [AddCommMonoid M] (r : ℕ) (g : ℕ → M) :
    ∑ a ∈ Finset.Icc (-(r : ℤ)) r, g a.natAbs =
      g 0 + ∑ t ∈ Finset.Icc 1 r, (g t + g t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hI : Finset.Icc (-((r + 1 : ℕ) : ℤ)) ((r + 1 : ℕ) : ℤ) =
        insert ((r + 1 : ℕ) : ℤ) (insert (-((r + 1 : ℕ) : ℤ)) (Finset.Icc (-(r : ℤ)) r)) := by
      ext a; simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
    rw [hI, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_Icc_succ_top (by omega)]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    abel

/-! ### Lattice tilings -/

/-- `L` is a lattice tiling of `ℤⁿ` by the finite set `S`: the translates `S + c` (`c ∈ L`)
partition `ℤⁿ`, i.e. every `z ∈ ℤⁿ` is uniquely of the form `b + c` with `b ∈ S`, `c ∈ L`. -/
def IsLatticeTiling {n : ℕ} (S : Finset (Fin n → ℤ)) (L : AddSubgroup (Fin n → ℤ)) : Prop :=
  ∀ z : Fin n → ℤ, ∃! bc : (Fin n → ℤ) × (Fin n → ℤ), bc.1 ∈ S ∧ bc.2 ∈ L ∧ bc.1 + bc.2 = z

/-- There exists a lattice tiling of `ℤⁿ` by `S`. -/
def HasLatticeTiling {n : ℕ} (S : Finset (Fin n → ℤ)) : Prop :=
  ∃ L : AddSubgroup (Fin n → ℤ), IsLatticeTiling S L

/-- **Lemma 2.1** (Horak–AlBdaiwi). There is a lattice tiling of `ℤⁿ` by a finite set `S` iff
there is an abelian group `G` of order `|S|` and a homomorphism `ℤⁿ → G` that is bijective on
`S`. -/
theorem hasLatticeTiling_iff_exists_hom {n : ℕ} (S : Finset (Fin n → ℤ)) :
    HasLatticeTiling S ↔ ∃ (G : Type) (_ : AddCommGroup G) (_ : Fintype G),
      Fintype.card G = S.card ∧ ∃ φ : (Fin n → ℤ) →+ G, Set.BijOn φ S Set.univ := by
  constructor
  · rintro ⟨L, hL⟩
    let G := (Fin n → ℤ) ⧸ L
    let φ : (Fin n → ℤ) →+ G := QuotientAddGroup.mk' L
    have hbij : Set.BijOn φ S Set.univ := by
      refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
      · intro b hb b' hb' h
        have h' : -b + b' ∈ L := (QuotientAddGroup.eq).1 h
        obtain ⟨bc, -, huniq⟩ := hL b'
        have e1 := huniq ⟨b', 0⟩ ⟨hb', L.zero_mem, by simp⟩
        have e2 := huniq ⟨b, -b + b'⟩ ⟨hb, h', by simp⟩
        have := e1.trans e2.symm
        exact (congrArg Prod.fst this).symm
      · intro g _
        obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective g
        obtain ⟨⟨b, c⟩, ⟨hb, hc, hbc⟩, -⟩ := hL z
        refine ⟨b, hb, ?_⟩
        show (QuotientAddGroup.mk b : G) = QuotientAddGroup.mk z
        rw [QuotientAddGroup.eq]
        simp only at hbc
        rw [← hbc]; simpa using hc
    have hfin : Finite G := by
      have : Set.univ ⊆ φ '' (S : Set (Fin n → ℤ)) := hbij.image_eq.symm.subset
      exact Set.finite_univ_iff.1 ((S.finite_toSet.image φ).subset this)
    letI : Fintype G := Fintype.ofFinite G
    refine ⟨G, inferInstance, this, ?_, φ, hbij⟩
    classical
    have h1 : S.image φ = Finset.univ := by
      ext g; simp only [Finset.mem_image, Finset.mem_univ, iff_true]
      obtain ⟨b, hb, h⟩ := hbij.surjOn (Set.mem_univ g)
      exact ⟨b, hb, h⟩
    rw [← Finset.card_univ, ← h1, Finset.card_image_of_injOn hbij.injOn]
  · rintro ⟨G, _, _, -, φ, hbij⟩
    refine ⟨φ.ker, fun z => ?_⟩
    obtain ⟨b, hb, hbz⟩ := hbij.surjOn (Set.mem_univ (φ z))
    refine ⟨⟨b, z - b⟩, ⟨hb, ?_, by simp⟩, ?_⟩
    · simp [AddMonoidHom.mem_ker, map_sub, hbz]
    · rintro ⟨b', c'⟩ ⟨hb', hc', hbc'⟩
      simp only at hb' hc' hbc'
      have : φ b' = φ b := by
        rw [hbz, ← hbc', map_add, (AddMonoidHom.mem_ker).1 hc', add_zero]
      have := hbij.injOn hb' hb this
      subst this
      ext1
      · rfl
      · simp only; rw [← hbc']; abel

/-- **Corollary 2.2**. There is a lattice tiling of `ℤⁿ` by `Bⁿ(r)` iff there is an abelian
group `G` of order `|Bⁿ(r)|` and a homomorphism `ℤⁿ → G` bijective on `Bⁿ(r)`. -/
theorem hasLatticeTiling_leeBall_iff (n r : ℕ) :
    HasLatticeTiling (leeBall n r) ↔ ∃ (G : Type) (_ : AddCommGroup G) (_ : Fintype G),
      Fintype.card G = (leeBall n r).card ∧
        ∃ φ : (Fin n → ℤ) →+ G, Set.BijOn φ (leeBall n r) Set.univ :=
  hasLatticeTiling_iff_exists_hom _

/-! ### The size of a Lee ball -/

/-- The Stanton–Cowan number `∑_{i=0}^{min(n,r)} 2ⁱ C(n,i) C(r,i)`. -/
def stantonCowan (n r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (min n r + 1), 2 ^ i * n.choose i * r.choose i

lemma stantonCowan_eq_range (n r : ℕ) :
    stantonCowan n r = ∑ i ∈ Finset.range (r + 1), 2 ^ i * n.choose i * r.choose i := by
  unfold stantonCowan
  refine Finset.sum_subset (by intro i; simp only [Finset.mem_range]; omega) fun i hi hi' => ?_
  simp only [Finset.mem_range] at hi hi'
  rcases le_total n r with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < i)]; simp
  · omega

lemma sum_Icc_sub_eq_sum_range {M : Type*} [AddCommMonoid M] (r : ℕ) (f : ℕ → M) :
    ∑ t ∈ Finset.Icc 1 r, f (r - t) = ∑ m ∈ Finset.range r, f m := by
  refine Finset.sum_nbij' (fun t => r - t) (fun m => r - m) ?_ ?_ ?_ ?_ ?_
  · intro t ht; simp only [Finset.mem_Icc] at ht; simp; omega
  · intro m hm; simp only [Finset.mem_range] at hm; simp; omega
  · intro t ht; simp only [Finset.mem_Icc] at ht; dsimp only; omega
  · intro m hm; simp only [Finset.mem_range] at hm; dsimp only; omega
  · intro t _; rfl

lemma card_leeBall_succ (n r : ℕ) :
    (leeBall (n + 1) r).card =
      (leeBall n r).card + ∑ m ∈ Finset.range r, 2 * (leeBall n m).card := by
  have h := sum_leeBall_succ n r (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h]
  rw [sum_Icc_natAbs r (fun t => (leeBall n (r - t)).card), Nat.sub_zero]
  rw [← sum_Icc_sub_eq_sum_range r (fun m => 2 * (leeBall n m).card)]
  simp [two_mul]

lemma card_leeBall_zero_dim (r : ℕ) : (leeBall 0 r).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext b; simp [leeNorm, Subsingleton.elim b 0]

/-- Hockey-stick identity. -/
lemma sum_range_choose' (r i : ℕ) : ∑ m ∈ Finset.range r, m.choose i = r.choose (i + 1) := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ, add_comm]

lemma stantonCowan_eq_range_of_le (n r R : ℕ) (h : r ≤ R) :
    stantonCowan n r = ∑ i ∈ Finset.range (R + 1), 2 ^ i * n.choose i * r.choose i := by
  rw [stantonCowan_eq_range]
  refine Finset.sum_subset (by intro i; simp; omega) fun i hi hi' => ?_
  simp only [Finset.mem_range] at hi hi'
  rw [Nat.choose_eq_zero_of_lt (by omega : r < i)]; simp

/-- **Equation `eq:P2-size_ball`** (Stanton–Cowan). `|Bⁿ(r)| = ∑_{i=0}^{min(n,r)} 2ⁱ C(n,i) C(r,i)`. -/
theorem card_leeBall (n r : ℕ) : (leeBall n r).card = stantonCowan n r := by
  induction n generalizing r with
  | zero =>
    rw [card_leeBall_zero_dim]; simp [stantonCowan]
  | succ n ih =>
    rw [card_leeBall_succ, ih]
    simp_rw [ih]
    have h2 : ∑ m ∈ Finset.range r, 2 * stantonCowan n m =
        ∑ i ∈ Finset.range (r + 1), 2 ^ (i + 1) * n.choose i * r.choose (i + 1) := by
      rw [Finset.sum_congr rfl fun m hm => by
        rw [stantonCowan_eq_range_of_le n m r (Finset.mem_range.1 hm).le]]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sum_range_choose', Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [h2, stantonCowan_eq_range, stantonCowan_eq_range, Finset.sum_range_succ' (fun i =>
      2 ^ i * (n + 1).choose i * r.choose i)]
    simp_rw [Nat.choose_succ_succ']
    rw [Finset.sum_range_succ (fun i => 2 ^ (i + 1) * n.choose i * r.choose (i + 1)),
      Nat.choose_succ_self, mul_zero, add_zero, Finset.sum_range_succ' (fun i =>
      2 ^ i * n.choose i * r.choose i)]
    simp only [pow_zero, Nat.choose_zero_right, mul_one, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring

/-- The size of a Lee ball is odd. -/
theorem card_leeBall_odd (n r : ℕ) : Odd (leeBall n r).card := by
  rw [card_leeBall, stantonCowan_eq_range, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, mul_one]
  refine Even.add_one (Finset.even_sum _ fun i _ => ?_)
  exact ((Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _).mul_right _

end LeeBall
