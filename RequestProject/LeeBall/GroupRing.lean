module

public import RequestProject.LeeBall.GroupRingIdentity
public import RequestProject.LeeBall.QPoly

/-!
# Theorem 1.8: group-ring characterisation of lattice tilings by Lee balls

We work in the rational group ring `ℚ[G] = MonoidAlgebra ℚ G` of a finite (multiplicatively
written) abelian group `G`.  A subset `T ⊆ G` is identified with `∑_{g ∈ T} g`, and the whole
group `G` with `∑_{g ∈ G} g`.
-/

@[expose] public section

open Finset

namespace LeeBall

variable {G : Type*} [CommGroup G]

local notation "ofG" => MonoidAlgebra.of ℚ G

/-- The group-ring element `∑_{g ∈ S} g`. -/
noncomputable def setElem (S : Finset G) : MonoidAlgebra ℚ G := ∑ g ∈ S, ofG g

/-- The summand `T^{(λ)} / (∏ᵢ λᵢ · ∏_{j=1}^{k} m_λ(j)!)` of Theorem 1.8. -/
noncomputable def grTerm (T : MonoidAlgebra ℚ G) {k : ℕ} (p : k.Partition) :
    MonoidAlgebra ℚ G :=
  (((p.parts.prod : ℕ) : ℚ) * ∏ j ∈ Icc 1 k, ((p.parts.count j).factorial : ℚ))⁻¹ •
    (p.parts.map fun j => pw j T).prod

/-- The right-hand side of the group-ring equation of Theorem 1.8:
`∑_{t=0}^{⌊r/2⌋} (-1)^t C(n,t) ∑_{λ ⊢ r-2t} T^{(λ)} / (∏ᵢ λᵢ ∏ⱼ m_λ(j)!)`. -/
noncomputable def grRHS (n r : ℕ) (T : MonoidAlgebra ℚ G) : MonoidAlgebra ℚ G :=
  ∑ t ∈ range (r / 2 + 1), (((-1) ^ t * n.choose t : ℚ)) •
    ∑ p : (r - 2 * t).Partition, grTerm T p

lemma multiset_prod_map_smul (s : Multiset ℕ) (c : ℕ → ℚ) (f : ℕ → MonoidAlgebra ℚ G) :
    (s.map fun j => c j • f j).prod = (s.map c).prod • (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, smul_mul_smul_comm]; rw [smul_smul, mul_comm]

lemma bellPart_pw (T : MonoidAlgebra ℚ G) (k : ℕ) :
    bellPart (fun j => (j : ℚ)⁻¹ • pw j T) k = ∑ p : k.Partition, grTerm T p := by
  unfold bellPart
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bellTerm, grTerm, multiset_prod_map_smul, smul_smul, ← multFact_eq_prod_Icc,
    Multiset.prod_map_inv, mul_inv, mul_comm]
  congr 3
  rw [Nat.cast_multiset_prod]

lemma pw_one (A : MonoidAlgebra ℚ G) : pw 1 A = A := by
  simp only [pw, pow_one]; exact Finsupp.mapDomain_id

lemma bellPart_one {R : Type*} [CommRing R] [Algebra ℚ R] (y : ℕ → R) : bellPart y 1 = y 1 := by
  have := bellPart_rec y 1
  simpa [bellPart_zero] using this

/-- The group-ring identity, written with `grRHS`. -/
theorem sum_leeBall_gpow_eq_grRHS {n : ℕ} (x : Fin n → G) (r : ℕ) :
    ∑ b ∈ leeBall n r, ofG (gpow x b) = grRHS n r (tElem x) := by
  rw [ball_groupRing_identity, grRHS]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bellPart_pw, Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast]

/-- `∑_{b ∈ Bⁿ(1)} x^b = T`. -/
lemma sum_leeBall_one_gpow {n : ℕ} (x : Fin n → G) :
    ∑ b ∈ leeBall n 1, ofG (gpow x b) = tElem x := by
  rw [ball_groupRing_identity]
  simp [bellPart_one, pw_one]

/-- If `∑_{b ∈ B} f(b) = ∑_{g ∈ G} g` in `ℚ[G]`, then `f` is a bijection from `B` onto `G`. -/
lemma bijOn_of_sum_eq [Fintype G] {ι : Type*} (B : Finset ι) (f : ι → G)
    (h : ∑ b ∈ B, ofG (f b) = setElem (univ : Finset G)) : Set.BijOn f B Set.univ := by
  classical
  have hcount : ∀ g : G, (B.filter fun b => f b = g).card = 1 := by
    intro g
    have := congrArg (fun A : MonoidAlgebra ℚ G => A g) h
    simp only [setElem, MonoidAlgebra.of_apply] at this
    rw [Finsupp.finset_sum_apply, Finsupp.finset_sum_apply] at this
    simp [MonoidAlgebra.single_apply] at this
    exact_mod_cast this
  refine ⟨fun b _ => Set.mem_univ _, fun a ha b hb hab => ?_, fun g _ => ?_⟩
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (hcount (f a))
    have h1 : a ∈ B.filter fun b => f b = f a := by simp [show a ∈ B from ha]
    have h2 : b ∈ B.filter fun b' => f b' = f a := by simp [show b ∈ B from hb, hab.symm]
    rw [hc] at h1 h2
    simp only [mem_singleton] at h1 h2
    rw [h1, h2]
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (hcount g)
    have : c ∈ B.filter fun b => f b = g := by rw [hc]; simp
    simp only [mem_filter] at this
    exact ⟨c, this.1, this.2⟩

lemma gpow_zero {n : ℕ} (x : Fin n → G) : gpow x 0 = 1 := by simp [gpow]

lemma gpow_add {n : ℕ} (x : Fin n → G) (a b : Fin n → ℤ) :
    gpow x (a + b) = gpow x a * gpow x b := by
  simp [gpow, zpow_add, Finset.prod_mul_distrib]

lemma gpow_neg {n : ℕ} (x : Fin n → G) (b : Fin n → ℤ) : gpow x (-b) = (gpow x b)⁻¹ := by
  simp [gpow, zpow_neg, Finset.prod_inv_distrib]

/-- In a group of odd order there are no involutions. -/
lemma inv_ne_self_of_odd [Fintype G] (hodd : Odd (Fintype.card G)) {g : G} (hg : g ≠ 1) :
    g⁻¹ ≠ g := by
  intro h
  have h2 : g ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← h]; exact inv_mul_cancel g
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hc : orderOf g ∣ Fintype.card G := orderOf_dvd_card
  have : orderOf g ∣ Nat.gcd 2 (Fintype.card G) := Nat.dvd_gcd hd hc
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), Nat.dvd_one, orderOf_eq_one_iff]
    at this
  exact hg this

/-- An inverse-closed subset `T ∋ e` of size `2n+1` of a group of odd order has the form
`{e, x₁, x₁⁻¹, …, xₙ, xₙ⁻¹}`. -/
lemma exists_tElem_eq [Fintype G] (hodd : Odd (Fintype.card G)) {n : ℕ} (T : Finset G)
    (hT1 : (1 : G) ∈ T) (hTinv : ∀ g ∈ T, g⁻¹ ∈ T) (hcard : T.card = 2 * n + 1) :
    ∃ x : Fin n → G, setElem T = tElem x := by
  classical
  let e := Fintype.equivFin G
  let R := (T.erase 1).filter fun g => e g < e g⁻¹
  have hdisj : Disjoint R (R.image fun g => g⁻¹) := by
    rw [Finset.disjoint_left]
    intro g hg hg'
    simp only [R, Finset.mem_image, Finset.mem_filter] at hg hg'
    obtain ⟨h, ⟨_, hh⟩, rfl⟩ := hg'
    rw [inv_inv] at hg
    exact absurd (hg.2.trans hh) (lt_irrefl _)
  have hunion : T.erase 1 = R ∪ R.image fun g => g⁻¹ := by
    ext g
    simp only [R, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hg1, hgT⟩
      have hne : e g ≠ e g⁻¹ := fun h => inv_ne_self_of_odd hodd hg1 (e.injective h).symm
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨⟨hg1, hgT⟩, h⟩
      · refine Or.inr ⟨g⁻¹, ⟨⟨inv_ne_one.2 hg1, hTinv g hgT⟩, ?_⟩, inv_inv g⟩
        rwa [inv_inv]
    · rintro (⟨h, _⟩ | ⟨h, ⟨⟨h1, hT⟩, _⟩, rfl⟩)
      · exact h
      · exact ⟨inv_ne_one.2 h1, hTinv h hT⟩
  have hinj : Set.InjOn (fun g : G => g⁻¹) R := fun a _ b _ h => inv_injective h
  have hRcard : R.card = n := by
    have h := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj,
      Finset.card_erase_of_mem hT1, hcard] at h
    omega
  let eR : R ≃ Fin n := Finset.equivFinOfCardEq hRcard
  refine ⟨fun i => (eR.symm i).1, ?_⟩
  rw [setElem, ← Finset.add_sum_erase _ _ hT1, hunion, Finset.sum_union hdisj,
    Finset.sum_image hinj, ← Finset.sum_add_distrib, tElem]
  congr 1
  rw [← Finset.sum_coe_sort R]
  exact (Equiv.sum_comp eR.symm (fun g : R => ofG g.1 + ofG (g.1)⁻¹)).symm

/-- **Theorem 1.8.** Let `r ≥ 1`.  There is a lattice tiling of `ℤⁿ` by `Bⁿ(r)` iff there are a
finite abelian group `G` of order `|Bⁿ(r)|` and a subset `T ⊆ G` with `|T| = 2n+1` such that
`e ∈ T`, `T = T^{(-1)}` and, in the group ring,
`G = ∑_{t=0}^{⌊r/2⌋} (-1)^t C(n,t) ∑_{λ ⊢ r-2t} T^{(λ)} / (∏ᵢ λᵢ ∏ⱼ m_λ(j)!)`.

The group ring is taken with rational coefficients (the equation has rational coefficients);
`T = T^{(-1)}` is expressed as `∀ g ∈ T, g⁻¹ ∈ T`. -/
theorem hasLatticeTiling_leeBall_iff_groupRing (n r : ℕ) (hr : 1 ≤ r) :
    HasLatticeTiling (leeBall n r) ↔
      ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G),
        Fintype.card G = (leeBall n r).card ∧
        ∃ T : Finset G, T.card = 2 * n + 1 ∧ (1 : G) ∈ T ∧ (∀ g ∈ T, g⁻¹ ∈ T) ∧
          setElem (univ : Finset G) = grRHS n r (setElem T) := by
  classical
  rw [hasLatticeTiling_leeBall_iff]
  constructor
  · rintro ⟨A, _, _, hcard, φ, hφ⟩
    let x : Fin n → Multiplicative A := fun i => Multiplicative.ofAdd (φ (Pi.single i 1))
    have hx : ∀ b, gpow x b = Multiplicative.ofAdd (φ b) := by
      intro b
      simp only [gpow, x]
      conv_rhs => rw [← Finset.univ_sum_single b]
      rw [map_sum, ofAdd_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← ofAdd_zsmul, ← map_zsmul]; congr 2; ext j; simp [Pi.single_apply]
    have hsub : leeBall n 1 ⊆ leeBall n r := fun b hb => by
      simp only [mem_leeBall] at hb ⊢; omega
    have hinj1 : Set.InjOn (gpow x) (leeBall n 1) := by
      intro a ha b hb hab
      rw [hx, hx] at hab
      exact hφ.injOn (hsub ha) (hsub hb) (Multiplicative.ofAdd.injective hab)
    refine ⟨Multiplicative A, inferInstance, inferInstance, by simpa using hcard,
      (leeBall n 1).image (gpow x), ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj1, card_leeBall]
      rw [stantonCowan_eq_range]; simp [Finset.sum_range_succ]; ring
    · exact Finset.mem_image.2 ⟨0, zero_mem_leeBall n 1, gpow_zero x⟩
    · intro g hg
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hg
      refine Finset.mem_image.2 ⟨-b, ?_, gpow_neg x b⟩
      simpa [mem_leeBall, leeNorm_neg] using hb
    · rw [show setElem ((leeBall n 1).image (gpow x)) = tElem x by
        rw [setElem, Finset.sum_image hinj1, sum_leeBall_one_gpow],
        ← sum_leeBall_gpow_eq_grRHS, setElem]
      symm
      refine Finset.sum_nbij (gpow x) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
      · intro a ha b hb hab
        rw [hx, hx] at hab
        exact hφ.injOn ha hb (Multiplicative.ofAdd.injective hab)
      · intro g _
        obtain ⟨b, hb, hbg⟩ := hφ.surjOn (Set.mem_univ (Multiplicative.toAdd g))
        exact ⟨b, hb, by rw [hx, hbg]; rfl⟩
  · rintro ⟨G, _, _, hcard, T, hTcard, hT1, hTinv, heq⟩
    have hodd : Odd (Fintype.card G) := by rw [hcard]; exact card_leeBall_odd n r
    obtain ⟨x, hx⟩ := exists_tElem_eq hodd T hT1 hTinv hTcard
    have hsum : ∑ b ∈ leeBall n r, MonoidAlgebra.of ℚ G (gpow x b) = setElem (univ : Finset G) := by
      rw [sum_leeBall_gpow_eq_grRHS, ← hx, heq]
    have hbij := bijOn_of_sum_eq _ _ hsum
    let φ : (Fin n → ℤ) →+ Additive G :=
      { toFun := fun b => Additive.ofMul (gpow x b)
        map_zero' := by simp [gpow_zero]
        map_add' := fun a b => by simp [gpow_add] }
    refine ⟨Additive G, inferInstance, inferInstance, by simpa using hcard, φ, ?_⟩
    refine ⟨fun _ _ => Set.mem_univ _, fun a ha b hb hab => hbij.injOn ha hb
      (Additive.ofMul.injective hab), fun g _ => ?_⟩
    obtain ⟨b, hb, hbg⟩ := hbij.surjOn (Set.mem_univ (Additive.toMul g))
    exact ⟨b, hb, by simp [φ, hbg]⟩

end LeeBall
