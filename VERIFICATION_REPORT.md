# Verification report for `main_lee_cayley.tex`

All Lean code is in `RequestProject/LeeBall/`. The whole project builds with `lake build` and contains no
`sorry`, no `axiom` and no `native_decide`. The proved theorems depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. Finite computations are checked by the Lean kernel
(`decide +kernel`).

Statement numbers follow the compiled manuscript (one shared counter per section). Line numbers refer to
`main_lee_cayley.tex`.

## Proved results

| Manuscript | tex line | Lean declaration(s) | File |
|---|---|---|---|
| Lemma 1.3 (Zhang–Zhou, `r = 2`) | 171 | `hasLatticeTiling_leeBall_two_iff` (obtained as the case `r = 2` of Thm 1.8) | `GroupRingApps.lean` |
| Qureshi's formula for `c_{(k)}` (Sec. 1) | 161 | `cInt_indiscrete` | `Section5Examples.lean` |
| Theorem 1.7 (explicit Q-polynomial formula) | 200 | `qPoly_leeBall_explicit`, `qPoly_leeBall_explicit_int`, `cLam_eq_cInt` | `QPoly.lean` |
| Theorem 1.8 (group-ring characterisation) | 216 | `hasLatticeTiling_leeBall_iff_groupRing`, `ball_groupRing_identity`, `sum_leeBall_gpow_eq_grRHS` | `GroupRing.lean`, `GroupRingIdentity.lean` |
| Theorem 1.9 (ideal criterion) | 234 | `no_tiling_of_mem_ideal` | `Ideal.lean` |
| Lemma 2.1 (Horak–AlBdaiwi) | 293 | `hasLatticeTiling_iff_exists_hom` | `Basic.lean` |
| Corollary 2.2 | 297 | `hasLatticeTiling_leeBall_iff` | `Basic.lean` |
| Equation `eq:P2-size_ball` (Stanton–Cowan) | 276 | `card_leeBall`, `card_leeBall_odd` | `Basic.lean` |
| Definitions 2.3, 2.4 | 318, 323 | Mathlib's `MvPolynomial.esymm`, `MvPolynomial.psum` | — |
| Lemma 2.6 | 393 | `exists_surj_hom_zmod` | `Ideal.lean` |
| Theorem 2.7 (a), (b) | 409 | `sum_char_eq_zero`, `fourierUnits_inversion` | `FourierUnits.lean` |
| Equation `eq:power_sum_value` | 420 | `sum_zmod_pow` | `Ideal.lean` |
| Definition 3.1 | 431 | `qPoly` | `QPoly.lean` |
| Theorem 3.2 (Lee spheres) | 468 | `sphereMoment_eq` (with `oneDimQ_eq` for `n = 1`) | `Moments.lean`, `OneDim.lean` |
| Theorem 3.3 (Lee balls) | 537 | `ballMoment_eq` | `Moments.lean` |
| Equation `P5-generate_groupring` | in proof of Thm 5.16 | `sum_partition_pow_length`, `card_leeBall_eq_alt_sum` | `GroupRingApps.lean` |
| Theorem 4.1 (Qureshi's `p`-condition) | 662 | `no_tiling_of_p_condition` | `Ideal.lean` |
| Lemma 4.2 | 675 | `no_tiling_of_no_QSystem`, `exists_QSystem_of_tiling` | `Ideal.lean` |
| Theorem 4.3 | 717 | `no_tiling_of_no_YSystem`, `exists_YSystem_of_tiling` | `Ideal.lean` |
| Example 4.4 (`p = 5`, both sets of conditions) | 778 | `no_tiling_p5`, `no_tiling_of_ex44cond` | `Section4Examples.lean` |
| Corollary 4.5 (`r = 6`) | 837 | `no_tiling_r6` | `Section4Examples.lean` |
| Corollary 4.6 (`r = 7`) | 840 | `no_tiling_r7` | `Section4Examples.lean` |
| Lemma 4.7 (periodicity) | 852 | `binom_sum_periodic` | `Section4Examples.lean` |
| Example 5.2 (`(7,3)`, `p = 23`) | 961 | `no_tiling_7_3`, `forced_value_7_3` | `Section5Examples.lean` |
| Example 5.3 (`(26,3)`, `p = 67`) | 977 | `no_tiling_26_3`, `forced_value_26_3`, `c15_26_3_zero` | `Section5Examples.lean` |
| Lemma 5.4 | 989 | `exists_psum_card_sub_one_eq`, `no_tiling_of_S_pred` | `Section5.lean` |
| Lemma 5.5 | 1019 | `card_leeBall_tauE_le`, `tauE_eq` | `Section5.lean` |
| Newton's identities `eq:Newton` | 1008 | `newton_esymmSq` | `Section5.lean` |
| Example 5.6 (`(79,3)`, `p = 269`) | 1037 | `no_tiling_79_3` (see note 3) | `Section5Examples.lean` |
| Fourier formula `eq:P6-computegi` | 1064 | `count_sq_eq_fourier` | `Section5.lean` |
| Example 5.7 (`(80,3)`, `p = 149`) | 1074 | `no_tiling_80_3`, `forced_value_80_3` | `Section5Examples.lean` |
| Theorem 5.8 | 1096 | `no_tiling_of_sum_gSeq`, `sum_gSeq_val_le` | `Section5.lean` |
| Theorem 5.9 | 1108 | `zeros_S_up`, `no_tiling_of_up` (see note 2) | `Section5UP.lean` |
| Example 5.10 (`(13,3)`, `p = 367`) | 1124 | `no_tiling_13_3`, `forced_value_13_3` (see note 4) | `Section5Examples.lean` |
| Proposition 5.11 | 1190 | `cInt_eq_zero_of_length`, `ySystem_vanish`, `ySystem_reduced`, `card_K_le` | `Section5Prop.lean` |
| Example 5.14 (`(35,3)`, `p = 71` and `p = 29`) | 1321 | `example_35_3_p71`, `example_35_3_p29`, `card_leeBall_35_3` | `GroupRingApps.lean` |
| Theorem 5.15 | 1346 | `uniform_squares_tiling_identity` | `GroupRingApps.lean` |
| Theorem 5.16 | 1381 | `mCp_eq_grRHS` | `GroupRingApps.lean` |
| Remark 5.17 (bad primes) | 1427 | `badSet`, `one_mem_badSet`, `badSet_35_3_29`, `badSet_35_3_71` | `GroupRingApps.lean` |
| Non-computational step in the proof of Thm 5.1 | 1281 | `card_leeBall_mono`, `card_leeBall_13_13`, `card_leeBall_gt_of_ge_13` | `Computational.lean` |

Notes.
1. Theorem 1.8 is stated over the rational group ring `ℚ[G]` (the equation has rational coefficients), and
   `T = T^{(-1)}` is expressed as "closed under inverses".
2. Theorem 5.9: the manuscript derives it from the Feng–Hollmann–Xiang uncertainty principle (Theorem 2.5).
   That general result is not formalized. Instead the special case needed is proved directly, using a
   Vandermonde argument and a double count over cyclic windows. The resulting statement is that of
   Theorem 5.9.
3. Example 5.6: the Lean proof does not compute the entries that depend on the unknown `u`. It checks that every
   `k ≤ 134` with `c_{(k)} ≡ 0 (mod 269)` is a multiple of `20`. Proposition 5.11 then gives `S_{2i} = 0`
   for `20 ∤ i`, and Newton's identities give `e_k(x²) = 0` for `20 ∤ k`. Hence `τ(𝓔_{≤79}) ≥ 19`, and
   Lemma 5.5 with `|B¹⁹(3)| = 9919 > 2491` gives a contradiction.
4. Example 5.10: the manuscript concludes with Theorem 5.9. The Lean proof uses the forced value
   `S_{366} = 103 ∉ {0,…,13}` together with Lemma 5.4. The value `103` and all other values quoted in
   Examples 5.2, 5.3, 5.7 and 5.10 (`11`, `33`, `63`, `103`) are checked by kernel computation.
5. Theorem 1.7 is proved for all `n, k ≥ 0` (the manuscript assumes `n, k ≥ 1`), and Lemma 1.3 for all `n`.

## Statements not proved (positions reported)

### Results resting on the authors' Maple computations

As agreed, these are not proved. Their precise statements are recorded as propositions (`Prop`-valued
definitions) in `Computational.lean`, and nothing in the project depends on them.

| Manuscript | tex line | Lean | Reason |
|---|---|---|---|
| **Theorem 5.1** (no tiling for `n ≥ 3`, `r ≥ 2`, `\|Bⁿ(r)\| < 2³⁰`, except `(35,3)`, `(805,3)`) | 897 (proof at 1268–1284) | `MainComputationalClaim` (statement only) | Algorithm 5.1 was run on 1,358 pairs, plus Table `ta:maxn`. It also relies on the cited Theorem 1.2 (Horak–Kim/Post), the cited Corollary 1.4 and the cited result of Leung–Zhou for `r = 2`. The step for `r ≥ 13`, `n ≥ 13` is proved (`card_leeBall_gt_of_ge_13`). |
| **Proposition 5.12** (`n = 84, 437, 590, 597, 836`, `r = 3`) | 1234 | `Prop512Claim` (statement only) | Exhaustive search. Only the ball size `card_leeBall_84_3` is checked. |
| Example 4.8 (`r = 42`) and Tables `ta:proportion`, `tab:appendix-*` | 872, 245, 1449–1700 | — | Gröbner-basis computations over all `n` in a period, for each `r ≤ 50` and `p < 50`. |
| Example 5.13 (`n = 805`) | 1291 | `card_leeBall_805_3` (ball size only) | Describes a search the authors did not carry out. |
| Table `ta:maxn` and the claim that `(35,3)` is the only pair with all prime factors bad | 1255, 1435 | — | Computational. |

### Cited results whose proofs are not in the manuscript

| Manuscript | tex line | Remark |
|---|---|---|
| Conjecture 1.1 (Golomb–Welch) | 94 | Open conjecture. Not formalized. |
| Theorem 1.2 (Horak–Kim) | 120 | Cited. Not formalized. |
| Corollary 1.4 (Zhang–Zhou, `r = 3`) | 181 | Cited. It rests on the `r = 3` group-ring conditions of another paper. Not formalized. |
| Theorem 1.5 (Leung–Zhou, `r = 2`) | 186 | Cited. Not formalized. |
| Question 1.6 | 191 | A question. It is answered by Theorem 1.8, which is proved. |
| Theorem 2.5 (Feng–Hollmann–Xiang uncertainty principle) | 374 | Cited. The special case used for Theorem 5.9 is proved directly (note 2). |
