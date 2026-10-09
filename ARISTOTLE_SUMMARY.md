# Summary of changes for run e5c26a2c-3d42-4b8a-886b-1aa425f5f55f
I drafted the remark and saved it as `LEAN_REMARK.tex`, ready to paste into `main_lee_cayley.tex`. I did not edit the manuscript itself.

**What the file contains**
- **Version A (detailed):** a `rem` environment titled "Formal verification". It says the proofs were formalized in Lean 4 (version 4.28.0) with Mathlib, with the help of Aristotle by Harmonic. It says every proof is checked by the Lean kernel, with no `sorry`, no new axioms and only Lean's standard axioms, and that the finite computations in the examples are also checked inside Lean. It then:
  - lists the formalized results;
  - names the three places where the formal proof takes a different route from the paper: Theorem 5.9 by a direct Vandermonde argument instead of Theorem 2.5, Example 5.6 and Example 5.10;
  - lists what was not formalized. That is the Maple-based results (Theorem 5.1, Proposition 5.12, Examples 4.8 and 5.13, the tables) and the results quoted from other papers. It also notes that the statements of Theorem 5.1 and Proposition 5.12 are written in Lean but not proved, and that the step \(|B^n(r)|>2^{30}\) for \(n,r\ge 13\) is proved.
- **Version B (short):** one paragraph with the same claims in less detail.
- **Three `\bibitem` entries** for Lean 4 (de Moura–Ullrich, CADE 2021), Mathlib (CPP 2020) and Aristotle (website). Add them to your bibliography.

I suggest putting it at the end of "Concluding Remarks", just before the Acknowledgment.

**Checks behind the wording**
- The project builds again with `lake build`.
- There are no `sorry`, `axiom` or `native_decide` in the Lean code.
- I printed the axioms for 15 of the main results, including Theorems 1.7–1.9, 5.9, 5.15 and 5.16 and Examples 5.6, 5.7 and 5.10. They depend only on `propext`, `Classical.choice` and `Quot.sound`.
- The text cross-references your paper using its existing labels, and I checked that every label it uses exists in the manuscript.
- There is no LaTeX compiler here, so I could not compile the remark.

**Things to do before you submit**
1. Replace `<REPOSITORY-URL>` with a permanent public location for the Lean code, such as GitHub or a Zenodo DOI.
2. Keep the sentence "The authors have checked that the formal statements agree with the statements in the paper" only if you have actually read the Lean statements against the paper. Lean checks the proofs, but whether each statement matches the paper's wording is a human judgment. `VERIFICATION_REPORT.md` maps each result to its Lean declaration to help with this.
3. Six statements have no `\label` in the manuscript: Conjecture 1.1, Theorem 1.5, Lemma 2.1, and Examples 4.8, 5.6 and 5.10. Their numbers are typed by hand and marked `% no label`. Either add labels to them or update these numbers if the numbering changes.
4. Many journals require a separate declaration on the use of AI tools. Check your journal's policy; the remark may need to go there too, or instead.

# Summary of changes for run 1e62039c-c38e-404a-b78a-70fc3c0242c6
The "numbering corrections" in the earlier summary were changes to the comments in the Lean files, not to your manuscript. Earlier Lean comments had cited some results under the wrong numbers, and those comments were changed to match the numbers your compiled paper actually shows. Your `.tex` file was not edited.

I also rechecked the numbering in `main_lee_cayley.tex`. Theorems, lemmas, corollaries, remarks, definitions, propositions, examples, conjectures and questions all share one counter per section (lines 29–38). I found no numbering errors in the manuscript.

These are the statements whose numbers were fixed in the Lean comments, with the line in `main_lee_cayley.tex` where each starts:

| Statement (compiled number) | Label | Line in `.tex` |
|---|---|---|
| Lemma 1.3 | `lem:P5-groupring_r2` | 171 |
| Theorem 1.7 | `thm:P3-Q-poly_explicit_formula` | 200 |
| Theorem 1.8 | `thm:P5-groupring` | 216 |
| Theorem 1.9 | `thm:P4-ideal` | 234 |
| Lemma 2.6 | `lem:P2-m_to_1` | 393 |
| Lemma 5.5 | `lem:P6-overzeros` | 1019 |
| Proposition 5.11 | `pro-P6:S_{2k}` | 1190 |
| Proposition 5.12 | `prop:(84,3)` | 1234 |
| Theorem 5.15 | `thm:P6-mCp=f(T)add` | 1346 |
| Theorem 5.16 | `thm:P6-mCp=f(T)mul` | 1381 |
| Remark 5.17 | `rem:badprimes` | 1427 |

The Lean comments also used to give equation numbers. They now cite equations by your LaTeX labels instead:
- `eq:P2-size_ball`: line 276
- `eq:P3-cor_Q-poly_explicit_formula`: line 202
- `eq:power_sum_value`: line 420
- `eq:Newton`: line 1008

A full map from every statement to its line in the `.tex` file and its Lean declaration is in `VERIFICATION_REPORT.md`.

No files were changed this time and no Lean code was rebuilt, since this was only a question about the earlier work.

# Summary of changes for run 964ed7cc-ef32-47f0-903b-39d81256f95c
I continued the formalization of the manuscript (`main_lee_cayley.tex`). The whole project builds with `lake build` and contains no `sorry`, no new axioms and no `native_decide`. The main theorems depend only on the standard axioms (checked with `#print axioms`), and the finite computations are checked by the Lean kernel.

**Added in this session**
- **Qureshi's formula** \(c_{(k)} = 2\sum_{i=0}^{r}(r-i)^{2k-1}|B^n(i)|\), derived from Theorem 1.7 (`cInt_indiscrete`).
- **Two general nonexistence criteria**, each combining Proposition 5.11 with another result:
  - with Lemma 5.4 (`no_tiling_of_last_forced`, `no_tiling_of_qureshi`);
  - with Theorem 5.8, for the case of one undetermined entry (`no_tiling_of_one_unknown`).
- **Section 5 examples, now fully proved:**
  - Example 5.2: no tiling for \((7,3)\).
  - Example 5.3: no tiling for \((26,3)\).
  - Example 5.6: no tiling for \((79,3)\). The proof uses Newton's identities and Lemma 5.5, without computing the entries that depend on the unknown \(u\).
  - Example 5.7: no tiling for \((80,3)\). Theorem 5.8 is checked for all 149 values of the unknown.
  - Example 5.10: no tiling for \((13,3)\). The manuscript uses Theorem 5.9; the Lean proof instead uses Lemma 5.4 with the forced value \(S_{366} = 103\).
  - The forced values quoted in the manuscript (11, 33, 63, 103) are confirmed by computation.
- **Theorem 2.7 (a) and (b)**: characters and Fourier inversion on a subgroup of \(\mathbb F_p^*\), in a new file `FourierUnits.lean`.
- **Ball sizes** quoted in Example 5.6, Proposition 5.12 and Example 5.13 are checked.
- **Numbering corrections.** The earlier docstrings used several wrong statement numbers. They now follow the compiled manuscript, e.g. Lemma 1.3, Theorems 1.7–1.9, Lemma 2.6, Lemma 5.5, Proposition 5.11, Proposition 5.12, Theorems 5.15–5.16 and Remark 5.17. Equation references now use the LaTeX labels. The definition for Proposition 5.12's statement was renamed to `Prop512Claim`.

**Overall coverage**
Every statement proved in the manuscript itself is now formalized and proved: Lemma 1.3 through Theorem 5.16 and Remark 5.17. The full map from statements to Lean declarations, with line numbers in the `.tex` file, is in `VERIFICATION_REPORT.md`.

Two caveats on how statements were proved:
- **Theorem 5.9** is proved directly with a Vandermonde argument. The general Feng–Hollmann–Xiang uncertainty principle (Theorem 2.5) it is derived from in the manuscript is not formalized.
- **Theorem 1.8** is stated over the rational group ring, since the equation has rational coefficients.

**Not proved (positions in the report)**
- **Maple-dependent results**, skipped as agreed:
  - Theorem 5.1 (line 897) and Proposition 5.12 (line 1234). Their statements are recorded as `MainComputationalClaim` and `Prop512Claim` in `Computational.lean`. The one non-computational step in the proof of Theorem 5.1, \(|B^n(r)| > 2^{30}\) for \(n, r \ge 13\), is proved.
  - Example 4.8 (line 872), Example 5.13 (line 1291), and the tables (lines 245, 1255, 1449–1700).
- **Results cited from other papers**, whose proofs are not in the manuscript: Conjecture 1.1, Theorem 1.2, Corollary 1.4, Theorem 1.5 and Theorem 2.5. Question 1.6 is answered by Theorem 1.8, which is proved.

The Properties table lists the main results, each linked to its line in the manuscript.

# Summary of changes for run 5436935f-a518-42bf-bb7b-dc3ee7c69466


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.