# Uniform exclusion of Landau–Siegel zeros: Lean formalization

This project formalizes the mathematical results in the body of the paper and their
proof dependencies. The main theorem uses Mathlib's actual Dirichlet L-function,
with no additional analytic or arithmetic hypotheses. See
[PAPER_COVERAGE.md](PAPER_COVERAGE.md) for the detailed scope and the correspondence
between paper results and formal proofs. The final library verification, axiom
dependencies for each theorem, and source checksums are recorded in
`verification/status.json` and `verification/axioms.txt`.

Final verification passed on October 10, 2026: the entire library compiled, and all
406 public theorems passed the axiom dependency audit. There is no `sorryAx` or
custom axiom; the proofs use only Lean's standard foundational axioms.

The source is the nine-page paper
`OpenAI - Uniform exclusion of Landau–Siegel zeros.pdf` in the project root, dated
October 1, 2026. The original PDF is unchanged. The two separate Quasi-RH PDFs in
the local workspace are outside the scope of this project.

## Main theorem

The entry point is [Main.lean](Siegel/Main.lean). The theorem with all quantifiers
written explicitly is `Siegel.uniform_exclusion_of_landau_siegel_zeros`:

```lean
∃ c : ℝ, 0 < c ∧
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
    3 ≤ q → χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
    0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
      c ≤ (1 - β) * Real.log (q : ℝ)
```

The constant `c` is quantified before the conductor, character, and zero.
`χ.IsQuadratic` means that the character takes values in `{0, 1, -1}`; together
with the nonprincipal condition, it expresses the real quadratic character
condition used here. `Siegel.uniformExclusion : Siegel.UniformExclusion` is a
compact version of the same theorem. `UniformExclusion` itself is a proposition
definition; its proof is supplied by these two `theorem` declarations.

## Verification

The toolchain is pinned to Lean `v4.30.0`, and Mathlib is pinned to `v4.30.0`, with
the exact commit recorded in `lake-manifest.json`. From the project directory,
run:

```sh
bash scripts/verify.sh
```

The script regenerates the theorem inventory, builds the entire library, runs
`#print axioms` for every public theorem, and checks the original PDF's checksum.
The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The project proofs use no `sorry`, `admit`, or custom axioms, and no unproved
estimate is supplied as a hypothesis of the final theorem.

You can also run the build and axiom audit separately:

```sh
lake build
lake env lean Audit.lean
```

`verification/status.json` records the audit time, theorem count, final theorem
names, and per-file SHA-256 checksums. `verification/build.txt` and
`verification/axioms.txt` contain the full verification logs.

The repository includes all source files, the toolchain specification, and the
dependency lockfile. Lake retrieves the dependencies and build cache. After
installing the Lean toolchain manager elan, reproduce the verification on a new
machine with:

```sh
git clone https://github.com/AolinHAN/landau-siegel-lean.git
cd landau-siegel-lean
lake exe cache get
bash scripts/verify.sh
```

The original paper PDF and the successful build and axiom audit records are also
included in the repository.

## Reading guide

1. [Main.lean](Siegel/Main.lean): the main theorem with all quantifiers.
2. [PaperZeroIdentity.lean](Siegel/PaperZeroIdentity.lean):
   `paper_equation_two_three_complete`, proving equation (2.3) with the actual
   nontrivial zero multiplicities, summability, nonnegativity, and the identity.
3. [SingleZeroBound.lean](Siegel/SingleZeroBound.lean):
   derives (2.4) from the global formula by retaining the term for the real zero
   β. The main theorem uses this analytic route.
4. [TorusInterpretation.lean](Siegel/TorusInterpretation.lean):
   the Euler derivation identity and rectangular multiplicity estimate of Remark 5.
5. [PAPER_COVERAGE.md](PAPER_COVERAGE.md):
   the files and theorem names corresponding to all 24 numbered formulas and each
   theorem, lemma, corollary, and remark.

Open the entire project folder in VS Code, then open the `.lean` files above.
Place the cursor on a proof step to see the current goal in Lean InfoView, and
use F12 to follow referenced lemmas. A local `No goals` message only means that
the goal at that location has been closed. Use the verification script and axiom
audit to assess the status of the whole library.

## Additional formalized results from the paper

| Paper content | Files and theorems |
|---|---|
| Global zero formula (2.3), with actual multiplicities, convergence, and nonnegativity | `PaperZeroIdentity.lean`: `paper_equation_two_three_complete`; `NontrivialZeros.lean` |
| Completed L-function, functional equation, growth bounds, Γ factor, and bounds uniform in both parities | `CompletedLFunction.lean`, `CompletedGrowth.lean`, `CompletedLogDerivative.lean` |
| Exact normalization of the paper's completed L-function and its real-axis Γ′/Γ notation | `PaperCompletion.lean`, `PaperRealIdentity.lean` |
| Derivation of (2.4) from (2.3) by retaining the β term | `SingleZeroBound.lean`: `logDerivativeUpper_from_global_zeros` |
| Two-sided absolute error bound in the Mertens estimate | `MertensTwoSided.lean`: `exists_mertens_absolute_error_bound` |
| Absolute error bound for the pole term of the logarithmic derivative of ζ | `ZetaPoleError.lean`: `exists_zeta_logDerivative_absolute_error_bound` |
| The actual Euler derivation and interpolation formulation in Remark 5 | `TorusInterpretation.lean`: `remark_five_identity`, `rectangular_multiplicity_estimate` |
| Squarefree d for every q≥3, size bounds, and the correspondence between quadratic fields and Legendre characters | `SquarefreeCharacter.lean`: `exists_squarefree_character_radical`; `SectionFour.lean` |
| Independence of the four generators for d≠1,2, the actual number field degree, and Galois automorphisms | `SquarefreeIndependence.lean`, `BiquadraticFieldDegree.lean`, `BiquadraticField.lean` |
| N=⌈q^γ⌉ for any fixed real γ>0, all parameter limits, and the final contradiction | `CeilingParameters.lean`: `ceilingCutoff_log_ratio_tendsto`, `ceiling_comparison_impossible` |
| Equivalence between real-valued characters and IsQuadratic, and the main theorem with an explicit real-valuedness condition | `RealCharacter.lean`, `RealCharacterMain.lean` |

The existing formalizations of Lemma 2, Lemma 3, Corollary 4, Lemma 6, Lemma 7,
the determinant upper and lower bounds, the treatment of finitely many
conductors, and the final uniform gap theorem are retained. The coverage table
gives the detailed correspondence.

## Proof implementation and scope

Global formula (2.3) has an independent proof: global growth bounds for the
completed L-function → Jensen zero counts and inverse Blaschke factors on
arbitrarily large disks → a limit of logarithmic derivative differences →
summability of the nonnegative real-part series → cancellation of the constant
by reflection pairing via the functional equation. This proves the paper's zero
identity without separately constructing an infinite Hadamard product. It does
not assert absolute convergence of the unregularized complex series Σρ 1/(s−ρ).

`nontrivialZeroMultiplicity` is defined directly from the analytic multiplicity
of the actual `χ.LFunction` in the open critical strip. It is proved to equal the
zero divisor of the completed L-function. `PaperCompletion.lean` also defines
the completed L-function with the paper's exact normalization and proves that
it has the same zero multiplicities and logarithmic derivative as the version
used in the calculations. The zero sum is not defined to be the right-hand side
of the identity being proved.

The earlier local disk proof remains in `LogDerivativeUpper.lean` and related
modules. The arithmetic argument can use a signed conductor, and a version using
a squarefree radicand is also provided. The final parameter may be chosen as the
integer power `N=q^k` permitted by the paper; the ceiling version for any fixed
real exponent is proved separately as well. These implementation differences
add no hypotheses to the final theorem.

The completed scope covers the mathematical results in the body of the paper
and their actual dependencies, allowing complete equivalent proofs. It is not a
line-by-line transcription of the prose, nor does it claim to re-formalize all
literature cited in the introduction, the classification of fundamental
discriminants, or general Galois theory.
