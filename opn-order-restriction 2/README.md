# Orders Three and Six at the Largest Prime Divisor of an Odd Perfect Number

This updated archive accompanies the expanded paper `paper.pdf` and includes
the 3-adic, Euler-prime, and distinct fourth-power-prime refinements, together
with upper bounds from cyclotomic values and degrees. Theorem 17 states the
combined lower and upper inequality with every variable defined in its own
statement. The archive contains a complete
Lean formalization of the original inequalities, their three corollaries, and
the new refinements and examples, starting from
mathlib's `Nat.Perfect N` and `Odd N`, together with the assumption that `P` is a
largest prime divisor of `N`. No additional number-theoretic conjecture is assumed.

The result is a necessary condition for an odd perfect number. It does not assert
that such a number exists or prove that none exists. Publication priority has not
been established.

## Files

| File | Purpose |
| --- | --- |
| `paper.pdf` | Updated paper with the original results, all three refinements, proofs, and references. |
| `paper.tex` | Editable LaTeX source of the updated paper. |
| `LargestPrimeOrders.lean` | Arithmetic prerequisites and the two main inequalities. |
| `Consequences.lean` | Explicit low-order bounds and the three corollaries. |
| `ThreeAdicRefinement.lean` | Both new piecewise bounds, valuation identities, and existence and uniqueness of the prime with an odd exponent. |
| `RefinementConsequences.lean` | The concrete exponent-8 and exponent-2 consequences of the new bounds. |
| `CubicCofactors.lean` | Divisibility, size, residue, and disjointness properties of the cubic cofactors; each forces a repeated prime divisor. |
| `FourthPowerBudget.lean` | The count of distinct fourth-power prime divisors and the stronger exponent-8 dichotomy. |
| `CyclotomicUpper.lean` | Upper bounds from cyclotomic values, totients, and the odd part of P-1; the case with no Wieferich congruences. |
| `CombinedBounds.lean` | The self-contained theorem's combined inequalities and their restriction on the exponent at P. |
| `Audit.lean` | Public theorem types and their axiom dependencies. |
| `lakefile.lean`, `lean-toolchain` | Pinned Lean and mathlib configuration. |
| `verify.sh` | Build the proof files and run the audit. |
| `verification.log` | Actual compiler output and axiom report from verification. |
| `SHA256SUMS` | Checksums of the delivered files. |

The Lean files are parts of one project, not alternative proofs. The combined
theorem is in `CombinedBounds.lean`. The verification entry point for all the results
is `Audit.lean`; run `bash verify.sh` after the setup below.

## Reproduce the verification

Install Lean's `elan` toolchain manager using the official instructions at
<https://github.com/leanprover/elan>. From the extracted project directory run:

```sh
lake update
lake exe cache get
bash verify.sh
```

The first two commands require internet access to obtain the pinned dependencies
and compiled mathlib cache. The toolchain file selects Lean 4.19.0. The Lake file
pins mathlib to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
`lake build` checks all eight proof modules; `lake env lean Audit.lean` checks the
public declarations and prints their axiom dependencies. A successful verification
exits with status zero. No previously compiled local proof modules are included in
this archive.

The recorded verification used the same Lean version and mathlib revision through
the Lean compiler directly against an existing mathlib cache. A local launcher
supplied the import paths and a container-specific executable-path workaround;
neither changes the proof terms or Lean's kernel. `verification.log` records the
compiler commands, source hashes, and their exit statuses. The public reproduction
procedure uses standard Lake commands and needs no such launcher.

## What is formalized

Let `a_q = N.factorization q`, and let `P` be a largest prime divisor of the odd
perfect number `N`. The function `component N q` is the geometric sum
`1 + q + ... + q^a_q`. The lemma `component_sigma` identifies this sum with
mathlib's divisor-sum function on the corresponding prime power.

`ord P q` is the multiplicative order `orderOf (q : ZMod P)`.
`high N P` consists of primes `q` dividing `N` with `q < P` and order different
from 3 and 6. Its name is shorthand for this set, not a further hypothesis about
the numerical size of the order. `sources N P d` consists of contributing primes
of order `d`.

All public theorem names are in the namespace `LargestPrimeOrders`:

| Paper result | Lean theorem |
| --- | --- |
| Sum over `high` is at least `a_P - 2` | `largestPrime_order_bound` |
| Sum is at least `a_P - 1` if `3` does not divide `N` | `largestPrime_order_bound_without_three` |
| Combined order-3 and order-6 contribution is at most 2 | `low_order_contribution_bound` |
| Combined contribution is at most 1 if `3` does not divide `N` | `low_order_contribution_bound_without_three` |
| Corollary 7: two distinct contributing primes or a congruence modulo `P^2` | `fourth_power_alternative` |
| Corollary 8: exponent 1 or the exceptional pair | `exceptional_pair` |
| Corollary 9: contributing exponents are at least 4, or at least 9 when odd | `high_contributor_exponents` |

Natural-number subtraction truncates at zero. This is equivalent to the paper's
lower bounds because each valuation is nonnegative. The hypothesis `P^4 | N` in
Corollary 7 is represented by `4 ≤ N.factorization P`, and its congruence is
represented by `P^2 | q^(P-1)-1`. The exceptional-pair theorem expresses the
order and contribution conditions using `sources`; the polynomial and shifted
exponent divisibilities follow from `order_three_phi` and
`order_dvd_of_component_dvd`. The exponent theorem uses the condition that the
exponent is odd; no separate formalization of Euler's structure theorem is needed.

## The 3-adic refinement

Write `W = highWeight N P`, `b = padicValNat 3 N`, and
`t = padicValNat 3 (N.factorization P + 1)`.
The function `threeAllowance b t` is defined by:

| Condition | Allowance | Bound on W |
| --- | --- | --- |
| `b < t` | 0 | `a_P` |
| `b = t` | 1 | `a_P - 1` |
| `b > t` | 2 | `a_P - 2` |

The theorem `three_adic_refinement` proves that
`a_P - threeAllowance b t ≤ W`.

For a prime divisor `e` with odd factorization exponent, `eulerThreeDelta N e`
is `padicValNat 3 (e+1) + padicValNat 3 (a_e+1)` if `e % 3 = 2`, and zero
otherwise. The theorem `euler_three_adic_refinement` replaces `t` by
`t + eulerThreeDelta N e` in the same allowance. Membership of `e` among the
prime divisors and oddness of its exponent specify the Euler prime; no unproved
valuation identity is assumed. The separate theorem
`exists_unique_odd_exponent_prime` derives existence and uniqueness directly from
odd perfectness. `exists_euler_three_adic_refinement` combines existence with the
stronger bound, so its hypotheses mention only `N`, `P`, and the original
odd-perfect-number and maximal-prime assumptions.

| New result | Lean theorem |
| --- | --- |
| The bound using the exponents at 3 and P | `three_adic_refinement` |
| The stronger bound using the Euler-prime contribution | `euler_three_adic_refinement` |
| Existence and uniqueness of the prime with an odd exponent | `exists_unique_odd_exponent_prime` |
| Euler refinement with existence discharged | `exists_euler_three_adic_refinement` |
| If `a_3 = 2` and `a_P = 8`, then `W ≥ 7` | `eighth_power_refinement` |
| If also `e % 3 = 2`, then `W = 8` | `eighth_power_euler_refinement` |
| If `3` does not divide `N` and `a_P = 2`, then `W = 2` | `no_three_square_highWeight` |
| In that case, two contributors or a congruence modulo `P^2`, with each contributing exponent at least 4 | `no_three_square_alternative` |

The supporting lemmas prove the two geometric-sum valuation identities by using
mathlib's lifting-the-exponent theorem. They derive both the single-source and
paired-source constraints on the available 3-adic valuation, including the extra
contribution from the Euler prime when it is congruent to 2 modulo 3. The final
inequalities are therefore formalized from the arithmetic hypotheses, rather
than supplied as assumptions to an arithmetic-only wrapper.

## The stronger fourth-power condition

Let `K = (fourthPrimes N P).card`: the number of distinct prime divisors `r` of
`N` satisfying `r < P`, `r % 3 = 1`, and `4 ≤ a_r`. If `P % 3 = 1`, then

```text
2*t + delta ≤ b + K,     where delta = eulerThreeDelta N e.
```

In particular, `2*t ≤ b + K`. If `b = t + delta`, this forces `K ≥ t`.
These statements are Theorem 11 in the updated paper.

For each `0 ≤ j < t`, the integer

```text
C_j = (P^(2*3^j) + P^(3^j) + 1) / 3
```

divides `N`, exceeds `P`, and has only prime divisors smaller than `P` and
congruent to 1 modulo 3. The `C_j` are pairwise coprime. Each `C_j` must have
a prime divisor with exponent at least two in `N`: otherwise it could only
be supported by the Euler prime, with exponent one, and could not exceed `P`.
Thus there are `t` distinct candidate primes. Every candidate not counted in
`K` has exponent exactly two and contributes one unit of 3-adic valuation to
the divisor-sum product. At most `b - t - delta` such candidates can occur.
The Lean proof derives all these facts; the candidate primes and the valuation
inequalities are not extra hypotheses.

The concrete consequence strengthens the earlier `W ≥ 7`:

```text
a_3 = 2 and a_P = 8  ==>  W = 8 or (W = 7 and K ≥ 2).
```

The two fourth-power prime divisors in the second case are distinct. They are
not asserted to lie in `high N P`, and the conclusion does not assume that
the weight `W` is spread across different prime divisors.

| Latest result | Lean theorem |
| --- | --- |
| `t` distinct smaller primes congruent to 1 modulo 3, each with exponent at least two | `cubic_distinct_candidates` |
| `2*t + delta ≤ b + K` | `fourth_power_budget_euler` |
| `2*t ≤ b + K` | `fourth_power_budget` |
| If `b = t + delta`, then `t ≤ K` | `saturated_fourth_power_count` |
| If `a_3 = 2` and `a_P = 8`, then `W = 8` or `W = 7` with `K ≥ 2` | `eighth_power_fourth_power_dichotomy` |

The first four rows assume `P % 3 = 1`; the last row derives that congruence
in the `W = 7` case. The Euler-refined rows specify `e` by prime-factor
membership and odd exponent. The project proves such a prime exists uniquely;
the plain count theorem discharges that existence internally.

## Upper bounds for W

Section 7 of the paper gives upper bounds independent of `a_P`. Let
`T = highContributors N P`, the subset of `high N P` whose components are
divisible by `P`, and let `M = T.card`. Write `d_q = ord P q`.

For every `q ∈ T`, the proof establishes

```text
w_q = v_P(Phi_(d_q)(q))
    ≤ floor(log_P(Phi_(d_q)(q)))
    ≤ phi(d_q) - 1.
```

Thus `W` is at most the sum of the logarithmic bounds, and hence at most
`sum (phi(d_q)-1)` over `q ∈ T`. Here `Phi` is the cyclotomic polynomial
and `phi` is Euler's totient. The integer logarithm is `Nat.log` in Lean.
The key estimate is `0 < Phi_d(q) < P^phi(d)`; the proof also establishes
that the entire component valuation occurs in this single cyclotomic factor.

If `P-1 = 2^s*m` with `m` odd, then

```text
W ≤ M*(phi(m)-1).
```

This uses the proved fact that `4` does not divide a contributing order.
Such an order is `u` or `2*u` for an odd divisor `u` of `m`, and its totient
is at most `phi(m)`. Combining the upper bound with Theorem 1 gives

```text
a_P ≤ c(N) + sum (phi(d_q)-1) ≤ c(N) + M*(phi(m)-1),
where c(N) = 2 if 3 divides N, and c(N) = 1 otherwise.
```

When none of the contributing bases satisfies `q^(P-1) = 1 mod P^2`, the
stronger equality `W = M` holds. That extra hypothesis matters: for example,
`ord_11(3) = 5` and `Phi_5(3) = 121`, illustrating a contribution of two in
the local arithmetic. This example is not an odd perfect number.

| Upper-bound result | Lean theorem |
| --- | --- |
| Component valuation equals the cyclotomic-value valuation | `component_val_eq_cycloValue` |
| Each contribution is at most `phi(d_q)-1` | `high_component_totient_upper` |
| Sum of integer logarithms bounds `W` | `highWeight_log_upper` |
| The logarithmic sum is at most the totient sum | `logarithmic_bound_le_totient_bound` |
| The totient sum bounds `W` | `highWeight_totient_upper` |
| `W ≤ M*(phi(m)-1)` | `highWeight_odd_part_upper` |
| `a_P ≤ c(N) + sum (phi(d_q)-1)` | `largest_exponent_totient_upper` |
| Without contributing Wieferich bases, `W = M` | `highWeight_eq_card_of_no_wieferich` |

Theorem 17 of the paper defines all symbols and states the complete chain:

```text
a_P - A(b,t+delta) ≤ W
  ≤ min(a_P, logarithmicCapacity N P)
  ≤ min(a_P, totientCapacity N P)
  ≤ min(a_P, oddPartCapacity N P m).
```

The compiled theorem `combined_inequality` proves the first two inequalities
and both capacity comparisons, from which the displayed chain follows.
`combined_exponent_constraint` concludes `a_P ≤ A(b,t+delta) + M*(phi(m)-1)`;
`exists_combined_exponent_constraint` derives the existence of the Euler prime
from odd perfectness rather than assuming it separately.

The usable upper bound is the minimum of `a_P` and these bounds. They do not
give a uniform numerical constant, or a contradiction for all odd perfect
numbers. These are consequences of classical cyclotomic estimates; no claim
of publication priority is made.

## Trust and scope

The source contains no `sorry`, `admit`, added axioms, or use of `native_decide`.
The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`:
Lean's standard propositional extensionality, classical choice, and quotient
soundness axioms. Correctness is conditional on Lean's kernel and those standard
foundations. The audit checks the formal statements; it does not certify novelty
or the completeness of a literature review.

To rebuild the PDF with a LaTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```
