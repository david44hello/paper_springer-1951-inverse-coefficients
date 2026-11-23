# Lean proofs for Springer’s inverse-coefficient conjecture

The formalization defines the inverse coefficients using the analytic inverse of each univalent function on the exterior of the unit disk. The three main results have the following scope.

| Result | Lean declaration | Mathematical inputs |
|---|---|---|
| Theorem 1.2. The Catalan bound at every odd order, with equality precisely for the rotated slit maps | `Springer.odd_theorem_of_loewner_and_area` | Existence of the normalized disk Loewner evolution and the classical exterior area estimate for the map |
| Theorem 1.2. The numerical inequality and the necessity of a first coefficient of modulus one for equality | `Springer.odd_numerical_of_loewner` | Normalized Loewner existence alone |
| Theorem 1.3. The disk bound and its consequence for the modulus, for every odd order | `Springer.disk_theorem_of_loewner` | Normalized Loewner existence alone |
| Theorem 1.4. Explicit counterexamples at every even order from four onward | `Springer.even_four`, `Springer.even_family`, `Springer.even_order_counterexamples` | No external mathematical hypothesis |

## Results taken as given

The Loewner hypothesis asserts existence of a normalized analytic disk evolution ending at the prescribed map. Its type is `Springer.NormalizedLoewnerRepresentation`. It is the classical parametric representation of Loewner, Kufarev and Pommerenke, without the uniqueness of the trajectories. The development proves trajectory uniqueness and the Herglotz representation, including the measurable family of circle measures. [Gumenyuk, §2.2 and Theorem B](https://arxiv.org/pdf/1603.04043#page=7)

The area hypothesis, `Springer.AreaBound`, states that the sum of the index times the squared modulus of the corresponding forward coefficient converges to at most one. Only the identification of the map when equality holds needs it; `Springer.odd_numerical_of_loewner` proves the inequality without it. [Grönwall, equation (9), p. 75](https://archive.org/details/jstor-1968044)

Both hypotheses appear as explicit arguments of the statements that use them. Neither says anything about inverse coefficients.

## Verification of this release

Lean’s native comparator accepted the 18 declarations listed in [comparator.json](../comparator/comparator.json) against their stated types after a clean build, including the quantified bounds and the explicit counterexamples. [Comparison instructions](../comparator/README.md)

The five additional checkers `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, and `con-ron` accepted the same exported proof. Its SHA-256 digest is `1db25f9e8dd4f96a393c2626c25698588bcc199d2fbdd8dbf46f72c6815eaa00`.

The audit, [AUDIT.md](AUDIT.md), lists 228 public theorems; each depends only on Lean’s three standard axioms.

The paper also contains the classical case of order two, historical comparisons, asymptotic statements and open questions. They are outside these 18 declarations.
