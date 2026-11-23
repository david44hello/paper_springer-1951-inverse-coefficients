# Lean proofs for Springer’s inverse-coefficient conjecture
Version 1.00 · November 22, 2026 · Guide to the privately verified proof candidate for the short paper, version 1.10.

The formalization defines the inverse coefficients using the analytic inverse of each univalent function on the exterior of the unit disk. The three main results have the following scope.

| Result | Lean declaration | Mathematical inputs |
|---|---|---|
| Theorem 1.2. The Catalan bound at every odd order, with equality precisely for the rotated slit maps | `Springer.odd_theorem_of_loewner_and_area` | Existence of the normalized disk Loewner evolution and the classical exterior area estimate for the map |
| Theorem 1.2. The numerical inequality and the necessity of a first coefficient of modulus one for equality | `Springer.odd_numerical_of_loewner` | Normalized Loewner existence alone |
| Theorem 1.3. The disk bound and its consequence for the modulus, for every odd order | `Springer.disk_theorem_of_loewner` | Normalized Loewner existence alone |
| Theorem 1.4. Explicit counterexamples at every even order from four onward | `Springer.even_four`, `Springer.even_family`, `Springer.even_order_counterexamples` | No external mathematical hypothesis |

The Loewner hypothesis asserts existence of a normalized analytic disk evolution ending at the prescribed map. Its type is `Springer.NormalizedLoewnerRepresentation`. The development proves trajectory uniqueness and the Herglotz representation, including the measurable family of circle measures. [Gumenyuk, §2.2 and Theorem B](https://arxiv.org/pdf/1603.04043#page=7)

The area hypothesis, `Springer.AreaBound`, states that the sum of the index times the squared modulus of the corresponding forward coefficient converges to at most one. The proof uses it to identify the map when equality holds. [Grönwall, equation (9), p. 75](https://www.jstor.org/stable/1968044)

The clean build covered all 67 project modules. Kernel replay covered the same modules. The axiom audit covered 228 public proof declarations; their reported axioms were confined to Lean’s three standard axioms. The external mathematical inputs above appear as explicit arguments. The private native comparator accepted the 18 declarations listed in [comparator.json](../comparator/comparator.json), including the quantified bounds and explicit counterexamples. The complete manuscript includes historical comparisons, asymptotics, and questions beyond those targets.
