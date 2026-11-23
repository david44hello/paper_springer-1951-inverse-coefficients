# Springer's 1951 conjecture on inverse coefficients

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_springer-1951-inverse-coefficients).

This folder proves the paper's three main theorems in Lean 4: Theorem 1.2 (the Catalan bound at every odd order, with equality exactly for the rotated slit maps), Theorem 1.3 (the disk bound at every odd order) and Theorem 1.4 (explicit counterexamples at every even order from four on).

Theorem 1.4 requires no external mathematical hypothesis. Theorem 1.3 and the inequality of Theorem 1.2 take as given the classical existence of the normalized Loewner evolution in the disk. The characterization of equality in Theorem 1.2 also takes the exterior area theorem. For the exact statements and their sources, see [What to read](WHAT_TO_READ.md).

## Directions to Reproduce

Install Git, Python 3 and elan, the Lean toolchain manager. From the `lean/` directory of a Git checkout, run:

```sh
./scripts/check.sh
```

It downloads Mathlib's build files once, builds the proof, checks the main theorem statements and regenerates the audit, [AUDIT.md](AUDIT.md). Its final line reads `Springer verification passed.` The largest Lean compilation used about 6.6 GiB of memory with Mathlib already cached.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
