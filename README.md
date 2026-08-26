[![Logo for Axiom Math](logo.svg)](https://axiommath.ai/)

# Tan Arctan

This repository contains Lean files for the formalisation of three results about the
Gaussian integers $P_n = \prod_{k=1}^{n}(1 + ik)$, the rational sequence
$x_n = \mathrm{Im}(P_n) / \mathrm{Re}(P_n)$, and the arctangent angle sum
$a_n = \sum_{k=1}^{n} \arctan(1/k)$.

Writing $A_n = \mathrm{Re}(P_n)$, $B_n = \mathrm{Im}(P_n)$,
$\omega_n = A_n^2 + B_n^2 = \prod_{k=1}^{n}(1 + k^2)$, and letting $K_n$ be the squarefree
kernel of $\omega_n$ (the product of the primes dividing $\omega_n$ to an odd power), the
formalised statements are:

1. **`thm_main`** — If $x_n = m$ is an integer (with $A_n \neq 0$), then $K_n \mid (1 + m^2)$,
   and if $K_n > 1$ then $|m| \ge \sqrt{K_n - 1}$.
2. **`lem_proximity`** — For every $n$ in the exceptional set
   $E = \{\, n \ge 5 : |x_n| > n/2 + 1 \,\}$ there is an integer $j$ with
   $\left| a_n - j\,\tfrac{\pi}{2} \right| < \tfrac{2}{n}$.
3. **`cor_density`** — $#\bigl(E \cap [1, N]\bigr) = O(\log N)$.

The proofs were produced by [AxiomProver](https://axiommath.ai/) and are fully sorry-free.
They were developed and verified using **Lean 4.28.0**. Compatibility with earlier or later
versions is not guaranteed due to the evolving nature of the Lean 4 compiler and its core
libraries.

## Files

### Input Files

- [`input/main_engine.tex`](input/main_engine.tex) and [`input/task.md`](input/task.md) contain
  the informal source and the task given to AxiomProver.

### Output Files

- [`problem.lean`](output/problem.lean) is the formal problem statement.
- [`solution.lean`](output/solution.lean) is the formal solution.

## Verifying with Comparator

This repository can be verified against the formal problem statement with the Lean comparator on a Linux machine. First, follow the instructions in [https://github.com/leanprover/comparator](https://github.com/leanprover/comparator) to install comparator. Then, run the following command:

```
lake env comparator comparator.json
```

## License

This repository uses the MIT License. See [LICENSE](LICENSE) for details.

## Repository maintainers

- [Evan Chen](https://github.com/vEnhance)
- [Ken Ono](https://github.com/kenono691)
