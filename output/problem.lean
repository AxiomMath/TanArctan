import Mathlib

open scoped BigOperators

/-
# Problem Description

Throughout, $i$ denotes the imaginary unit and $\mathbb{Z}[i]$ the Gaussian integers.

We study the Gaussian integer $P_n = \prod_{k=1}^n (1 + i k)$, its real and imaginary
parts $A_n, B_n$, the rational sequence $x_n = B_n / A_n$, the norm
$\omega_n = A_n^2 + B_n^2 = \prod_{k=1}^n (1 + k^2)$, the squarefree kernel $K_n$ of
$\omega_n$ (the product of primes dividing $\omega_n$ to an odd power), the exceptional set
$E = \{ n \ge 5 : |x_n| > n/2 + 1 \}$, and the angle sum
$a_n = \sum_{k=1}^n \arctan(1/k)$.

Main statements:
1. (`thm:main`) If $x_n = m \in \mathbb{Z}$ (with $A_n \ne 0$), then $K_n \mid (1 + m^2)$,
   and if $K_n > 1$ then $|m| \ge \sqrt{K_n - 1}$.
2. (`lem:proximity`) For every $n \in E$ there is $j \in \mathbb{Z}$ with
   $|a_n - j \pi/2| < 2/n$.
3. (`cor:density`) $\#(E \cap [1,N]) = O(\log N)$.
-/

/-
## Background and context

Direct computation confirms the recurrence and initial values: with $P_n = A_n + i B_n$,
one gets $A_1 = B_1 = 1$, $A_2 = -1, B_2 = 3$, $A_3 = -10, B_3 = 0$, $A_4 = -10, B_4 = -40$,
$A_5 = 190, B_5 = -90$, $A_6 = 730, B_6 = 1050$, giving
$x_1 = 1, x_2 = -3, x_3 = 0, x_4 = 4, x_5 = -9/19, x_6 = 105/73$.
The identity $\omega_n = \prod_{k=1}^n (1 + k^2)$ follows from multiplicativity of the norm:
$|1 + i k|^2 = 1 + k^2$.

Domain caveat for $x_n$: $x_n$ is defined only when $A_n \ne 0$. In `thm:main` the hypothesis
$A_n \ne 0$ is stated explicitly. In the definition of $E$ (and hence Statements 2 and 3) we
adopt the extended-value convention: indices with $A_n = 0$ are treated as belonging to $E$
(reading $|x_n|$ as $+\infty$). Such indices are rare and do not affect the $O(\log N)$ bound.
-/

-- Main Definition(s)

/-- Definition 1. The Gaussian integer $P_n = \prod_{k=1}^n (1 + i k) \in \mathbb{Z}[i]$. -/
def P (n : ℕ) : GaussianInt := ∏ k ∈ Finset.Icc 1 n, (⟨1, (k : ℤ)⟩ : GaussianInt)

/-- The real part $A_n = \operatorname{Re}(P_n)$. -/
def A (n : ℕ) : ℤ := (P n).re

/-- The imaginary part $B_n = \operatorname{Im}(P_n)$. -/
def B (n : ℕ) : ℤ := (P n).im

/-- Definition 2. The rational sequence $x_n = B_n / A_n$ (meaningful when $A_n \ne 0$). -/
noncomputable def x (n : ℕ) : ℚ := (B n : ℚ) / (A n : ℚ)

/-- Definition 3. The norm $\omega_n = A_n^2 + B_n^2 = |P_n|^2 = \prod_{k=1}^n (1 + k^2)$. -/
def omega (n : ℕ) : ℕ := (A n).natAbs ^ 2 + (B n).natAbs ^ 2

/-- Definition 4. The squarefree kernel $K_n$ of $\omega_n$: the product of the primes dividing
$\omega_n$ to an odd power. Here `Nat.factorization (omega n) p` is the $p$-adic valuation
$\nu_p(\omega_n)$. When no prime divides $\omega_n$ to an odd power the empty product gives
$K_n = 1$. -/
def K (n : ℕ) : ℕ :=
  ∏ p ∈ (omega n).primeFactors.filter (fun p => Odd ((omega n).factorization p)), p

/-- Definition 5. The exceptional set
$E = \{ n \ge 5 : |x_n| > n/2 + 1 \}$. Following the extended-value convention, an index with
$A_n = 0$ (so $x_n$ is undefined) is included in $E$. -/
def E : Set ℕ := {n | 5 ≤ n ∧ (A n = 0 ∨ ((n : ℚ) / 2 + 1 < |x n|))}

/-- Definition 6. The angle sum $a_n = \sum_{k=1}^n \arctan(1/k)$. -/
noncomputable def a (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, Real.arctan (1 / (k : ℝ))

-- Main Statement(s)

/-- Statement 1 (`thm:main`). Let $n \ge 1$ with $A_n \ne 0$, and suppose $x_n = m$ for some
integer $m$. Then $K_n \mid (1 + m^2)$, and if $K_n > 1$ then $|m| \ge \sqrt{K_n - 1}$. -/
theorem thm_main {n : ℕ} (hn : 1 ≤ n) (hA : A n ≠ 0) {m : ℤ} (hx : x n = (m : ℚ)) :
    ((K n : ℤ) ∣ (1 + m ^ 2)) ∧
      (1 < K n → Real.sqrt ((K n : ℝ) - 1) ≤ |(m : ℝ)|) := by
  sorry

/-- Statement 2 (`lem:proximity`). For every $n \in E$ there exists an integer $j$ such that
$|a_n - j \pi/2| < 2/n$. -/
theorem lem_proximity {n : ℕ} (hn : n ∈ E) :
    ∃ j : ℤ, |a n - (j : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ) := by
  sorry

/-- Statement 3 (`cor:density`). $\#(E \cap [1,N]) = O(\log N)$: there exist constants
$C > 0$ and $N_0$ such that for all $N \ge N_0$, $\#(E \cap [1,N]) \le C \log N$. -/
theorem cor_density :
    ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧ ∀ N : ℕ, N₀ ≤ N →
      ((E ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * Real.log N := by
  sorry
