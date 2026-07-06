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

-- Helper lemmas for Statement 2

/-- For `k ≥ 1`, `arctan(1/k) = arg(k + i)`. -/
lemma arctan_eq_arg (k : ℕ) (hk : 1 ≤ k) :
    Real.arctan (1 / (k : ℝ)) = Complex.arg (⟨(k : ℝ), 1⟩ : ℂ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hre : (0 : ℝ) ≤ (⟨(k : ℝ), 1⟩ : ℂ).re := le_of_lt hkpos
  rw [Complex.arg_of_re_nonneg hre]
  rw [Real.arctan_eq_arcsin]
  congr 1
  -- (1/k)/√(1+(1/k)^2) = im/‖·‖ = 1/√(k^2+1)
  have hnorm : ‖(⟨(k : ℝ), 1⟩ : ℂ)‖ = Real.sqrt ((k : ℝ) ^ 2 + 1) := by
    rw [Complex.norm_def, Complex.normSq_mk]
    congr 1; ring
  rw [hnorm]
  show (1 / (k:ℝ)) / Real.sqrt (1 + (1 / (k:ℝ)) ^ 2) = (1 : ℝ) / Real.sqrt ((k:ℝ) ^ 2 + 1)
  have h1 : Real.sqrt (1 + (1 / (k:ℝ)) ^ 2) = Real.sqrt ((k:ℝ)^2 + 1) / (k:ℝ) := by
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have : (1 : ℝ) + (1 / (k:ℝ)) ^ 2 = ((k:ℝ)^2 + 1) / (k:ℝ)^2 := by
      field_simp
    rw [this, Real.sqrt_div (by positivity)]
    rw [Real.sqrt_sq (le_of_lt hkpos)]
  rw [h1]
  field_simp

/-- The complex number `k + i` is nonzero for `k ≥ 0` real. -/
lemma cmk_ne (k : ℕ) : (⟨(k : ℝ), 1⟩ : ℂ) ≠ 0 := by
  intro h
  have : (⟨(k : ℝ), 1⟩ : ℂ).im = 0 := by rw [h]; rfl
  simp at this

/-- `(P n : ℂ) = ∏ (1 + k i)`. -/
lemma P_toComplex (n : ℕ) :
    ((P n : GaussianInt) : ℂ) = ∏ k ∈ Finset.Icc 1 n, (⟨1, (k : ℝ)⟩ : ℂ) := by
  unfold P
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [GaussianInt.toComplex_def₂]
  simp [Complex.ext_iff]

/-- `(a n : Angle) = arg(∏ (k + i))`. -/
lemma a_eq_arg_W (n : ℕ) :
    ((a n : ℝ) : Real.Angle) =
      ((Complex.arg (∏ k ∈ Finset.Icc 1 n, (⟨(k : ℝ), 1⟩ : ℂ))) : Real.Angle) := by
  unfold a
  induction n with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Finset.Icc_self, Finset.sum_singleton, Finset.prod_singleton]
      rw [arctan_eq_arg 1 (le_refl 1)]
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1),
          Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1)]
      rw [Real.Angle.coe_add, ih]
      rw [Complex.arg_mul_coe_angle]
      · rw [arctan_eq_arg (m+1) (by omega)]
      · exact Finset.prod_ne_zero_iff.mpr (fun k _ => cmk_ne k)
      · exact cmk_ne (m+1)

/-- `∏(k+i) = i^n * conj(P n)`. -/
lemma W_eq (n : ℕ) :
    (∏ k ∈ Finset.Icc 1 n, (⟨(k : ℝ), 1⟩ : ℂ)) =
      Complex.I ^ n * (starRingEnd ℂ) ((P n : GaussianInt) : ℂ) := by
  rw [P_toComplex]
  rw [map_prod]
  have : ∀ k ∈ Finset.Icc 1 n, (⟨(k : ℝ), 1⟩ : ℂ)
      = Complex.I * (starRingEnd ℂ) (⟨1, (k : ℝ)⟩ : ℂ) := by
    intro k _
    apply Complex.ext <;> simp [Complex.ext_iff]
  rw [Finset.prod_congr rfl this]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_const]
  congr 1
  simp

/-- `(P n : ℂ) ≠ 0`. -/
lemma P_ne_zero (n : ℕ) : ((P n : GaussianInt) : ℂ) ≠ 0 := by
  rw [P_toComplex]
  apply Finset.prod_ne_zero_iff.mpr
  intro k _ h
  have : (⟨1, (k : ℝ)⟩ : ℂ).re = 0 := by rw [h]; rfl
  simp at this

/-- Master identity: `(a n : Angle) = n • (π/2) - arg (P n)`. -/
lemma a_angle_eq (n : ℕ) :
    ((a n : ℝ) : Real.Angle) =
      n • (((Real.pi / 2 : ℝ)) : Real.Angle)
        - ((Complex.arg ((P n : GaussianInt) : ℂ)) : Real.Angle) := by
  rw [a_eq_arg_W, W_eq]
  rw [Complex.arg_mul_coe_angle (pow_ne_zero _ Complex.I_ne_zero) ?_]
  · rw [Complex.arg_conj_coe_angle]
    rw [Complex.arg_pow_coe_angle, Complex.arg_I]
    rw [sub_eq_add_neg]
  · intro h
    exact P_ne_zero n (by simpa using h)

-- Main Statement(s)

/-- Statement 1 (`thm:main`). Let $n \ge 1$ with $A_n \ne 0$, and suppose $x_n = m$ for some
integer $m$. Then $K_n \mid (1 + m^2)$, and if $K_n > 1$ then $|m| \ge \sqrt{K_n - 1}$. -/
theorem thm_main {n : ℕ} (hn : 1 ≤ n) (hA : A n ≠ 0) {m : ℤ} (hx : x n = (m : ℚ)) :
    ((K n : ℤ) ∣ (1 + m ^ 2)) ∧
      (1 < K n → Real.sqrt ((K n : ℝ) - 1) ≤ |(m : ℝ)|) := by
  -- B n = m * A n
  have hB : (B n : ℤ) = m * A n := by
    have hAQ : (A n : ℚ) ≠ 0 := by exact_mod_cast hA
    have : (B n : ℚ) / (A n : ℚ) = (m : ℚ) := hx
    have h2 : (B n : ℚ) = (m : ℚ) * (A n : ℚ) := by
      field_simp at this
      linarith [this]
    exact_mod_cast h2
  -- omega n as integer = A n ^2 (1 + m^2)
  have homega : (omega n : ℤ) = A n ^ 2 * (1 + m ^ 2) := by
    unfold omega
    push_cast
    rw [sq_abs, sq_abs]
    rw [hB]
    ring
  -- Work at ℕ level. Let c = (1 + m^2).toNat, a = (A n).natAbs.
  set c : ℕ := (1 + m ^ 2).toNat with hc_def
  set a : ℕ := (A n).natAbs with ha_def
  have hc_pos : 0 < 1 + m ^ 2 := by positivity
  have hc_int : (c : ℤ) = 1 + m ^ 2 := by
    rw [hc_def]; exact Int.toNat_of_nonneg (le_of_lt hc_pos)
  have ha_int : (a : ℤ) = |A n| := by rw [ha_def]; exact Int.abs_eq_natAbs (A n) |>.symm
  have ha_pos : 0 < a := by
    rw [ha_def]; exact Int.natAbs_pos.mpr hA
  have hc_pos' : 0 < c := by
    have : 0 < (c : ℤ) := by rw [hc_int]; exact hc_pos
    exact_mod_cast this
  have homega_nat : omega n = a ^ 2 * c := by
    have : (omega n : ℤ) = ((a ^ 2 * c : ℕ) : ℤ) := by
      push_cast
      rw [ha_int, hc_int, homega]
      rw [sq_abs]
    exact_mod_cast this
  -- Each prime with odd valuation in omega n divides c.
  have homega_ne : omega n ≠ 0 := by
    rw [homega_nat]; exact Nat.mul_ne_zero (pow_ne_zero 2 ha_pos.ne') hc_pos'.ne'
  have key_dvd : ∀ p ∈ (omega n).primeFactors.filter (fun p => Odd ((omega n).factorization p)),
      p ∣ c := by
    intro p hp
    simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, _, _⟩, hodd⟩ := hp
    have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha_pos.ne'
    have hval : (omega n).factorization p = 2 * a.factorization p + c.factorization p := by
      rw [homega_nat, Nat.factorization_mul ha2_ne hc_pos'.ne']
      simp only [Finsupp.coe_add, Pi.add_apply, Nat.factorization_pow, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul]
    rw [hval] at hodd
    have hc_odd : Odd (c.factorization p) := by
      rcases Nat.even_or_odd (c.factorization p) with he | ho
      · exfalso
        exact (Nat.not_odd_iff_even.mpr (by exact (Even.add (even_two_mul _) he))) hodd
      · exact ho
    have hpos : 0 < c.factorization p := hc_odd.pos
    exact Nat.dvd_of_factorization_pos hpos.ne'
  -- Convert to the goal: work over ℤ
  have hKc_int : (K n : ℤ) ∣ (1 + m ^ 2) := by
    rw [← hc_int]
    have hcast : ((K n : ℕ) : ℤ) = ∏ p ∈ (omega n).primeFactors.filter
        (fun p => Odd ((omega n).factorization p)), (p : ℤ) := by
      unfold K
      push_cast
      rfl
    rw [hcast]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Nat.mem_primeFactors] at hp hq
      have hpp : p.Prime := hp.1.1
      have hqp : q.Prime := hq.1.1
      have hco : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).mpr hpq
      simp only [Function.onFun]
      exact hco.isCoprime
    · intro p hp
      exact Int.natCast_dvd_natCast.mpr (key_dvd p hp)
  refine ⟨hKc_int, ?_⟩
  intro hK1
  -- K n ≤ c = 1 + m^2, so K n - 1 ≤ m^2
  have hKle : (K n : ℤ) ≤ 1 + m ^ 2 := Int.le_of_dvd hc_pos hKc_int
  have hKm : (K n : ℝ) - 1 ≤ (m : ℝ) ^ 2 := by
    have : (K n : ℝ) ≤ 1 + (m : ℝ) ^ 2 := by exact_mod_cast hKle
    linarith
  calc Real.sqrt ((K n : ℝ) - 1) ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt hKm
    _ = |(m : ℝ)| := Real.sqrt_sq_eq_abs m

/-!
### Sub-lemma for Statement 2 (the `hxbig` analytic kernel)

The remaining content of `lem_proximity` is the case where `|x_n| = |B_n/A_n|` is large.
We factor it out as `arg_close_of_ratio_large`.

MATH ARGUMENT (rigorous):
Write `φ = arg(P_n)` where `P_n = A_n + i B_n` (with `re = A_n`, `im = B_n`).
The tangent of the argument is `B_n / A_n = x_n`, so `|x_n|` large means the point
`(A_n, B_n)` is nearly vertical, i.e. `φ` is close to `±π/2`.

Precisely: suppose `A_n ≠ 0` and `n/2 + 1 < |x_n| = |B_n/A_n|`. Set `t = A_n/B_n`, so
`|t| = 1/|x_n| < 1/(n/2 + 1) = 2/(n+2) < 2/n`.  There are two cases on the sign of `A_n B_n`.

- If `A_n > 0` (so `arg` lies in `(-π/2, π/2]`): then `arg(A_n + i B_n) = arctan(B_n/A_n)`,
  and `arctan(x_n)` is within `arctan(1/|x_n|) = |π/2 - |arctan(x_n)||` of `sign(x_n)·(π/2)`.
  Concretely, using `arctan u + arctan(1/u) = ±π/2` for `u ≠ 0`, we get
  `|arctan(x_n) - sign(x_n)·(π/2)| = arctan(1/|x_n|) ≤ 1/|x_n| < 2/n`.
- If `A_n < 0`: `arg` is `arctan(B_n/A_n) ± π`, still within `arctan(1/|x_n|)` of `±π/2`,
  again a multiple of `π/2` at distance `< 2/n`.

The key analytic inequality is `arctan y ≤ y` for `y ≥ 0` (Mathlib: `Real.arctan_le_self`
or `Real.arctan_lt_self`/`Real.abs_arctan_le`), applied with `y = 1/|x_n|`.

Relevant Mathlib API to look for in the formal phase:
- `Complex.arg` and `Complex.arg_of_re_nonneg` / the arctan characterization of `arg`.
- `Real.arctan_add`, `Real.arctan_inv_of_pos`/`Real.arctan_inv_of_neg`
  (`arctan(1/x) = π/2 - arctan x` for `x>0`), `Real.arctan_le_self`, `Real.arctan_lt_self`.
- `Complex.tan_arg`, `Complex.arg_mem_Ioc`.
-/

/-- arctan is bounded by its argument on the nonnegatives. -/
lemma arctan_le_self' {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  have h1 : 0 ≤ Real.arctan y := Real.arctan_nonneg.mpr hy
  have h2 : Real.arctan y < Real.pi / 2 := Real.arctan_lt_pi_div_two y
  have := Real.le_tan h1 h2
  rwa [Real.tan_arctan] at this

/-- Tail bound: for `w ≠ 0`, `arctan w` is within `arctan(|w|⁻¹) ≤ |w|⁻¹` of `±π/2`. -/
lemma arctan_close_to_half_pi {w : ℝ} (hw : w ≠ 0) :
    ∃ s : ℤ, |Real.arctan w - (s : ℝ) * (Real.pi / 2)| = Real.arctan (|w|⁻¹) := by
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · -- w < 0: arctan w = -π/2 + arctan(|w|⁻¹)
    refine ⟨-1, ?_⟩
    have habs : |w|⁻¹ = (-w)⁻¹ := by rw [abs_of_neg hneg]
    -- arctan(|w|⁻¹) = arctan((-w)⁻¹) = π/2 - arctan(-w) = π/2 + arctan w  (since -w>0)
    have hposw : 0 < -w := by linarith
    have hh : Real.arctan ((-w)⁻¹) = Real.pi / 2 - Real.arctan (-w) := Real.arctan_inv_of_pos hposw
    rw [Real.arctan_neg] at hh
    have hval : Real.arctan (|w|⁻¹) = Real.pi / 2 + Real.arctan w := by
      rw [habs, hh]; ring
    rw [hval]
    push_cast
    rw [abs_of_nonneg (by linarith [Real.neg_pi_div_two_lt_arctan w])]
    ring
  · -- w > 0: arctan w = π/2 - arctan(|w|⁻¹)
    refine ⟨1, ?_⟩
    have habs : |w|⁻¹ = w⁻¹ := by rw [abs_of_pos hpos]
    have hinv : Real.arctan w⁻¹ = Real.pi / 2 - Real.arctan w := Real.arctan_inv_of_pos hpos
    rw [habs, hinv]
    have hpp : 0 < Real.arctan w := by rw [Real.arctan_pos]; exact hpos
    push_cast
    rw [abs_of_nonpos (by nlinarith [Real.arctan_lt_pi_div_two w])]
    ring

/-- The analytic core of the `hxbig` case: if `A_n ≠ 0` and `n/2+1 < |B_n/A_n|`, then
`arg(P_n)` is within `2/n` of some integer multiple of `π/2`. -/
lemma arg_close_of_ratio_large {n : ℕ} (hn5 : 5 ≤ n) (hA : A n ≠ 0)
    (hxbig : (n : ℚ) / 2 + 1 < |x n|) :
    ∃ j' : ℤ, |Complex.arg ((P n : GaussianInt) : ℂ) - (j' : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ) := by
  -- Set up reals.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hre_val : ((P n : GaussianInt) : ℂ).re = (A n : ℝ) := by
    rw [GaussianInt.toComplex_def]; simp [A]
  have him_val : ((P n : GaussianInt) : ℂ).im = (B n : ℝ) := by
    rw [GaussianInt.toComplex_def]; simp [B]
  set Ar : ℝ := (A n : ℝ) with hAr
  set Br : ℝ := (B n : ℝ) with hBr
  have hAr_ne : Ar ≠ 0 := by rw [hAr]; exact_mod_cast hA
  -- |x n| = |Br/Ar|
  have hxabs : (|x n| : ℝ) = |Br / Ar| := by
    unfold x
    push_cast
    rw [hAr, hBr]
  -- |x n| > n/2 + 1 > 0 so B n ≠ 0.
  have hxbigR : (n : ℝ) / 2 + 1 < |Br / Ar| := by
    have h2 : ((n : ℝ) / 2 + 1) < |((x n : ℚ) : ℝ)| := by
      have hcast : (((n : ℚ) / 2 + 1 : ℚ) : ℝ) < ((|x n| : ℚ) : ℝ) := by
        exact_mod_cast hxbig
      rw [Rat.cast_abs] at hcast
      push_cast at hcast
      convert hcast using 2
    rwa [hxabs] at h2
  have hBr_ne : Br ≠ 0 := by
    intro h
    rw [h] at hxbigR
    simp at hxbigR
    have : (0:ℝ) ≤ (n:ℝ)/2 + 1 := by positivity
    linarith
  -- the small quantity: |Ar/Br| = 1/|Br/Ar| < 1/(n/2+1) = 2/(n+2) < 2/n
  have hsmall : |Ar / Br| < 2 / (n : ℝ) := by
    have hpos : (0:ℝ) < |Br / Ar| := by
      rw [abs_pos]; exact div_ne_zero hBr_ne hAr_ne
    have hinv_eq : |Ar / Br| = |Br / Ar|⁻¹ := by
      rw [← abs_inv]; congr 1; rw [inv_div]
    rw [hinv_eq]
    have hlb : (n : ℝ) / 2 + 1 < |Br / Ar| := hxbigR
    have h1 : |Br / Ar|⁻¹ < ((n : ℝ) / 2 + 1)⁻¹ := by
      apply inv_strictAnti₀ (by positivity) hlb
    have h2 : ((n : ℝ) / 2 + 1)⁻¹ ≤ 2 / (n : ℝ) := by
      rw [inv_eq_one_div]
      rw [div_le_div_iff₀ (by positivity) hnpos]
      nlinarith [hnpos]
    linarith
  -- w = im/re = Br/Ar, the tangent; the tail bound quantity is arctan(|w|⁻¹) = arctan(|Ar/Br|)
  set w : ℝ := Br / Ar with hw_def
  have hw_ne : w ≠ 0 := div_ne_zero hBr_ne hAr_ne
  have hwinv : |w|⁻¹ = |Ar / Br| := by
    rw [hw_def, ← abs_inv, inv_div]
  obtain ⟨s, hs⟩ := arctan_close_to_half_pi hw_ne
  -- arctan(|w|⁻¹) ≤ |w|⁻¹ < 2/n
  have htail_lt : Real.arctan (|w|⁻¹) < 2 / (n : ℝ) := by
    have h1 : Real.arctan (|w|⁻¹) ≤ |w|⁻¹ := arctan_le_self' (by positivity)
    rw [hwinv] at h1 ⊢
    linarith
  -- Now compute arg = arctan w (re > 0) or arctan w ± π (re < 0).
  rcases lt_or_gt_of_ne hAr_ne with hAneg | hApos
  · -- re < 0: arg z = arctan(im/re) ± π.
    have hzre : ((P n : GaussianInt) : ℂ).re < 0 := by rw [hre_val]; exact hAneg
    -- Use -z with positive re.
    set z : ℂ := ((P n : GaussianInt) : ℂ) with hz
    have hnegz_re : (-z).re = -Ar := by rw [Complex.neg_re, hre_val]
    have hnegz_re_pos : 0 < (-z).re := by rw [hnegz_re]; linarith
    have hnegz_arg : Complex.arg (-z) = Real.arctan ((-z).im / (-z).re) := by
      have hb : |Complex.arg (-z)| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hnegz_re_pos)
      have hb1 : -(Real.pi/2) < Complex.arg (-z) := by
        rw [abs_lt] at hb; exact hb.1
      have hb2 : Complex.arg (-z) < Real.pi/2 := by rw [abs_lt] at hb; exact hb.2
      have htan : Real.tan (Complex.arg (-z)) = (-z).im / (-z).re := Complex.tan_arg (-z)
      rw [← htan, Real.arctan_tan hb1 hb2]
    have hnegzim_re : (-z).im / (-z).re = w := by
      rw [Complex.neg_im, hnegz_re, him_val]; rw [hw_def, hAr, hBr]; ring
    rw [hnegzim_re] at hnegz_arg
    -- arg z relation to arg(-z)
    rcases lt_or_gt_of_ne hBr_ne with hBneg | hBpos
    · -- im < 0: arg(-z) = arg z + π  (from arg_neg_eq_arg_add_pi_of_im_neg with z.im<0)
      have hzim : z.im < 0 := by rw [him_val]; exact hBneg
      have hrel : Complex.arg (-z) = Complex.arg z + Real.pi := by
        have := Complex.arg_neg_eq_arg_add_pi_of_im_neg hzim
        -- this : arg(-z) = arg z + π
        exact this
      -- arg z = arctan w - π
      have hargz : Complex.arg z = Real.arctan w - Real.pi := by
        rw [hnegz_arg] at hrel; linarith
      refine ⟨s - 2, ?_⟩
      have heq : |Complex.arg z - ((s - 2 : ℤ) : ℝ) * (Real.pi / 2)|
          = |Real.arctan w - (s : ℝ) * (Real.pi / 2)| := by
        congr 1
        rw [hargz]; push_cast; ring
      rw [heq, hs]; exact htail_lt
    · -- im > 0: arg(-z) = arg z - π
      have hzim : 0 < z.im := by rw [him_val]; exact hBpos
      have hrel : Complex.arg (-z) = Complex.arg z - Real.pi :=
        Complex.arg_neg_eq_arg_sub_pi_of_im_pos hzim
      have hargz : Complex.arg z = Real.arctan w + Real.pi := by
        rw [hnegz_arg] at hrel; linarith
      refine ⟨s + 2, ?_⟩
      have heq : |Complex.arg z - ((s + 2 : ℤ) : ℝ) * (Real.pi / 2)|
          = |Real.arctan w - (s : ℝ) * (Real.pi / 2)| := by
        congr 1
        rw [hargz]; push_cast; ring
      rw [heq, hs]; exact htail_lt
  · -- re > 0: arg z = arctan(im/re) = arctan w
    have hzre_pos : 0 < ((P n : GaussianInt) : ℂ).re := by rw [hre_val]; exact hApos
    set z : ℂ := ((P n : GaussianInt) : ℂ) with hz
    have hargz : Complex.arg z = Real.arctan w := by
      have hb : |Complex.arg z| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre_pos)
      have hb1 : -(Real.pi/2) < Complex.arg z := by rw [abs_lt] at hb; exact hb.1
      have hb2 : Complex.arg z < Real.pi/2 := by rw [abs_lt] at hb; exact hb.2
      have htan : Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
      have hzim_re : z.im / z.re = w := by
        rw [hre_val, him_val, hw_def, hAr, hBr]
      rw [hzim_re] at htan
      rw [← htan, Real.arctan_tan hb1 hb2]
    refine ⟨s, ?_⟩
    rw [hargz, hs]; exact htail_lt

/-- Statement 2 (`lem:proximity`). For every $n \in E$ there exists an integer $j$ such that
$|a_n - j \pi/2| < 2/n$. -/
theorem lem_proximity {n : ℕ} (hn : n ∈ E) :
    ∃ j : ℤ, |a n - (j : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ) := by
  obtain ⟨hn5, hcase⟩ := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set φ : ℝ := Complex.arg ((P n : GaussianInt) : ℂ) with hφ
  -- From the angle identity, get a real integer shift.
  have hangle : ((a n : ℝ) : Real.Angle) = (((n : ℝ) * (Real.pi / 2) - φ : ℝ) : Real.Angle) := by
    rw [a_angle_eq]
    rw [Real.Angle.coe_sub, Real.Angle.natCast_mul_eq_nsmul]
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hangle
  obtain ⟨k, hk⟩ := hangle
  have hanval : a n = (n : ℝ) * (Real.pi / 2) - φ + 2 * Real.pi * k := by linarith
  -- Reduce to finding j' with |φ - j' π/2| small.
  suffices h : ∃ j' : ℤ, |φ - (j' : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ) by
    obtain ⟨j', hj'⟩ := h
    refine ⟨n + 4 * k - j', ?_⟩
    have : a n - ((n + 4 * k - j' : ℤ) : ℝ) * (Real.pi / 2)
        = -(φ - (j' : ℝ) * (Real.pi / 2)) := by
      push_cast
      rw [hanval]
      ring
    rw [this, abs_neg]
    exact hj'
  -- Now prove φ is close to a multiple of π/2.
  have hre_val : ((P n : GaussianInt) : ℂ).re = (A n : ℝ) := by
    rw [GaussianInt.toComplex_def]; simp [A]
  have him_val : ((P n : GaussianInt) : ℂ).im = (B n : ℝ) := by
    rw [GaussianInt.toComplex_def]; simp [B]
  have hB_ne : B n ≠ 0 ∨ A n ≠ 0 := by
    by_contra h
    push_neg at h
    apply P_ne_zero n
    rw [GaussianInt.toComplex_def]
    rw [show ((P n).re : ℂ) = ((A n : ℤ) : ℂ) from rfl, show ((P n).im : ℂ) = ((B n : ℤ) : ℂ) from rfl]
    rw [h.2, h.1]; simp
  rcases hcase with hA0 | hxbig
  · -- A n = 0: φ = ± π/2 exactly.
    have hBne : B n ≠ 0 := by
      rcases hB_ne with h | h
      · exact h
      · exact absurd hA0 h
    rcases lt_or_gt_of_ne hBne with hBneg | hBpos
    · -- B n < 0: φ = -(π/2)
      have : φ = -(Real.pi / 2) := by
        rw [hφ, Complex.arg_eq_neg_pi_div_two_iff]
        constructor
        · rw [hre_val, hA0]; simp
        · rw [him_val]; exact_mod_cast hBneg
      refine ⟨-1, ?_⟩
      rw [this]; push_cast; simp
      positivity
    · -- B n > 0: φ = π/2
      have : φ = Real.pi / 2 := by
        rw [hφ, Complex.arg_eq_pi_div_two_iff]
        constructor
        · rw [hre_val, hA0]; simp
        · rw [him_val]; exact_mod_cast hBpos
      refine ⟨1, ?_⟩
      rw [this]; push_cast; simp
      positivity
  · -- |x_n| large: delegate to the analytic sub-lemma.
    have hAne : A n ≠ 0 := by
      rcases hB_ne with _ | h
      · -- if A n = 0 the |x n| = |B/0| = 0, contradicting n/2+1 < |x n|; but hB_ne may give A n ≠ 0
        -- The `hxbig` hypothesis with A n = 0 gives |x n| = 0, contradiction handled below.
        by_contra hA0
        -- x n = B n / 0 = 0 in ℚ (division by zero), so |x n| = 0, contradicting hxbig.
        have : x n = 0 := by
          unfold x; rw [hA0]; simp
        rw [this] at hxbig; simp at hxbig
        have : (0 : ℚ) ≤ (n : ℚ) / 2 + 1 := by positivity
        linarith [hxbig]
      · exact h
    exact arg_close_of_ratio_large hn5 hAne hxbig

/-!
### Decomposition scaffold for Statement 3 (`cor:density`)

GOAL: `∃ C N₀, 0 < C ∧ ∀ N ≥ N₀, #(E ∩ [1,N]) ≤ C·log N`.

MATH ARGUMENT (rigorous outline):
1. By `lem_proximity`, every `n ∈ E` satisfies: `∃ j, |a_n - jπ/2| < 2/n`, i.e. `a_n` lies
   within `2/n` of the lattice `(π/2)·ℤ`.
2. The angle sum has the asymptotic `a_n = ∑_{k=1}^n arctan(1/k)`. Since `arctan(1/k) = 1/k + O(1/k³)`
   and `∑ 1/k = log n + γ + O(1/n)`, we have `a_n = log n + C₀ + o(1)` for an explicit constant
   `C₀` (`= γ + ∑(arctan(1/k) - 1/k)`). In particular `a_n` is strictly increasing with
   `a_{n+1} - a_n = arctan(1/(n+1)) ∈ (0, 1/(n+1)]`, and `a_n → ∞`.
3. KEY SPACING FACT: consecutive exceptional indices `n < n'` (both in E) with the SAME nearest
   lattice point are impossible once `n` is moderately large, because `a` increases by less than
   the tolerance; more importantly, distinct exceptional indices force `a_n` to visit distinct
   `(π/4)`-neighborhoods, and since `a_n` grows like `log n`, over `[1,N]` the value `a_N ≈ log N`
   sweeps an interval of length `≈ log N`, which the lattice `(π/2)ℤ` meets `O(log N)` times.
   Hence `#(E ∩ [1,N]) = O(log N)`.

FORMALIZATION PLAN (three named sub-lemmas, each a `sorry`):
   (a) `a_mono` / `a_growth`: `a` is monotone and `a_N ≤ log N + C₁` for an explicit `C₁`
       (upper bound via `arctan(1/k) ≤ 1/k` and `∑_{k=1}^N 1/k ≤ log N + 1`).
   (b) `E_near_lattice`: for `n ∈ E ∩ [1,N]`, `a_n` is within `2/n ≤ 2/5` of some multiple of
       `π/2` (from `lem_proximity`). The distinct exceptional indices land near distinct lattice
       points once `n ≥ 5` (separation `2/n < π/4` for `n ≥ 5`... actually need injectivity via
       monotonicity of `a`).
   (c) `count_lattice_hits`: the number of multiples `jπ/2` in `[a_1 - 1, a_N + 1] ⊆ [c, log N + C₁ + 1]`
       is at most `(2/π)(log N + C₂)`, giving the `O(log N)` count.

For this SKETCH phase we record the decomposition as `have`-sub-lemmas with `sorry`s and their
arguments; the constant assembly and the injectivity argument are the next phase's work.
-/

/-- Upper growth bound: `a_N ≤ log N + 1` for `N ≥ 1`. Uses `arctan(1/k) ≤ 1/k` (`Real.arctan_le_self`
applied to `1/k ≥ 0`) termwise, and the harmonic-sum bound `∑_{k=1}^N 1/k ≤ log N + 1`
(Mathlib: `Real.sum_range... `; look for `Real.add_pow_le_pow_mul_pow_of_sq_le` — actually the
harmonic bound is `Real.sum_div_le` / `Nat.log`... search `harmonic`, `Real.log`, `Finset.sum_range_succ`). -/
lemma a_growth {N : ℕ} (hN : 1 ≤ N) : a N ≤ Real.log N + 1 := by
  -- arctan y ≤ y for y ≥ 0 via le_tan
  have harctan : ∀ y : ℝ, 0 ≤ y → Real.arctan y ≤ y := by
    intro y hy
    have h1 : 0 ≤ Real.arctan y := Real.arctan_nonneg.mpr hy
    have h2 : Real.arctan y < Real.pi / 2 := Real.arctan_lt_pi_div_two y
    have := Real.le_tan h1 h2
    rwa [Real.tan_arctan] at this
  have hterm : a N ≤ ∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ)) := by
    unfold a
    apply Finset.sum_le_sum
    intro k hk
    apply harctan
    have : (0:ℝ) < k := by
      simp only [Finset.mem_Icc] at hk
      exact_mod_cast (by omega : 0 < k)
    positivity
  have hharm : (∑ k ∈ Finset.Icc 1 N, (1 / (k : ℝ))) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [one_div]
  have hb : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  rw [hharm] at hterm
  linarith

/-- `arctan t ≥ t/2` for `t ∈ [0,1]`. Proof: it suffices `tan(t/2) ≤ t`; with `s = t/2 ∈ [0,1/2]`,
`cos s ≥ 1 - s²/2 ≥ 1/2` and `sin s ≤ s`, so `tan s = sin s / cos s ≤ s / cos s ≤ 2s = t`. -/
lemma arctan_ge_half {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t / 2 ≤ Real.arctan t := by
  rcases eq_or_lt_of_le h0 with heq | hpos
  · simp [← heq]
  · set s : ℝ := t / 2 with hs
    have hs0 : 0 < s := by rw [hs]; linarith
    have hs_le : s ≤ 1 / 2 := by rw [hs]; linarith
    have hpi : (2 : ℝ) < Real.pi := by
      have := Real.pi_gt_three
      linarith
    have hs_lt_pi2 : s < Real.pi / 2 := by linarith
    have hs_gt_neg : -(Real.pi / 2) < s := by linarith
    have hcos : (1 : ℝ) / 2 ≤ Real.cos s := by
      have hc := Real.one_sub_sq_div_two_le_cos (x := s)
      nlinarith [hs_le, hs0]
    have hcos_pos : 0 < Real.cos s := by linarith
    have hsin : Real.sin s ≤ s := Real.sin_le (le_of_lt hs0)
    have htan : Real.tan s ≤ t := by
      rw [Real.tan_eq_sin_div_cos]
      rw [div_le_iff₀ hcos_pos]
      have ht2 : t = 2 * s := by rw [hs]; ring
      rw [ht2]
      nlinarith [hsin, hcos, hs0]
    have harc : Real.arctan (Real.tan s) = s := Real.arctan_tan hs_gt_neg hs_lt_pi2
    calc s = Real.arctan (Real.tan s) := harc.symm
      _ ≤ Real.arctan t := Real.arctan_mono htan
lemma a_lower_growth {N : ℕ} (hN : 1 ≤ N) : (1 / 2 : ℝ) * Real.log N ≤ a N := by
  -- termwise arctan(1/k) ≥ (1/2)(1/k), then ∑ (1/2)(1/k) = (1/2) harmonic N ≥ (1/2) log N.
  have hterm : (∑ k ∈ Finset.Icc 1 N, (1 / (2 * (k : ℝ)))) ≤ a N := by
    unfold a
    apply Finset.sum_le_sum
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have h0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    have h1 : (1 / (k : ℝ)) ≤ 1 := by
      rw [div_le_one hkpos]; exact hk1
    have hge := arctan_ge_half h0 h1
    have heq : (1 / (k : ℝ)) / 2 = 1 / (2 * (k : ℝ)) := by ring
    rw [heq] at hge
    exact hge
  have hsum_eq : (∑ k ∈ Finset.Icc 1 N, (1 / (2 * (k : ℝ))))
      = (1 / 2 : ℝ) * (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_div]; ring
  rw [hsum_eq] at hterm
  have hlog : Real.log N ≤ (harmonic N : ℝ) := by
    have h1 : Real.log ((N : ℝ) + 1) ≤ (harmonic N : ℝ) := by
      have h := log_add_one_le_harmonic N
      push_cast at h
      exact h
    have h2 : Real.log N ≤ Real.log (N + 1) := by
      apply Real.log_le_log
      · exact_mod_cast hN
      · linarith
    linarith
  nlinarith [hterm, hlog]

/-- Monotone strict increments: `a (n+1) = a n + arctan(1/(n+1))`, and `0 < arctan(1/(n+1)) ≤ 1/(n+1)`. -/
lemma a_succ (n : ℕ) : a (n + 1) = a n + Real.arctan (1 / ((n : ℝ) + 1)) := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  push_cast
  ring_nf

/-- Counting lattice points: the number of integers `j` with `jπ/2 ∈ [L, U]` is at most
`(2/π)(U - L) + 1`. This is `Nat.card` of an `Int` interval, bounded by its length. -/
lemma count_lattice_hits (L U : ℝ) (hLU : L ≤ U) :
    ((Finset.Icc ⌈L / (Real.pi / 2)⌉ ⌊U / (Real.pi / 2)⌋).card : ℝ)
      ≤ (2 / Real.pi) * (U - L) + 1 := by
  set p : ℝ := Real.pi / 2 with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; positivity
  set a : ℤ := ⌈L / p⌉ with ha_def
  set b : ℤ := ⌊U / p⌋ with hb_def
  rw [Int.card_Icc]
  -- key real bound
  have hkey : ((b : ℝ) + 1 - a) ≤ (2 / Real.pi) * (U - L) + 1 := by
    have hb_le : (b : ℝ) ≤ U / p := Int.floor_le _
    have ha_ge : L / p ≤ (a : ℝ) := Int.le_ceil _
    have hbma : (b : ℝ) - a ≤ U / p - L / p := by linarith
    have hdiv : U / p - L / p = (U - L) / p := by ring
    rw [hdiv] at hbma
    have hUL : (U - L) / p = (2 / Real.pi) * (U - L) := by
      rw [hp_def]; field_simp
    rw [hUL] at hbma
    linarith
  have hpos : 0 ≤ (2 / Real.pi) * (U - L) + 1 := by
    have : 0 ≤ U - L := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  rcases le_total 0 (b + 1 - a) with h | h
  · have hle : ((b + 1 - a).toNat : ℤ) = (b + 1 - a : ℤ) := Int.toNat_of_nonneg h
    have : ((b + 1 - a).toNat : ℝ) = ((b : ℝ) + 1 - a) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hle
      push_cast at this ⊢
      linarith [this]
    rw [this]; linarith
  · rw [Int.toNat_of_nonpos h]
    push_cast
    linarith

/-! ### Building blocks for `cor_density` assembly -/

/-- `a` is monotone: increments `arctan(1/(k+1))` are nonnegative. -/
lemma a_mono : Monotone a := by
  apply monotone_nat_of_le_succ
  intro n
  rw [a_succ]
  have : 0 ≤ Real.arctan (1 / ((n : ℝ) + 1)) := by
    apply Real.arctan_nonneg.mpr
    positivity
  linarith

/-- `a` is positive for `n ≥ 1`. -/
lemma a_pos {n : ℕ} (hn : 1 ≤ n) : 0 < a n := by
  have h1 : 0 < a 1 := by
    unfold a
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
    rw [Real.arctan_pos]; norm_num
  exact lt_of_lt_of_le h1 (a_mono hn)

/-- Strict lower bound on `a` increments over an interval: for `n₁ < n₂` (both ≥ 1),
`a n₂ - a n₁ ≥ (1/2) log((n₂+1)/(n₁+1))`. This is the integral-comparison bound. -/
lemma a_diff_log_lb {n₁ n₂ : ℕ} (h1 : 1 ≤ n₁) (h12 : n₁ ≤ n₂) :
    (1 / 2 : ℝ) * Real.log (((n₂ : ℝ) + 1) / ((n₁ : ℝ) + 1)) ≤ a n₂ - a n₁ := by
  -- a n = ∑ over Ioc 0 n (since Icc 1 n = Ioc 0 n)
  have hIcc : ∀ m : ℕ, a m = ∑ k ∈ Finset.Ioc 0 m, Real.arctan (1 / (k : ℝ)) := by
    intro m
    unfold a
    have : Finset.Icc 1 m = Finset.Ioc 0 m := by
      ext k
      simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
    rw [this]
  -- decompose: a n₂ - a n₁ = ∑ over Ioc n₁ n₂
  have hdecomp : a n₂ - a n₁ = ∑ k ∈ Finset.Ioc n₁ n₂, Real.arctan (1 / (k : ℝ)) := by
    rw [hIcc n₂, hIcc n₁]
    have := Finset.sum_Ioc_consecutive (fun k => Real.arctan (1 / (k : ℝ)))
      (Nat.zero_le n₁) h12
    linarith [this]
  rw [hdecomp]
  -- per-term bound: (1/2) log((k+1)/k) ≤ arctan(1/k) for k ≥ 1
  have hterm : ∀ k ∈ Finset.Ioc n₁ n₂,
      (1 / 2 : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) ≤ Real.arctan (1 / (k : ℝ)) := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    have hk1 : 1 ≤ k := by omega
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    -- arctan(1/k) ≥ (1/k)/2 = 1/(2k)
    have h0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    have h1le : (1 / (k : ℝ)) ≤ 1 := by rw [div_le_one hkpos]; exact hkR
    have hge := arctan_ge_half h0 h1le
    have heq : (1 / (k : ℝ)) / 2 = 1 / (2 * (k : ℝ)) := by ring
    rw [heq] at hge
    -- log((k+1)/k) ≤ 1/k
    have hdivpos : (0 : ℝ) < ((k : ℝ) + 1) / (k : ℝ) := by positivity
    have hlogsub : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hdivpos
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    have hval : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
      field_simp
      ring
    rw [hval] at hlogsub
    have hlogdiv : Real.log (((k : ℝ) + 1) / (k : ℝ)) = Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
      rw [Real.log_div (by positivity) (ne_of_gt hkpos)]
    rw [hlogdiv] at hlogsub
    -- combine: (1/2)(log(k+1)-log k) ≤ (1/2)(1/k) = 1/(2k) ≤ arctan(1/k)
    nlinarith [hlogsub, hge, hkpos]
  have hsum_le := Finset.sum_le_sum hterm
  -- telescope the LHS
  have htel : (∑ k ∈ Finset.Ioc n₁ n₂,
      (1 / 2 : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)))
      = (1 / 2 : ℝ) * Real.log (((n₂ : ℝ) + 1) / ((n₁ : ℝ) + 1)) := by
    -- first prove the inner telescoping identity by induction
    have htelraw : ∀ m : ℕ, n₁ ≤ m →
        (∑ k ∈ Finset.Ioc n₁ m, (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)))
          = Real.log ((m : ℝ) + 1) - Real.log ((n₁ : ℝ) + 1) := by
      intro m hm
      induction m with
      | zero =>
        omega
      | succ p ih =>
        rcases Nat.lt_or_ge n₁ (p + 1) with hlt | hge
        · -- n₁ ≤ p, use sum_Ioc_succ_top
          have hnp : n₁ ≤ p := by omega
          rw [Finset.sum_Ioc_succ_top hnp]
          rw [ih hnp]
          push_cast
          ring
        · -- n₁ = p + 1, empty sum
          have : n₁ = p + 1 := by omega
          subst this
          simp
    -- now assemble
    rw [← Finset.mul_sum]
    rw [htelraw n₂ h12]
    congr 1
    rw [Real.log_div (by positivity) (by positivity)]
  rw [htel] at hsum_le
  exact hsum_le

/-- For `n₁ < n₂` (both ≥ 1), a crude lower bound using only the smallest term:
`a n₂ - a n₁ ≥ (n₂ - n₁) · (1/(2 n₂))` since each of the `n₂-n₁` terms `arctan(1/k)`,
`n₁ < k ≤ n₂`, is `≥ arctan(1/n₂) ≥ 1/(2 n₂)`. -/
lemma a_diff_count_lb {n₁ n₂ : ℕ} (h1 : 1 ≤ n₁) (h12 : n₁ ≤ n₂) :
    ((n₂ - n₁ : ℕ) : ℝ) * (1 / (2 * (n₂ : ℝ))) ≤ a n₂ - a n₁ := by
  have hn2pos : (0 : ℝ) < (n₂ : ℝ) := by
    have : (1 : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast (le_trans h1 h12)
    linarith
  -- a n = ∑ over Ioc 0 n (since Icc 1 n = Ioc 0 n)
  have hIcc : ∀ m : ℕ, a m = ∑ k ∈ Finset.Ioc 0 m, Real.arctan (1 / (k : ℝ)) := by
    intro m
    unfold a
    have : Finset.Icc 1 m = Finset.Ioc 0 m := by
      ext k
      simp [Finset.mem_Icc, Finset.mem_Ioc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
    rw [this]
  -- decompose: a n₂ - a n₁ = ∑ over Ioc n₁ n₂
  have hdecomp : a n₂ - a n₁ = ∑ k ∈ Finset.Ioc n₁ n₂, Real.arctan (1 / (k : ℝ)) := by
    rw [hIcc n₂, hIcc n₁]
    have := Finset.sum_Ioc_consecutive (fun k => Real.arctan (1 / (k : ℝ)))
      (Nat.zero_le n₁) h12
    linarith [this]
  rw [hdecomp]
  -- lower bound each term by 1/(2 n₂)
  have hterm : ∀ k ∈ Finset.Ioc n₁ n₂, (1 / (2 * (n₂ : ℝ))) ≤ Real.arctan (1 / (k : ℝ)) := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    have hk1 : 1 ≤ k := by omega
    have hkn2 : k ≤ n₂ := hk.2
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hknR : (k : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hkn2
    -- arctan(1/k) ≥ (1/k)/2 = 1/(2k) ≥ 1/(2 n₂)
    have h0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    have h1le : (1 / (k : ℝ)) ≤ 1 := by rw [div_le_one hkpos]; exact hkR
    have hge := arctan_ge_half h0 h1le
    have heq : (1 / (k : ℝ)) / 2 = 1 / (2 * (k : ℝ)) := by ring
    rw [heq] at hge
    have hle : (1 / (2 * (n₂ : ℝ))) ≤ 1 / (2 * (k : ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith
    linarith
  have hsum_le := Finset.sum_le_sum hterm
  have hconst : (∑ _k ∈ Finset.Ioc n₁ n₂, (1 / (2 * (n₂ : ℝ))))
      = ((n₂ - n₁ : ℕ) : ℝ) * (1 / (2 * (n₂ : ℝ))) := by
    rw [Finset.sum_const, Nat.card_Ioc]
    rw [nsmul_eq_mul]
  rw [hconst] at hsum_le
  exact hsum_le

/-- The set `E ∩ [1,N]` is finite. -/
lemma E_inter_finite (N : ℕ) : (E ∩ Set.Icc 1 N).Finite :=
  (Set.finite_Icc 1 N).subset (Set.inter_subset_right)

/-- KEY SPACING LEMMA. If `5 ≤ n₁ ≤ n₂`, and both `a n₁`, `a n₂` are within `2/n` of the same
real `p`, then `n₂ ≤ n₁ + 47`. So any "fiber" (indices whose `a` lands near one point) spans a
bounded index range. Proof: `a n₂ - a n₁ < 4/n₁`; combined with `a_diff_log_lb` gives `n₂ < 6 n₁`
and with `a_diff_count_lb` gives `n₂ - n₁ < 48`. -/
lemma fiber_span {n₁ n₂ : ℕ} (h5 : 5 ≤ n₁) (h12 : n₁ ≤ n₂) {p : ℝ}
    (hb1 : |a n₁ - p| < 2 / (n₁ : ℝ)) (hb2 : |a n₂ - p| < 2 / (n₂ : ℝ)) :
    n₂ ≤ n₁ + 47 := by
  have h1 : 1 ≤ n₁ := by omega
  have hn1R : (5 : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast h5
  have hn1pos : (0 : ℝ) < (n₁ : ℝ) := by linarith
  have hn2pos : (0 : ℝ) < (n₂ : ℝ) := by
    have : (5 : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast (le_trans h5 h12)
    linarith
  have hn12R : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h12
  -- `2/n₂ ≤ 2/n₁`
  have hinv : (2 : ℝ) / (n₂ : ℝ) ≤ 2 / (n₁ : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) hn1pos hn12R
  -- a n₂ - a n₁ < 4/n₁
  have hdiff : a n₂ - a n₁ < 4 / (n₁ : ℝ) := by
    rw [abs_lt] at hb1 hb2
    have : a n₂ - a n₁ = (a n₂ - p) - (a n₁ - p) := by ring
    rw [this]
    have e1 : a n₂ - p < 2 / (n₂ : ℝ) := hb2.2
    have e2 : -(2 / (n₁ : ℝ)) < a n₁ - p := hb1.1
    have hfour : (4 : ℝ) / (n₁ : ℝ) = 2 / (n₁ : ℝ) + 2 / (n₁ : ℝ) := by ring
    rw [hfour]
    linarith
  have hdiff45 : a n₂ - a n₁ < 4 / 5 := by
    have : (4 : ℝ) / (n₁ : ℝ) ≤ 4 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn1R
    linarith
  -- Step 1: n₂ < 6 n₁ via log bound.
  have hlog_lb := a_diff_log_lb h1 h12
  have hlog_lt : Real.log (((n₂ : ℝ) + 1) / ((n₁ : ℝ) + 1)) < 8 / 5 := by
    have : (1 / 2 : ℝ) * Real.log (((n₂ : ℝ) + 1) / ((n₁ : ℝ) + 1)) < 4 / 5 := by
      linarith
    linarith
  have hratio_pos : (0 : ℝ) < ((n₂ : ℝ) + 1) / ((n₁ : ℝ) + 1) := by positivity
  have hexp : ((n₂ : ℝ) + 1) / ((n₁ : ℝ) + 1) < Real.exp (8 / 5) := by
    have := Real.log_lt_iff_lt_exp hratio_pos |>.mp hlog_lt
    -- log r < 8/5 ↔ r < exp(8/5)
    exact this
  have hexp_lt5 : Real.exp (8 / 5) < 5 := by
    -- e^{8/5} = (e^{4/5})^2; bound e^{4/5} < 2.2356 via exp_bound', square < 5.
    have h45 : Real.exp (4 / 5) ≤
        (∑ m ∈ Finset.range 7, (4/5:ℝ) ^ m / (m.factorial : ℝ))
          + (4/5:ℝ) ^ 7 * (7 + 1) / ((Nat.factorial 7 : ℝ) * 7) :=
      Real.exp_bound' (by norm_num) (by norm_num) (by norm_num : 0 < 7)
    have hsq : Real.exp (8 / 5) = Real.exp (4 / 5) * Real.exp (4 / 5) := by
      rw [← Real.exp_add]; norm_num
    have hpos45 : 0 < Real.exp (4 / 5) := Real.exp_pos _
    rw [hsq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h45
    norm_num at h45
    nlinarith [h45, hpos45]
  have hn2_lt : ((n₂ : ℝ) + 1) / ((n₁ : ℝ) + 1) < 5 := lt_trans hexp hexp_lt5
  have hn2_6 : (n₂ : ℝ) < 6 * (n₁ : ℝ) := by
    rw [div_lt_iff₀ (by positivity)] at hn2_lt
    nlinarith [hn1R]
  -- Step 2: count lower bound.
  have hcount_lb := a_diff_count_lb h1 h12
  have hcast : ((n₂ - n₁ : ℕ) : ℝ) = (n₂ : ℝ) - (n₁ : ℝ) := by
    rw [Nat.cast_sub h12]
  rw [hcast] at hcount_lb
  -- (n₂ - n₁)·(1/(2 n₂)) ≤ a n₂ - a n₁ < 4/n₁
  have hkey : ((n₂ : ℝ) - (n₁ : ℝ)) * (1 / (2 * (n₂ : ℝ))) < 4 / (n₁ : ℝ) := by
    linarith
  -- multiply out: (n₂ - n₁) n₁ < 8 n₂ < 48 n₁
  have hmul : ((n₂ : ℝ) - (n₁ : ℝ)) * (n₁ : ℝ) < 8 * (n₂ : ℝ) := by
    have hkey2 : ((n₂ : ℝ) - (n₁ : ℝ)) / (2 * (n₂ : ℝ)) < 4 / (n₁ : ℝ) := by
      rw [mul_one_div] at hkey; exact hkey
    rw [div_lt_div_iff₀ (by positivity) hn1pos] at hkey2
    nlinarith [hkey2, hn2pos]
  have hfinal : (n₂ : ℝ) - (n₁ : ℝ) < 48 := by
    nlinarith [hmul, hn2_6, hn1pos, hn1R]
  have : (n₂ : ℝ) < (n₁ : ℝ) + 48 := by linarith
  have hlt : n₂ < n₁ + 48 := by exact_mod_cast this
  omega

/-- Witness lattice index: for `n ∈ E`, `jwit n` is an integer with `|a n - jwit n · (π/2)| < 2/n`. -/
noncomputable def jwit (n : ℕ) : ℤ :=
  open Classical in
  if h : n ∈ E then (lem_proximity h).choose else 0

/-- Defining property of `jwit`. -/
lemma jwit_spec {n : ℕ} (hn : n ∈ E) :
    |a n - (jwit n : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ) := by
  have : jwit n = (lem_proximity hn).choose := by
    rw [jwit]; exact dif_pos hn
  rw [this]
  exact (lem_proximity hn).choose_spec

/-- FIBER CARD BOUND: within a finset `S` all of whose members are `≥ 5`, and where each `n ∈ S`
satisfies `|a n - jwit n · (π/2)| < 2/n`, every fiber `{n ∈ S | jwit n = b}` has at most `48`
elements. -/
lemma fiber_card_bound (S : Finset ℕ) (hS5 : ∀ n ∈ S, 5 ≤ n)
    (hSspec : ∀ n ∈ S, |a n - (jwit n : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ)) (b : ℤ) :
    (S.filter (fun n => jwit n = b)).card ≤ 48 := by
  set F := S.filter (fun n => jwit n = b) with hF
  rcases F.eq_empty_or_nonempty with hemp | hne
  · rw [hemp]; simp
  · obtain ⟨n₁, hn₁F, hn₁min⟩ := F.exists_min_image id hne
    have hn₁S : n₁ ∈ S := (Finset.mem_filter.mp hn₁F).1
    have hn₁b : jwit n₁ = b := (Finset.mem_filter.mp hn₁F).2
    have h5₁ : 5 ≤ n₁ := hS5 n₁ hn₁S
    have hsub : F ⊆ Finset.Icc n₁ (n₁ + 47) := by
      intro n hnF
      have hnS : n ∈ S := (Finset.mem_filter.mp hnF).1
      have hnb : jwit n = b := (Finset.mem_filter.mp hnF).2
      have h12 : n₁ ≤ n := hn₁min n hnF
      rw [Finset.mem_Icc]
      refine ⟨h12, ?_⟩
      have hb1 : |a n₁ - (b : ℝ) * (Real.pi / 2)| < 2 / (n₁ : ℝ) := by
        have := hSspec n₁ hn₁S; rwa [hn₁b] at this
      have hb2 : |a n - (b : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ) := by
        have := hSspec n hnS; rwa [hnb] at this
      exact fiber_span h5₁ h12 hb1 hb2
    calc F.card ≤ (Finset.Icc n₁ (n₁ + 47)).card := Finset.card_le_card hsub
      _ = 48 := by rw [Nat.card_Icc]; omega

/-- Statement 3 (`cor:density`). $\#(E \cap [1,N]) = O(\log N)$: there exist constants
$C > 0$ and $N_0$ such that for all $N \ge N_0$, $\#(E \cap [1,N]) \le C \log N$. -/
theorem cor_density :
    ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧ ∀ N : ℕ, N₀ ≤ N →
      ((E ∩ Set.Icc 1 N).ncard : ℝ) ≤ C * Real.log N := by
  refine ⟨200, 3, by norm_num, ?_⟩
  intro N hN3
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : (1 : ℝ) ≤ Real.log N := by
    have hmono : Real.log 3 ≤ Real.log N := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hN3
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      apply Real.log_le_log (Real.exp_pos 1)
      nlinarith [Real.exp_one_lt_three]
    linarith
  set S := (E_inter_finite N).toFinset with hS
  have hncard : (E ∩ Set.Icc 1 N).ncard = S.card := by
    rw [hS]; exact Set.ncard_eq_toFinset_card (E ∩ Set.Icc 1 N) (E_inter_finite N)
  rw [hncard]
  have hmemS : ∀ n, n ∈ S ↔ (n ∈ E ∧ 1 ≤ n ∧ n ≤ N) := by
    intro n
    rw [hS, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_Icc]
  have hS5 : ∀ n ∈ S, 5 ≤ n := by
    intro n hn
    exact ((hmemS n).mp hn).1.1
  have hSE : ∀ n ∈ S, n ∈ E := fun n hn => ((hmemS n).mp hn).1
  have hSspec : ∀ n ∈ S, |a n - (jwit n : ℝ) * (Real.pi / 2)| < 2 / (n : ℝ) :=
    fun n hn => jwit_spec (hSE n hn)
  set U : ℤ := ⌊(Real.log N + 7 / 5) * (2 / Real.pi)⌋ with hU
  set T : Finset ℤ := Finset.Icc 0 U with hT
  have hmaps : ∀ n ∈ S, jwit n ∈ T := by
    intro n hn
    have h5 : 5 ≤ n := hS5 n hn
    have hnR5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h5
    have hnRpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hnleN : n ≤ N := ((hmemS n).mp hn).2.2
    have hn1 : 1 ≤ n := by omega
    have hspec := hSspec n hn
    rw [abs_lt] at hspec
    have ha_up : a n ≤ Real.log N + 1 := by
      have hg := a_growth hn1
      have h2 : Real.log n ≤ Real.log N := by
        apply Real.log_le_log hnRpos; exact_mod_cast hnleN
      linarith
    have ha_lo : 0 < a n := a_pos hn1
    have h2n : 2 / (n : ℝ) ≤ 2 / 5 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR5
    have hpi2pos : (0 : ℝ) < Real.pi / 2 := by positivity
    have hjlow : -(2/5 : ℝ) < (jwit n : ℝ) * (Real.pi / 2) := by
      have := hspec.1; linarith
    have hjhigh : (jwit n : ℝ) * (Real.pi / 2) < Real.log N + 7/5 := by
      have := hspec.2; linarith
    rw [hT, Finset.mem_Icc]
    constructor
    · by_contra hneg
      push_neg at hneg
      have hjle : (jwit n : ℝ) ≤ -1 := by exact_mod_cast (by omega : jwit n ≤ -1)
      have hmul : (jwit n : ℝ) * (Real.pi / 2) ≤ -1 * (Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_right hjle (le_of_lt hpi2pos)
      nlinarith [hmul, hjlow, hpi]
    · rw [hU]
      apply Int.le_floor.mpr
      have hkey : (jwit n : ℝ) < (Real.log N + 7/5) * (2 / Real.pi) := by
        have hprod : (jwit n : ℝ) * (Real.pi / 2) < Real.log N + 7/5 := hjhigh
        have hexp : (Real.log N + 7/5) * (2 / Real.pi)
            = (Real.log N + 7/5) * 2 / Real.pi := by ring
        rw [hexp, lt_div_iff₀ hpi_pos]
        nlinarith [hprod, hpi_pos]
      linarith
  have hfiber := fiber_card_bound S hS5 hSspec
  have hcard : S.card ≤ 48 * T.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps 48 (fun b _ => hfiber b)
  have hTcard : (T.card : ℝ) ≤ (Real.log N + 7 / 5) * (2 / Real.pi) + 1 := by
    have hfl : (⌊(Real.log N + 7 / 5) * (2 / Real.pi)⌋ : ℝ)
        ≤ (Real.log N + 7 / 5) * (2 / Real.pi) := Int.floor_le _
    have hU0 : (0 : ℤ) ≤ ⌊(Real.log N + 7 / 5) * (2 / Real.pi)⌋ := by
      apply Int.le_floor.mpr; push_cast
      have : (0:ℝ) ≤ (Real.log N + 7/5) * (2/Real.pi) := by positivity
      simpa using this
    have hcardT : (T.card : ℤ) = ⌊(Real.log N + 7 / 5) * (2 / Real.pi)⌋ + 1 := by
      rw [hT, Int.card_Icc, hU]
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have : (T.card : ℝ) = (⌊(Real.log N + 7 / 5) * (2 / Real.pi)⌋ : ℝ) + 1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hcardT
      push_cast at this; exact this
    rw [this]
    linarith
  have hScardR : (S.card : ℝ) ≤ 48 * (T.card : ℝ) := by
    calc (S.card : ℝ) ≤ ((48 * T.card : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = 48 * (T.card : ℝ) := by push_cast; ring
  have hfin : 48 * ((Real.log N + 7 / 5) * (2 / Real.pi) + 1) ≤ 200 * Real.log N := by
    have hpiinv : 2 / Real.pi < 2 / 3 := by
      apply div_lt_div_of_pos_left (by norm_num) (by norm_num) hpi
    have hlogpos : (0:ℝ) < Real.log N := by linarith
    have hprod : (Real.log N + 7 / 5) * (2 / Real.pi) ≤ (Real.log N + 7 / 5) * (2 / 3) := by
      apply mul_le_mul_of_nonneg_left (le_of_lt hpiinv) (by linarith)
    nlinarith [hprod, hlogN]
  calc (S.card : ℝ) ≤ 48 * (T.card : ℝ) := hScardR
    _ ≤ 48 * ((Real.log N + 7 / 5) * (2 / Real.pi) + 1) := by
        apply mul_le_mul_of_nonneg_left hTcard (by norm_num)
    _ ≤ 200 * Real.log N := hfin
