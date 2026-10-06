import Mathlib

/-!
# Transfer paper, `β = -1`: the Laplace exponent and the Beta-mixture normalisation

At `β = -1` the dislocation density is `x^{-1}(1-x)^{-1}`, and the transfer paper uses:

* `φ_{-1}(m) = ∫_0^1 (1 - s^m) (1-s)^{-1} ds = h_m` (Lemma `phi`, `φ_{-1}(m) = h_m`);
* the normalising constant of Lemma `mix`:
  `Z_n = ∫_0^1 x^{-1}(1-x)^{-1} (1 - x^n - (1-x)^n) dx = 2 Φ_n = 2 h_{n-1}`.

Here `h_m = harmonic m = Σ_{i ≤ m} 1/i`. The integrands are written with division; at the
endpoints Lean's convention `t / 0 = 0` changes the integrand only on a null set.
-/

open MeasureTheory

namespace TreeBalance

lemma integral_pow_01 (k : ℕ) : ∫ x in (0 : ℝ)..1, x ^ k = 1 / ((k : ℝ) + 1) := by
  rw [integral_pow]
  simp

lemma integral_one_sub_pow_01 (k : ℕ) : ∫ x in (0 : ℝ)..1, (1 - x) ^ k = 1 / ((k : ℝ) + 1) := by
  have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ k) (a := 0) (b := 1)
    (d := 1)
  rw [h]
  simp only [sub_zero, sub_self]
  exact integral_pow_01 k

lemma integral_geom_01 (n : ℕ) :
    ∫ x in (0 : ℝ)..1, ∑ i ∈ Finset.range n, x ^ i = (harmonic n : ℝ) := by
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => (continuous_pow i).intervalIntegrable 0 1)]
  simp only [integral_pow_01]
  simp [harmonic, one_div]

lemma integral_geom_one_sub_01 (n : ℕ) :
    ∫ x in (0 : ℝ)..1, ∑ i ∈ Finset.range n, (1 - x) ^ i = (harmonic n : ℝ) := by
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => (by fun_prop : Continuous fun x : ℝ => (1 - x) ^ i).intervalIntegrable 0 1)]
  simp only [integral_one_sub_pow_01]
  simp [harmonic, one_div]

/-- `φ_{-1}(m) = ∫_0^1 (1 - s^m) / (1 - s) ds = h_m`. -/
theorem phi_neg_one (m : ℕ) : ∫ s in (0 : ℝ)..1, (1 - s ^ m) / (1 - s) = (harmonic m : ℝ) := by
  rw [← integral_geom_01 m]
  apply intervalIntegral.integral_congr_ae
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (1 : ℝ))
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  rw [Set.mem_singleton_iff]
  by_contra hne
  apply hx
  intro _
  have h1 : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2 : (x - 1) ≠ 0 := sub_ne_zero.mpr hne
  rw [geom_sum_eq hne, div_eq_div_iff h1 h2]
  ring

/-- **Normalisation of the Beta mixture at `β = -1`** (Lemma `mix`, `Z_n = 2 Φ_n`):
`∫_0^1 (1 - x^n - (1-x)^n) / (x (1-x)) dx = 2 h_{n-1}` for `n ≥ 1`. -/
theorem beta_neg_one_normalisation (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..1, (1 - x ^ n - (1 - x) ^ n) / (x * (1 - x)) = 2 * (harmonic (n - 1) : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hpoly : ∫ x in (0 : ℝ)..1, (1 - x ^ (k + 1) - (1 - x) ^ (k + 1)) / (x * (1 - x))
      = ∫ x in (0 : ℝ)..1, ((∑ i ∈ Finset.range (k + 1), x ^ i)
          + (∑ i ∈ Finset.range (k + 1), (1 - x) ^ i) - x ^ k - (1 - x) ^ k) := by
    apply intervalIntegral.integral_congr_ae
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_
      ((Set.toFinite ({0, 1} : Set ℝ)).measure_zero _)
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hne
    push Not at hne
    apply hx
    intro _
    have hx0 : x ≠ 0 := hne.1
    have hx1 : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne.2)
    rw [div_eq_iff (mul_ne_zero hx0 hx1)]
    have h1 := geom_sum_mul_neg x (k + 1)
    have h2 := geom_sum_mul_neg (1 - x) (k + 1)
    linear_combination (-x) * h1 + (-(1 - x)) * h2
  rw [hpoly, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
    intervalIntegral.integral_add, integral_geom_01, integral_geom_one_sub_01, integral_pow_01,
    integral_one_sub_pow_01]
  · simp only [Nat.add_sub_cancel, harmonic_succ]
    push_cast
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-! ### Lemma `mix` at `β = -1`: the Beta-mixture representation of `p_{n,j}` -/

open Nat in
/-- Beta integral with natural exponents: `∫_0^1 x^a (1-x)^b dx = a! b! / (a+b+1)!`. -/
theorem beta_integral_nat (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b = ((a ! : ℝ) * (b ! : ℝ)) / ((a + b + 1)! : ℝ) := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [integral_pow_01, Nat.factorial_succ]
    have ha : (a ! : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  | succ b ih =>
    have hsplit : ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1)
        = (∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b)
          - ∫ x in (0 : ℝ)..1, x ^ (a + 1) * (1 - x) ^ b := by
      rw [← intervalIntegral.integral_sub]
      · congr 1
        ext x
        ring
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
    rw [hsplit, ih a, ih (a + 1)]
    rw [show a + 1 + b + 1 = a + b + 1 + 1 by omega, show a + (b + 1) + 1 = a + b + 1 + 1 by omega,
      Nat.factorial_succ (a + b + 1), Nat.factorial_succ a, Nat.factorial_succ b]
    have hF : ((a + b + 1)! : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_sub_div _ _ hF (by positivity), div_eq_div_iff (by positivity) (by positivity)]
    ring

/-- The `β = -1` splitting rule `p_{n,j} = n / (2 h_{n-1} j (n-j))`. -/
noncomputable def pNegOne (n j : ℕ) : ℝ := n / (2 * (harmonic (n - 1) : ℝ) * j * (n - j))

open Nat in
/-- `binom(n,j) ∫_0^1 x^{j-1} (1-x)^{n-j-1} dx = n / (j (n-j))` for `1 ≤ j ≤ n-1`. -/
theorem choose_mul_beta_integral (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n - 1) :
    (n.choose j : ℝ) * ∫ x in (0 : ℝ)..1, x ^ (j - 1) * (1 - x) ^ (n - j - 1)
      = n / (j * (n - j)) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = a + c + 2 := ⟨n - a - 2, by omega⟩
  have hden : ((a + 1 : ℕ) : ℝ) * (((a + c + 2 : ℕ) : ℝ) - ((a + 1 : ℕ) : ℝ)) ≠ 0 := by
    push_cast
    ring_nf
    positivity
  rw [show a + 1 - 1 = a by omega, show a + c + 2 - (a + 1) - 1 = c by omega, beta_integral_nat,
    eq_div_iff hden]
  have hch := Nat.choose_mul_factorial_mul_factorial (show a + 1 ≤ a + c + 2 by omega)
  rw [show a + c + 2 - (a + 1) = c + 1 by omega] at hch
  have hch' : ((a + c + 2).choose (a + 1) : ℝ) * ((a + 1)! : ℝ) * ((c + 1)! : ℝ)
      = ((a + c + 2)! : ℝ) := by exact_mod_cast hch
  have e2 : ((a + c + 2)! : ℝ) = ((a : ℝ) + c + 2) * ((a + c + 1)! : ℝ) := by
    rw [show a + c + 2 = (a + c + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have ea : ((a + 1)! : ℝ) = ((a : ℝ) + 1) * (a ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have ec : ((c + 1)! : ℝ) = ((c : ℝ) + 1) * (c ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [ea, ec, e2] at hch'
  have hF : ((a + c + 1)! : ℝ) ≠ 0 := by positivity
  rw [mul_div_assoc', div_mul_eq_mul_div, div_eq_iff hF]
  push_cast
  linear_combination hch'

/-- **Lemma `mix` at `β = -1`**: `p_{n,j} = (1 / (2 Φ_n)) binom(n,j) ∫_0^1 x^{j+β} (1-x)^{n-j+β} dx`
with `β = -1` and `Φ_n = φ_{-1}(n-1) = h_{n-1}`. -/
theorem pNegOne_mixture (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n - 1) :
    pNegOne n j = 1 / (2 * (harmonic (n - 1) : ℝ))
      * ((n.choose j : ℝ) * ∫ x in (0 : ℝ)..1, x ^ (j - 1) * (1 - x) ^ (n - j - 1)) := by
  rw [choose_mul_beta_integral n j hj hjn, pNegOne, div_mul_div_comm, one_mul, mul_assoc]

lemma sum_one_div_Ico (n : ℕ) : ∑ j ∈ Finset.Ico 1 n, 1 / (j : ℝ) = (harmonic (n - 1) : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  unfold harmonic
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The `β = -1` rule is a probability distribution: `Σ_{j=1}^{n-1} p_{n,j} = 1` (`n ≥ 2`). -/
theorem sum_pNegOne (n : ℕ) (hn : 2 ≤ n) : ∑ j ∈ Finset.Ico 1 n, pNegOne n j = 1 := by
  have hpos : (0 : ℝ) < harmonic (n - 1) := by exact_mod_cast harmonic_pos (by omega)
  have hh : (harmonic (n - 1) : ℝ) ≠ 0 := hpos.ne'
  have hpt : ∀ j ∈ Finset.Ico 1 n, pNegOne n j
      = 1 / (2 * (harmonic (n - 1) : ℝ)) * (1 / (j : ℝ) + 1 / ((n - j : ℕ) : ℝ)) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    unfold pNegOne
    rw [Nat.cast_sub hj.2.le]
    have h1 : (j : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
      linarith
    have h2 : (n : ℝ) - j ≠ 0 := by
      have : (j : ℝ) < n := by exact_mod_cast hj.2
      linarith
    rw [div_add_div _ _ h1 h2, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hh) h1) h2)
        (mul_ne_zero (mul_ne_zero two_ne_zero hh) (mul_ne_zero h1 h2))]
    ring
  have hrefl := Finset.sum_Ico_reflect (fun i : ℕ => 1 / (i : ℝ)) 1 (Nat.le_succ n)
  rw [show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega] at hrefl
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_add_distrib, hrefl,
    sum_one_div_Ico, div_mul_eq_mul_div, one_mul, div_eq_one_iff_eq (mul_ne_zero two_ne_zero hh)]
  ring

end TreeBalance
