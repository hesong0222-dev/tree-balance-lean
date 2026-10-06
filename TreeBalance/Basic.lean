import Mathlib

/-!
# Common definitions

`Cq k` is the Catalan number `C_k` and `bq k` the central binomial coefficient
`b_k = binom(2k, k)`, both viewed as rationals.
-/

namespace TreeBalance

/-- The Catalan number `C_k` as a rational number. -/
def Cq (k : ℕ) : ℚ := (catalan k : ℚ)

/-- The central binomial coefficient `b_k = binom(2k,k)` as a rational number. -/
def bq (k : ℕ) : ℚ := (Nat.centralBinom k : ℚ)

/-- `(k+2) C_{k+1} = 2 (2k+1) C_k`. -/
theorem tb_catalan_succ_mul (k : ℕ) :
    (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 : (k + 2) * catalan (k + 1) = Nat.centralBinom (k + 1) :=
    succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 : (k + 1) * catalan k = Nat.centralBinom k := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1)
  rw [h1, h3, ← h2]
  ring

theorem Cq_succ (k : ℕ) : ((k : ℚ) + 2) * Cq (k + 1) = 2 * (2 * k + 1) * Cq k := by
  unfold Cq
  exact_mod_cast tb_catalan_succ_mul k

theorem bq_eq (k : ℕ) : bq k = ((k : ℚ) + 1) * Cq k := by
  unfold bq Cq
  exact_mod_cast (succ_mul_catalan_eq_centralBinom k).symm

theorem bq_succ (k : ℕ) : ((k : ℚ) + 1) * bq (k + 1) = 2 * (2 * k + 1) * bq k := by
  unfold bq
  exact_mod_cast Nat.succ_mul_centralBinom_succ k

end TreeBalance
