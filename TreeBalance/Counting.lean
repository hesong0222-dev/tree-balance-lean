import TreeBalance.Basic

/-!
# The counting identity behind the PDA ↔ plane-tree reduction

Lemma `plane` of the balance paper: labelled plane binary trees with `n` leaves are counted
both as `(2n-3)!! * 2^(n-1)` (phylogenetic trees times orderings of the `n-1` internal
vertices) and as `n! * C_{n-1}` (plane trees times leaf labellings). We prove the identity
`(2n-3)!! * 2^(n-1) = n! * C_{n-1}` for all `n ≥ 1` (with the convention `(-1)!! = 1`,
which is what Lean's truncated subtraction gives for `n = 1`).
-/

open Nat

namespace TreeBalance

theorem doubleFactorial_mul_two_pow (m : ℕ) :
    (2 * m - 1)‼ * 2 ^ m = (m + 1)! * catalan m := by
  induction m with
  | zero => simp [Nat.doubleFactorial]
  | succ m ih =>
    have e : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [e, Nat.doubleFactorial_add_one, Nat.factorial_succ]
    calc (2 * m + 1) * (2 * m - 1)‼ * 2 ^ (m + 1)
        = 2 * (2 * m + 1) * ((2 * m - 1)‼ * 2 ^ m) := by ring
      _ = 2 * (2 * m + 1) * ((m + 1)! * catalan m) := by rw [ih]
      _ = (m + 1)! * (2 * (2 * m + 1) * catalan m) := by ring
      _ = (m + 1)! * ((m + 2) * catalan (m + 1)) := by rw [tb_catalan_succ_mul]
      _ = (m + 1 + 1) * (m + 1)! * catalan (m + 1) := by ring

/-- **Counting identity** (proof of Lemma `plane`): `(2n-3)!! · 2^(n-1) = n! · C_{n-1}`. -/
theorem pda_plane_count (n : ℕ) (hn : 1 ≤ n) :
    (2 * n - 3)‼ * 2 ^ (n - 1) = n ! * catalan (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : 2 * (m + 1) - 3 = 2 * m - 1 := by omega
  rw [e, Nat.add_sub_cancel]
  exact doubleFactorial_mul_two_pow m

end TreeBalance
