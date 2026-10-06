import TreeBalance.Basic

/-!
# The convolution identity `Σ_{k=0}^{N} b_k b_{N-k} = 4^N`

Proof without generating functions: with `q_N = Σ_{k+l=N} b_k b_l`, the recurrence
`(k+1) b_{k+1} = 2(2k+1) b_k` and the symmetry `k ↔ l` give `(N+1) q_{N+1} = 4 (N+1) q_N`.
-/

open Finset

namespace TreeBalance

/-- `q_N = Σ_{k+l=N} b_k b_l`. -/
def bconv (N : ℕ) : ℚ := ∑ p ∈ antidiagonal N, bq p.1 * bq p.2

lemma sum_fst_mul (N : ℕ) :
    2 * ∑ p ∈ antidiagonal N, (p.1 : ℚ) * bq p.1 * bq p.2 = N * bconv N := by
  have hs : ∑ p ∈ antidiagonal N, (p.1 : ℚ) * bq p.1 * bq p.2
      = ∑ p ∈ antidiagonal N, (p.2 : ℚ) * bq p.1 * bq p.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    apply Finset.sum_congr rfl
    intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have hN : ∑ p ∈ antidiagonal N, ((p.1 : ℚ) + p.2) * bq p.1 * bq p.2 = N * bconv N := by
    unfold bconv
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h' : (p.1 : ℚ) + p.2 = N := by exact_mod_cast hp
    rw [h']
    ring
  have hadd : ∑ p ∈ antidiagonal N, ((p.1 : ℚ) + p.2) * bq p.1 * bq p.2
      = ∑ p ∈ antidiagonal N, (p.1 : ℚ) * bq p.1 * bq p.2
        + ∑ p ∈ antidiagonal N, (p.2 : ℚ) * bq p.1 * bq p.2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  linarith

lemma bconv_succ (N : ℕ) : bconv (N + 1) = 4 * bconv N := by
  have h1 := sum_fst_mul (N + 1)
  have h0 := sum_fst_mul N
  have h2 : ∑ p ∈ antidiagonal (N + 1), (p.1 : ℚ) * bq p.1 * bq p.2
      = ∑ p ∈ antidiagonal N, ((p.1 : ℚ) + 1) * bq (p.1 + 1) * bq p.2 := by
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp
  have h3 : ∑ p ∈ antidiagonal N, ((p.1 : ℚ) + 1) * bq (p.1 + 1) * bq p.2
      = ∑ p ∈ antidiagonal N, (2 * (2 * (p.1 : ℚ) + 1)) * bq p.1 * bq p.2 := by
    apply Finset.sum_congr rfl
    intro p _
    rw [bq_succ]
  have h4 : ∑ p ∈ antidiagonal N, (2 * (2 * (p.1 : ℚ) + 1)) * bq p.1 * bq p.2
      = 2 * (2 * ∑ p ∈ antidiagonal N, (p.1 : ℚ) * bq p.1 * bq p.2) + 2 * bconv N := by
    unfold bconv
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have key : ((N : ℚ) + 1) * bconv (N + 1) = ((N : ℚ) + 1) * (4 * bconv N) := by
    push_cast at h1
    rw [← h1, h2, h3, h4, h0]
    ring
  exact mul_left_cancel₀ (by positivity) key

theorem bconv_eq (N : ℕ) : bconv N = 4 ^ N := by
  induction N with
  | zero => simp [bconv, bq]
  | succ N ih => rw [bconv_succ, ih, pow_succ]; ring

/-- **Convolution identity** `Σ_{k=0}^{N} b_k b_{N-k} = 4^N` (over `ℕ`). -/
theorem sum_centralBinom_mul_centralBinom (N : ℕ) :
    ∑ p ∈ antidiagonal N, Nat.centralBinom p.1 * Nat.centralBinom p.2 = 4 ^ N := by
  have h := bconv_eq N
  unfold bconv bq at h
  exact_mod_cast h

end TreeBalance
