import TreeBalance.Basic

/-!
# Gosper certificate and the Colless root toll (balance paper, Lemma `gosper`, Prop. `toll`)

For `n ≥ 2` and `1 ≤ i ≤ n-1`:
`t_i = (2i-n) C_{i-1} C_{n-i-1}`, `U_i = i (2n-2i-1) C_{i-1} C_{n-i-1}`.
-/

open Finset

namespace TreeBalance

/-- `t_i = (2i - n) C_{i-1} C_{n-i-1}`. -/
def gT (n i : ℕ) : ℚ := (2 * (i : ℚ) - n) * Cq (i - 1) * Cq (n - i - 1)

/-- `U_i = i (2n - 2i - 1) C_{i-1} C_{n-i-1}`. -/
def gU (n i : ℕ) : ℚ := (i : ℚ) * (2 * n - 2 * i - 1) * Cq (i - 1) * Cq (n - i - 1)

/-- **Lemma `gosper`**: `U_{i+1} - U_i = t_i` for `1 ≤ i ≤ n-2`. -/
theorem gosper (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n - 2) : gU n (i + 1) - gU n i = gT n i := by
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = a + c + 3 := ⟨n - a - 3, by omega⟩
  have e1 : a + 1 + 1 - 1 = a + 1 := by omega
  have e2 : a + c + 3 - (a + 1 + 1) - 1 = c := by omega
  have e3 : a + 1 - 1 = a := by omega
  have e4 : a + c + 3 - (a + 1) - 1 = c + 1 := by omega
  simp only [gU, gT, e1, e2, e3, e4]
  have ha := Cq_succ a
  have hc := Cq_succ c
  push_cast
  linear_combination (2 * (c : ℚ) + 1) * Cq c * ha - (2 * (a : ℚ) + 1) * Cq a * hc

/-- The Colless root toll `a_n = Σ_{i=1}^{n-1} |2i - n| C_{i-1} C_{n-i-1}`
(equivalently `Σ_{i+j=n, i,j ≥ 1} |i-j| C_{i-1} C_{j-1}`). -/
def tollSum (n : ℕ) : ℚ := ∑ i ∈ Ico 1 n, |2 * (i : ℚ) - n| * Cq (i - 1) * Cq (n - i - 1)

/-- `ω_n = b_{⌊(n-1)/2⌋} b_{⌈(n-1)/2⌉}`. -/
def omegaSeq (n : ℕ) : ℚ := bq ((n - 1) / 2) * bq (n / 2)

theorem omegaSeq_even (m : ℕ) (hm : 1 ≤ m) : omegaSeq (2 * m) = bq m * bq (m - 1) := by
  unfold omegaSeq
  rw [show (2 * m - 1) / 2 = m - 1 by omega, show 2 * m / 2 = m by omega]
  ring

theorem omegaSeq_odd (m : ℕ) : omegaSeq (2 * m + 1) = bq m ^ 2 := by
  unfold omegaSeq
  rw [show (2 * m + 1 - 1) / 2 = m by omega, show (2 * m + 1) / 2 = m by omega]
  ring

lemma term_eq (n i : ℕ) : |2 * (i : ℚ) - n| * Cq (i - 1) * Cq (n - i - 1)
    = gT n i - 2 * (if 2 * i < n then gT n i else 0) := by
  unfold gT
  split_ifs with h
  · have h' : ((2 * i : ℕ) : ℚ) < n := by exact_mod_cast h
    push_cast at h'
    have hneg : 2 * (i : ℚ) - n < 0 := by linarith
    rw [abs_of_neg hneg]
    ring
  · have h' : (n : ℚ) ≤ ((2 * i : ℕ) : ℚ) := by exact_mod_cast (not_lt.mp h)
    push_cast at h'
    have hnn : 0 ≤ 2 * (i : ℚ) - n := by linarith
    rw [abs_of_nonneg hnn]
    ring

lemma gT_reflect (n i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ n - 1) : gT n (n - i) = -gT n i := by
  unfold gT
  rw [show n - (n - i) - 1 = i - 1 by omega, Nat.cast_sub (by omega : i ≤ n)]
  ring

lemma sum_gT (n : ℕ) : ∑ i ∈ Ico 1 n, gT n i = 0 := by
  have h : ∑ i ∈ Ico 1 n, gT n (n - i) = ∑ i ∈ Ico 1 n, gT n i := by
    rw [Finset.sum_Ico_reflect (gT n) 1 (by omega : n ≤ n + 1)]
    rw [show n + 1 - n = 1 by omega, show n + 1 - 1 = n by omega]
  have h2 : ∑ i ∈ Ico 1 n, gT n (n - i) = -∑ i ∈ Ico 1 n, gT n i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact gT_reflect n i hi.1 (by omega)
  linarith

lemma tele (n : ℕ) : ∀ k, 1 ≤ k → k ≤ n - 1 →
    ∑ i ∈ Ico 1 k, gT n i = gU n k - gU n 1 := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ k ih =>
    intro h1 h2
    by_cases hk : k = 0
    · subst hk
      simp
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k), ih (by omega) (by omega),
        ← gosper n k (by omega) (by omega)]
      ring

lemma gU_one (n : ℕ) (hn : 2 ≤ n) : gU n 1 = (2 * (n : ℚ) - 3) * Cq (n - 2) := by
  unfold gU
  rw [show n - 1 - 1 = n - 2 by omega, show (1 : ℕ) - 1 = 0 by rfl]
  simp only [Cq, catalan_zero, Nat.cast_one]
  ring

lemma two_gU_half (n : ℕ) (hn : 2 ≤ n) : 2 * gU n ((n + 1) / 2) = omegaSeq n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e1 : (2 * (k + 1) + 1) / 2 = k + 1 := by omega
    have e2 : k + 1 - 1 = k := by omega
    have e3 : 2 * (k + 1) - (k + 1) - 1 = k := by omega
    have e4 : (2 * (k + 1) - 1) / 2 = k := by omega
    have e5 : 2 * (k + 1) / 2 = k + 1 := by omega
    simp only [gU, omegaSeq, e1, e2, e3, e4, e5, bq_eq]
    have hk := Cq_succ k
    push_cast
    linear_combination (-((k : ℚ) + 1) * Cq k) * hk
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e1 : (2 * (k + 1) + 1 + 1) / 2 = k + 2 := by omega
    have e2 : k + 2 - 1 = k + 1 := by omega
    have e3 : 2 * (k + 1) + 1 - (k + 2) - 1 = k := by omega
    have e4 : (2 * (k + 1) + 1 - 1) / 2 = k + 1 := by omega
    have e5 : (2 * (k + 1) + 1) / 2 = k + 1 := by omega
    simp only [gU, omegaSeq, e1, e2, e3, e4, e5, bq_eq]
    have hk := Cq_succ k
    push_cast
    linear_combination (-((k : ℚ) + 2) * Cq (k + 1)) * hk

/-- **Proposition `toll`** (first form): for `n ≥ 2`,
`Σ_{i=1}^{n-1} |2i-n| C_{i-1} C_{n-i-1} = 2(2n-3) C_{n-2} - ω_n`. -/
theorem toll (n : ℕ) (hn : 2 ≤ n) :
    tollSum n = 2 * (2 * (n : ℚ) - 3) * Cq (n - 2) - omegaSeq n := by
  have hsplit : tollSum n = ∑ i ∈ Ico 1 n, gT n i
      - 2 * ∑ i ∈ Ico 1 n, (if 2 * i < n then gT n i else 0) := by
    unfold tollSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => term_eq n i)
  have hfilter : ∑ i ∈ Ico 1 n, (if 2 * i < n then gT n i else 0)
      = ∑ i ∈ Ico 1 ((n + 1) / 2), gT n i := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hsplit, hfilter, sum_gT, tele n ((n + 1) / 2) (by omega) (by omega), gU_one n hn,
    ← two_gU_half n hn]
  ring

/-- `b_{n-1} = 2(2n-3) C_{n-2}` for `n ≥ 2`. -/
theorem bq_pred (n : ℕ) (hn : 2 ≤ n) : bq (n - 1) = 2 * (2 * (n : ℚ) - 3) * Cq (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, bq_eq]
  have := Cq_succ k
  push_cast
  linear_combination this

/-- **Proposition `toll`** (second form): `a_n = b_{n-1} - ω_n` for `n ≥ 2`. -/
theorem toll_eq_b_sub_omega (n : ℕ) (hn : 2 ≤ n) : tollSum n = bq (n - 1) - omegaSeq n := by
  rw [toll n hn, bq_pred n hn]

end TreeBalance
