import TreeBalance.Toll
import TreeBalance.Convolution

/-!
# The total Colless index over plane binary trees (balance paper, Theorem `mean`)

Plane binary trees are Mathlib's `BinaryTree Unit` (`nil` is a leaf); a tree with `m`
internal nodes has `m + 1` leaves. The Colless index adds `|n_L - n_R|` over all internal
vertices. We prove, for the total `T_n` of the Colless index over the `C_{n-1}` plane trees
with `n` leaves,

* the recursion `T_n = Σ_{i+j=n} (|i-j| C_{i-1} C_{j-1} + 2 T_i C_{j-1})`,
* the closed form `T_n = 4^{n-1} - Z_{n-1}`, `Z_N = Σ_{j=0}^{N} b_{⌊j/2⌋} b_{⌈j/2⌉} b_{N-j}`,
* hence the uniform average over plane trees is `(4^{n-1} - Z_{n-1}) / C_{n-1}`.

The proof of the closed form follows the paper (`F = G / (1 - 2B)`) inside `ℚ⟦X⟧`, using
Proposition `toll` and the convolution identity `Σ b_k b_{N-k} = 4^N`.
-/

open Finset PowerSeries BinaryTree

namespace TreeBalance

/-- The Colless index: `Σ_v |n_L(v) - n_R(v)|` over internal vertices. -/
def colless : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l r => Int.natAbs ((l.numLeaves : ℤ) - r.numLeaves) + colless l + colless r

/-- The plane binary trees with `n` leaves. -/
def planeTrees (n : ℕ) : Finset (BinaryTree Unit) := treesOfNumNodesEq (n - 1)

theorem mem_planeTrees {n : ℕ} (hn : 1 ≤ n) {x : BinaryTree Unit} :
    x ∈ planeTrees n ↔ x.numLeaves = n := by
  simp only [planeTrees, mem_treesOfNumNodesEq, numLeaves_eq_numNodes_succ]
  omega

theorem card_planeTrees (n : ℕ) : (planeTrees n).card = catalan (n - 1) :=
  treesOfNumNodesEq_card_eq_catalan _

/-- `T_n`: the total Colless index over all plane binary trees with `n` leaves. -/
def collessTotal (n : ℕ) : ℕ := ∑ x ∈ planeTrees n, colless x

/-- Auxiliary: the total over trees with `m` internal nodes (`m + 1` leaves). -/
def collessTot (m : ℕ) : ℕ := ∑ x ∈ treesOfNumNodesEq m, colless x

theorem collessTotal_succ (m : ℕ) : collessTotal (m + 1) = collessTot m := by
  simp only [collessTotal, collessTot, planeTrees, Nat.add_sub_cancel]

theorem collessTot_succ (m : ℕ) : collessTot (m + 1) = ∑ p ∈ antidiagonal m,
    (Int.natAbs ((p.1 : ℤ) - p.2) * catalan p.1 * catalan p.2
      + collessTot p.1 * catalan p.2 + catalan p.1 * collessTot p.2) := by
  unfold collessTot
  rw [treesOfNumNodesEq_succ, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ _
    simp only [pairwiseNode, Finset.sum_map, Finset.sum_product]
    have key : ∀ l ∈ treesOfNumNodesEq i, ∀ r ∈ treesOfNumNodesEq j,
        colless (BinaryTree.node () l r) = Int.natAbs ((i : ℤ) - j) + colless l + colless r := by
      intro l hl r hr
      rw [mem_treesOfNumNodesEq] at hl hr
      have e : ((l.numLeaves : ℕ) : ℤ) - (r.numLeaves : ℕ) = (i : ℤ) - j := by
        rw [numLeaves_eq_numNodes_succ, numLeaves_eq_numNodes_succ, hl, hr]
        push_cast
        ring
      simp only [colless, e]
    trans ∑ l ∈ treesOfNumNodesEq i, ∑ r ∈ treesOfNumNodesEq j,
      (Int.natAbs ((i : ℤ) - j) + colless l + colless r)
    · apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro r hr
      exact key l hl r hr
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      treesOfNumNodesEq_card_eq_catalan, ← Finset.mul_sum]
    ring
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
    aesop

/-- **Recursion** for the Colless total, in the paper's form
`T_n = Σ_{i+j=n} (|i-j| C_{i-1} C_{j-1} + 2 T_i C_{j-1})` with `n = m + 2`, `i = p.1 + 1`,
`j = p.2 + 1`. -/
theorem collessTotal_rec (m : ℕ) : collessTotal (m + 2) = ∑ p ∈ antidiagonal m,
    (Int.natAbs ((p.1 : ℤ) - p.2) * catalan p.1 * catalan p.2
      + 2 * collessTotal (p.1 + 1) * catalan p.2) := by
  rw [show collessTotal (m + 2) = collessTot (m + 1) from collessTotal_succ (m + 1)]
  simp only [collessTotal_succ]
  rw [collessTot_succ]
  have hs : ∑ p ∈ antidiagonal m, catalan p.1 * collessTot p.2
      = ∑ p ∈ antidiagonal m, collessTot p.1 * catalan p.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    apply Finset.sum_congr rfl
    intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have h2 : ∑ p ∈ antidiagonal m, 2 * collessTot p.1 * catalan p.2
      = ∑ p ∈ antidiagonal m, collessTot p.1 * catalan p.2
        + ∑ p ∈ antidiagonal m, collessTot p.1 * catalan p.2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hs, h2]
  ring

/-! ### Generating functions in `ℚ⟦X⟧` -/

/-- `Σ b_n X^n` (that is, `(1-4z)^{-1/2}`). -/
noncomputable def SB : PowerSeries ℚ := PowerSeries.mk bq
/-- `Σ C_n X^n`. -/
noncomputable def SC : PowerSeries ℚ := PowerSeries.mk Cq
/-- `Σ 4^n X^n`. -/
noncomputable def G4 : PowerSeries ℚ := PowerSeries.mk fun n => (4 : ℚ) ^ n
/-- `W = 1 - 2 X C(X)`, i.e. `1 - 2B = √(1-4z)`. -/
noncomputable def W : PowerSeries ℚ := 1 - 2 * X * SC

theorem SB_sq : SB * SB = G4 := by
  ext n
  rw [coeff_mul]
  simp only [SB, G4, coeff_mk]
  have h := bconv_eq n
  unfold bconv at h
  exact h

theorem SC_eq : SC = 1 + X * SC ^ 2 := by
  ext n
  cases n with
  | zero => simp [SC, Cq]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, pow_two, coeff_mul]
    simp only [SC, coeff_mk, Cq, coeff_one]
    rw [catalan_succ']
    simp

theorem W_sq : W ^ 2 = 1 - 4 * X := by
  have h := SC_eq
  unfold W
  linear_combination (-4 * X) * h

theorem G4_mul : G4 * (1 - 4 * X) = 1 := by
  have h4 : (4 : PowerSeries ℚ) = C (4 : ℚ) := (map_ofNat (C (R := ℚ)) 4).symm
  ext n
  rw [h4, mul_sub, mul_one, map_sub, show G4 * (C 4 * X) = C 4 * (X * G4) by ring, coeff_C_mul]
  cases n with
  | zero => simp [G4, coeff_one, constantCoeff_mk]
  | succ n =>
    rw [coeff_succ_X_mul]
    simp [G4, coeff_one, pow_succ]
    ring

/-- `B_b · (1 - 2 X C) = 1`, i.e. `Σ b_r z^r = 1/√(1-4z)` and `1 - 2B = √(1-4z)`. -/
theorem SB_W : SB * W = 1 := by
  have h1 : (SB * W) * (SB * W) = 1 := by
    calc (SB * W) * (SB * W) = (SB * SB) * W ^ 2 := by ring
      _ = G4 * (1 - 4 * X) := by rw [SB_sq, W_sq]
      _ = 1 := G4_mul
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · exact h
  · exfalso
    have h0 := congrArg constantCoeff h
    norm_num [SB, W, constantCoeff_mk, bq, constantCoeff_X] at h0

/-- The Colless toll in antidiagonal form: `D_m = Σ_{p+q=m} |p-q| C_p C_q = a_{m+2}`. -/
def tollA (m : ℕ) : ℚ := ∑ p ∈ antidiagonal m, |(p.1 : ℚ) - p.2| * Cq p.1 * Cq p.2

theorem tollA_eq (m : ℕ) : tollA m = tollSum (m + 2) := by
  unfold tollA tollSum
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_Ico_eq_sum_range]
  rw [show m + 2 - 1 = m.succ by omega]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have e1 : 1 + k - 1 = k := by omega
  have e2 : m + 2 - (1 + k) - 1 = m - k := by omega
  simp only [e1, e2]
  rw [Nat.cast_sub (by omega : k ≤ m)]
  push_cast
  ring_nf

noncomputable def SS : PowerSeries ℚ := PowerSeries.mk fun m => (collessTot m : ℚ)
noncomputable def D : PowerSeries ℚ := PowerSeries.mk tollA
noncomputable def Om : PowerSeries ℚ := PowerSeries.mk fun m => omegaSeq (m + 1)

lemma collessTot_succ_q (m : ℕ) : (collessTot (m + 1) : ℚ) = tollA m
    + ∑ p ∈ antidiagonal m, (collessTot p.1 : ℚ) * Cq p.2
    + ∑ p ∈ antidiagonal m, Cq p.1 * (collessTot p.2 : ℚ) := by
  rw [collessTot_succ]
  unfold tollA Cq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  push_cast [Nat.cast_natAbs, Int.cast_abs]
  try (apply Finset.sum_congr rfl; intro p _; ring)

theorem SS_rec : SS = X * (D + SS * SC + SC * SS) := by
  ext n
  cases n with
  | zero => simp [SS, collessTot, colless]
  | succ m =>
    rw [coeff_succ_X_mul, map_add, map_add, coeff_mul, coeff_mul]
    simp only [SS, D, SC, coeff_mk]
    exact collessTot_succ_q m

theorem XD_eq : X * D = SB - Om := by
  ext n
  cases n with
  | zero => simp [SB, Om, omegaSeq, bq]
  | succ m =>
    rw [coeff_succ_X_mul, map_sub]
    simp only [D, SB, Om, coeff_mk]
    rw [tollA_eq, toll_eq_b_sub_omega (m + 2) (by omega)]
    rfl

theorem SS_eq : SS = G4 - Om * SB := by
  have h1 : SS * W = X * D := by
    have hrec := SS_rec
    unfold W
    linear_combination hrec
  calc SS = SS * (SB * W) := by rw [SB_W, mul_one]
    _ = (SS * W) * SB := by ring
    _ = (SB - Om) * SB := by rw [h1, XD_eq]
    _ = SB * SB - Om * SB := by ring
    _ = G4 - Om * SB := by rw [SB_sq]

/-- `Z_N = Σ_{j=0}^{N} b_{⌊j/2⌋} b_{⌈j/2⌉} b_{N-j}`. -/
def Zpaper (N : ℕ) : ℕ :=
  ∑ j ∈ range (N + 1),
    Nat.centralBinom (j / 2) * Nat.centralBinom ((j + 1) / 2) * Nat.centralBinom (N - j)

theorem collessTot_add_Z (m : ℕ) : collessTot m + Zpaper m = 4 ^ m := by
  have h := congrArg (coeff m) SS_eq
  rw [map_sub, coeff_mul] at h
  simp only [SS, G4, Om, SB, coeff_mk] at h
  have hZ : (Zpaper m : ℚ) = ∑ p ∈ antidiagonal m, omegaSeq (p.1 + 1) * bq p.2 := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    unfold Zpaper
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    simp only [omegaSeq, bq, Nat.add_sub_cancel]
  have h' : (collessTot m : ℚ) + Zpaper m = 4 ^ m := by
    rw [hZ, h]
    ring
  exact_mod_cast h'

/-- **Theorem `mean`, total form**: for `n ≥ 1`, `T_n + Z_{n-1} = 4^{n-1}`, i.e.
`T_n = 4^{n-1} - Z_{n-1}`. -/
theorem collessTotal_add_Z (n : ℕ) (hn : 1 ≤ n) : collessTotal n + Zpaper (n - 1) = 4 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [collessTotal_succ, Nat.add_sub_cancel]
  exact collessTot_add_Z m

/-- **Theorem `mean`**: the mean Colless index over the uniform distribution on plane binary
trees with `n` leaves is `(4^{n-1} - Z_{n-1}) / C_{n-1}`. (By Lemma `plane`, not formalized
here, this is the uniform/PDA-model mean `E_U[col_n]`.) -/
theorem colless_mean (n : ℕ) (hn : 1 ≤ n) :
    (collessTotal n : ℚ) / (planeTrees n).card
      = ((4 : ℚ) ^ (n - 1) - Zpaper (n - 1)) / catalan (n - 1) := by
  rw [card_planeTrees]
  have h := collessTotal_add_Z n hn
  have h' : (collessTotal n : ℚ) = 4 ^ (n - 1) - Zpaper (n - 1) := by
    have h'' : ((collessTotal n + Zpaper (n - 1) : ℕ) : ℚ) = ((4 ^ (n - 1) : ℕ) : ℚ) := by
      rw [h]
    push_cast at h''
    linarith
  rw [h']

end TreeBalance
