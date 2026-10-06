# tree-balance-lean

Lean 4 / Mathlib formalization of key results from

- H. Song, *Exact moments of tree balance indices under the Yule and uniform models* (2026), and
- H. Song, *Transfer theorems and the phase diagram of limit laws for Aldous's beta-splitting trees* (2026).

Toolchain: Lean v4.34.1, Mathlib v4.34.1 (pinned in `lake-manifest.json`). Build with `lake exe cache get && lake build`; CI runs the same in `.github/workflows/build.yml`. No `sorry`; main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.

| File | Main theorems | Paper statement |
|---|---|---|
| `TreeBalance/Counting.lean` | `pda_plane_count` | (2n-3)!! 2^(n-1) = n! Catalan(n-1) |
| `TreeBalance/Toll.lean` | `gosper`, `toll`, `toll_eq_b_sub_omega` | Gosper certificate; closed form of the Colless root toll |
| `TreeBalance/Convolution.lean` | `sum_centralBinom_mul_centralBinom` | sum_k b_k b_(N-k) = 4^N |
| `TreeBalance/Colless.lean` | `collessTotal_rec`, `colless_mean` | mean Colless index over uniform plane binary trees = (4^(n-1) - S_(n-1)) / Catalan(n-1) |
| `TreeBalance/BetaSplitting.lean` | `phi_neg_one`, `beta_neg_one_normalisation`, `pNegOne_mixture` | beta = -1 splitting rate, normalisation, Beta-mixture representation |

Scope: `colless_mean` is stated for uniformly random plane binary trees; its identification with the uniform (PDA) model of phylogenetic trees uses the paper's Lemma (plane trees), of which only the counting identity is formalized. The Beta-mixture representation is formalized for beta = -1 only.

License: MIT.
