# Diary — Best Kronecker Approximation via SVD

## Lemma
$$\min_{L, R} \|g g^\top - L \otimes R\|_F$$
Solution: $L = \sigma_1 u_1 u_1^\top$, $R = \sigma_1 v_1 v_1^\top$
where $u_1, v_1$ are singular vectors of $G$ for $\sigma_1 = \sigma_1(G)$.

## Key Mathlib lemmas
- `Matrix.IsHermitian.eigenvectorBasis` — orthonormal eigenbasis for Hermitian
- `Matrix.IsHermitian.mulVec_eigenvectorBasis` — $A v_i = \lambda_i v_i$
- `OrthonormalBasis.sum_repr` — $v = \sum_i \langle b_i, v \rangle b_i$
- `OrthonormalBasis.norm_eq_one` — $\|b_i\| = 1$
- `Matrix.PosSemidef.eigenvalues_nonneg` — eigenvalues ≥ 0
- `Matrix.IsHermitian.trace_eq_sum_eigenvalues`

## Current status (2026-11-06)
- [x] `GtG_IsHermitian` — $(G^T G)$ is Hermitian
- [x] `GtG_eigenvalues_nonneg` — eigenvalues of $G^T G$ are ≥ 0
- [x] `h_v1_unit` — $\|v_1\| = 1$
- [x] `h_u1_unit` — $\|u_1\| = 1$
- [x] `h_cross_term` — $u_1^T G v_1 = \sigma_1$
- [x] `h_error` — error = $\|G\|_F^2 - \sigma_1^2$
- [x] `h_optimal` — imported, optimality follows
- [x] `h_uGv_bound` — imported, bound on $|u^T G v|$
- [ ] **`h_quadratic_bound`** — 3 `sorry` remain (see below)

## Unresolved: `h_quadratic_bound`
Goal: $\forall v,\; \lambda_1 \|v\|^2 \ge v^T (G^T G) v$

3 `sorry` in the spectral expansion block:
1. `h_expand` — OK, `OrthonormalBasis.sum_repr` closes it
2. `h_quadratic` — need to show $v^T A v = \sum_i \lambda_i c_i^2$ where $c_i = \langle e_i, v \rangle$
   - Sub-sorry 1: substitute $v = \sum c_i e_i$ into $(G^T G).mulVec v$
   - Sub-sorry 2: simplify using linearity + `mulVec_eigenvectorBasis`
   - Sub-sorry 3: the final `calc` step
3. The `sorry` after `h_quadratic` (goal: $\ge \dots$)

Plan to close:
- Use `OrthonormalBasis.sum_repr` for `h_expand`
- Expand $(G^T G).mulVec (\sum c_i e_i)$ using `Finset.sum_smul` + `Matrix.mulVec_sum`
- Apply `mulVec_eigenvectorBasis` to get $\sum c_i \lambda_i e_i$
- Use `OrthonormalBasis.orthonormal` for inner product: $\langle \sum c_i e_i, \sum c_j \lambda_j e_j \rangle = \sum \lambda_i c_i^2$
- Apply `h_eigen_le` + `h_coeff_nonneg` for the bound

## proof.lean structure
- Main theorem: `minimize_kronecker_approximation`
- Imports: `h_quadratic`, `matrix_lemmas`, `h_uGv_bound`, `h_optimal`
- 3 external imports; 2 internal (`h_quadratic`, `GtG_eigenvalues_nonneg`)