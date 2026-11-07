import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import h_quadratic
import «matrix_lemmas»

import h_uGv_bound
import h_optimal

open Matrix InnerProductSpace Finset EuclideanSpace

/-- Main theorem: best rank-1 approximation via SVD -/
theorem minimize_kronecker_approximation
  (m n : Type*) [Fintype m] [Fintype n]
  (G : Matrix m n ℝ)
  (hG : G ≠ 0) :
  ∃ (sigma1 : ℝ) (u1 : m → ℝ) (v1 : n → ℝ),
    sigma1 > 0 ∧
    (∑ i, u1 i ^ 2) = 1 ∧
    (∑ j, v1 j ^ 2) = 1 ∧
    (∑ i, ∑ j, (G i j - sigma1 * u1 i * v1 j) ^ 2) =
      (∑ i, ∑ j, (G i j) ^ 2) - sigma1 ^ 2 ∧
    ∀ (sigma : ℝ) (u : m → ℝ) (v : n → ℝ),
      (∑ i, u i ^ 2) = 1 →
      (∑ j, v j ^ 2) = 1 →
      (∑ i, ∑ j, (G i j - sigma * u i * v j) ^ 2) ≥
        (∑ i, ∑ j, (G i j) ^ 2) - sigma1 ^ 2 :=
by
  have hHermitian : (G.transpose * G).IsHermitian := GtG_IsHermitian G
  let eigenbasis := hHermitian.eigenvectorBasis
  let eigenvalues := hHermitian.eigenvalues
  let S := Finset.image eigenvalues Finset.univ
  let lambda1 := Finset.max' S (by apply Finset.image_nonempty.mpr Finset.univ_nonempty)
  have h_max_exists : ∃ i, eigenvalues i = lambda1 := by
    have h : lambda1 ∈ S := by apply Finset.max'_mem
    simpa [S] using h
  let ⟨i_max, hi_max⟩ := h_max_exists
  let v1 : n → ℝ := (eigenbasis i_max).ofLp
  let sigma1 := Real.sqrt lambda1
  let u1 : m → ℝ := fun k => (∑ j, G k j * v1 j) / sigma1

  have h_lambda_nonneg : 0 ≤ lambda1 := by
    rcases h_max_exists with ⟨i, hi⟩
    have h_nonneg : 0 ≤ eigenvalues i := GtG_eigenvalues_nonneg G i
    rw [hi] at *
    exact h_nonneg

  have h_lambda_pos : 0 < lambda1 := by
    have h_trace : (G.transpose * G).trace = ∑ i, ∑ j, (G i j) ^ 2 := by
      calc
        (G.transpose * G).trace = ∑ i, (G.transpose * G) i i := by rw [Matrix.trace]
        _ = ∑ i, ∑ k, G.transpose i k * G k i := by rw [Matrix.mul_apply]
        _ = ∑ i, ∑ k, G k i * G k i := by simp [Matrix.transpose_apply]; congr 1; ext <;> ring
        _ = ∑ i, ∑ k, (G k i) ^ 2 := by simp [pow_two]; congr 1; ext <;> ring
        _ = ∑ k, ∑ i, (G k i) ^ 2 := by rw [Finset.sum_comm]
        _ = ∑ i, ∑ j, (G i j) ^ 2 := by simp [Finset.sum_comm]; congr 1; ext <;> ring
    have h_sum_eigenvalues : (G.transpose * G).trace = ∑ i, ↑(hHermitian.eigenvalues i) := by
      apply hHermitian.trace_eq_sum_eigenvalues
    have h_norm_pos : 0 < ∑ i, ∑ j, (G i j) ^ 2 := by
      have hG' : ∃ i j, G i j ≠ 0 := by
        by_contra h; push_neg at h
        have : G = 0 := by ext i j; apply h
        contradiction
      rcases hG' with ⟨i, j, hij⟩
      have : 0 < ∑ i, ∑ j, (G i j) ^ 2 := by
        have : 0 ≤ ∑ i, ∑ j, (G i j) ^ 2 := by exact Finset.sum_nonneg (fun ⟨i, j⟩ _ => sq_nonneg _)
        have : ∑ i, ∑ j, (G i j) ^ 2 ≠ 0 := by
          have : (G i j) ^ 2 > 0 := by apply sq_pos_of_ne_zero hij
          have : ∑ i, ∑ j, (G i j) ^ 2 ≥ (G i j) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx; simp
            · intro x _; exact sq_nonneg _
          linarith
        linarith
      exact this
    have h_sum_pos : 0 < ∑ i, ↑(hHermitian.eigenvalues i) := by
      rw [h_sum_eigenvalues]; rw [h_trace]; exact h_norm_pos
    have h_exists_pos : ∃ i, 0 < eigenvalues i := by
      by_contra h; push_neg at h
      have : ∀ i, eigenvalues i ≤ 0 := by intro i; have h_nonneg : 0 ≤ eigenvalues i := GtG_eigenvalues_nonneg G i; linarith
      have : ∑ i, ↑(hHermitian.eigenvalues i) ≤ 0 := by
        apply Finset.sum_nonpos; intro i _; exact this i
      linarith
    rcases h_exists_pos with ⟨i, hi_pos⟩
    have h_max_ge : lambda1 ≥ eigenvalues i := by
      have h : eigenvalues i ∈ S := by apply Finset.mem_image.mpr; exact ⟨i, Finset.mem_univ i⟩
      have : ∀ x ∈ S, x ≤ lambda1 := by intro x hx; apply Finset.max'_le; exact hx
      exact this (eigenvalues i) (by apply Finset.mem_image.mpr; exact ⟨i, Finset.mem_univ i⟩)
    linarith

  have h_sigma_pos : 0 < sigma1 := by
    rw [sigma1]; apply Real.sqrt_pos.mpr; exact h_lambda_pos

  have h_v1_unit : ∑ j, v1 j ^ 2 = 1 := by
    calc
      ∑ j, v1 j ^ 2 = ∑ j, ‖v1 j‖ ^ 2 := by simp [sq]
      _ = ‖v1‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
      _ = 1 ^ 2 := by
        have : v1 = (eigenbasis i_max).ofLp := rfl
        rw [this]
        have : ‖(eigenbasis i_max).ofLp‖ = 1 := by apply OrthonormalBasis.norm_eq_one
        rw [this]
      _ = 1 := by ring

  -- Key lemma: v^T (G^T G) v ≤ lambda1 * ||v||^2 for any vector v
  have h_quadratic_bound : ∀ (v : EuclideanSpace ℝ n),
      (∑ j, v j ^ 2) * lambda1 ≥ ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) := by
    intro v
    classical
    have h_orth : Orthonormal ℝ eigenbasis := by apply hHermitian.eigenvectorBasis.orthonormal
    have h_ev : ∀ i, (G.transpose * G).mulVec (eigenbasis i) = eigenvalues i • (eigenbasis i) := by
      intro i; apply hHermitian.mulVec_eigenvectorBasis
    have h_eigen_le : ∀ i, eigenvalues i ≤ lambda1 := by
      intro i
      apply Finset.max'_le
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have h_coeff_nonneg : ∀ i, 0 ≤ (∑ j, v j * (eigenbasis i) j) ^ 2 := by
      intro i
      exact sq_nonneg _
    -- Шаг 1: разложение v по ортонормированному собственному базису.
    -- Then v^T (G^T G) v = ∑ λ_i c_i^2 ≤ λ_max ∑ c_i^2 = λ_max ||v||^2
    have h_expand : v = ∑ i, (∑ j, v j * (eigenbasis i) j) • (eigenbasis i) := by
      apply OrthonormalBasis.sum_repr
    have h_quadratic : ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) = ∑ i, eigenvalues i * (∑ j, v j * (eigenbasis i) j) ^ 2 := by
      -- v^T A v = ⟨v, Av⟩ = ⟨∑ c_i e_i, ∑ c_i λ_i e_i⟩ = ∑ λ_i c_i^2
      calc
        ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) = ∑ j, v j * ((G.transpose * G).mulVec v) j := by ext j; simp [Matrix.mulVec]
        _ = ∑ j, v j * ((G.transpose * G).mulVec (∑ i, (∑ l, v l * (eigenbasis i) l) • (eigenbasis i))) j := by
            congr 1
            ext j
            simp [Matrix.mulVec]
            -- Use the fact that v = ∑ c_i e_i
            sorry
        _ = ∑ j, v j * ((G.transpose * G).mulVec (∑ i, (∑ l, v l * (eigenbasis i) l) • (eigenbasis i))) j := by sorry
      sorry
    sorry

  -- Key lemma: |u^T G v| ≤ sigma1 for unit vectors u, v
  have h_uGv_bound := h_uGv_bound G lambda1 sigma1 h_quadratic_bound h_sigma_pos (by
    rw [sigma1]
    field_simp [h_lambda_pos.ne']
    <;> simp [Real.sqrt_eq_iff_sq_eq, h_lambda_nonneg, h_lambda_pos.le]
    <;> ring)

  -- Step 5: u1 is unit norm
  have h_u1_unit : ∑ i, u1 i ^ 2 = 1 := by
    calc
      ∑ i, u1 i ^ 2 = ∑ i, ((∑ j, G i j * v1 j) / sigma1) ^ 2 := by simp [u1]
      _ = (1 / sigma1 ^ 2) * ∑ i, (∑ j, G i j * v1 j) ^ 2 := by
        rw [Finset.sum_div]; <;> simp [pow_two]; <;> ring
      _ = (1 / sigma1 ^ 2) * ∑ i, (G.mulVec v1) i ^ 2 := by
        congr 1; ext i; simp [Matrix.mulVec]; <;> ring
      _ = (1 / sigma1 ^ 2) * ‖G.mulVec v1‖ ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
      _ = (1 / sigma1 ^ 2) * (∑ j, v1 j * (∑ k, (G.transpose * G) j k * v1 k)) := by
        calc
          ‖G.mulVec v1‖ ^ 2 = ∑ i, (G.mulVec v1) i ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
          _ = ∑ i, (∑ j, G i j * v1 j) ^ 2 := by congr 1; ext i; simp [Matrix.mulVec]; <;> ring
          _ = ∑ i, (∑ j, G i j * v1 j) * (∑ k, G i k * v1 k) := by simp [pow_two]; congr 1; ext <;> ring
          _ = ∑ j, v1 j * (∑ k, (∑ i, G i j * G i k) * v1 k) := by
              rw [Finset.sum_mul_sum]; <;> simp [mul_assoc, mul_comm, mul_left_comm]; <;> congr 1; ext <;> ring
          _ = ∑ j, v1 j * (∑ k, (G.transpose * G) j k * v1 k) := by
              congr 1; ext j; simp [Matrix.mul_apply, Matrix.transpose_apply]; <;> ring
      _ = (1 / sigma1 ^ 2) * lambda1 := by
        have h_ev : (G.transpose * G).mulVec v1 = lambda1 • v1 := by
          calc
            (G.transpose * G).mulVec v1 = (G.transpose * G).mulVec (eigenbasis i_max).ofLp := by rw [v1]
            _ = hHermitian.eigenvalues i_max • (eigenbasis i_max).ofLp := by apply hHermitian.mulVec_eigenvectorBasis
            _ = lambda1 • (eigenbasis i_max).ofLp := by rw [hi_max]
            _ = lambda1 • v1 := by rw [v1]
        have h_quadratic : ∑ j, v1 j * (∑ k, (G.transpose * G) j k * v1 k) = lambda1 := by
          calc
            ∑ j, v1 j * (∑ k, (G.transpose * G) j k * v1 k) = ∑ j, v1 j * ((G.transpose * G).mulVec v1) j := by ext j; simp [Matrix.mulVec]
            _ = ∑ j, v1 j * (lambda1 * v1 j) := by congr 1; ext j; rw [h_ev]; simp [smul_eq_mul]
            _ = lambda1 * ∑ j, v1 j ^ 2 := by rw [Finset.sum_mul]
            _ = lambda1 * 1 := by rw [h_v1_unit]
            _ = lambda1 := by ring
        exact h_quadratic
      _ = 1 := by
        rw [sigma1]; field_simp [h_lambda_pos.ne']; <;> ring
        <;> simp [Real.sqrt_eq_iff_sq_eq, h_lambda_nonneg, h_lambda_pos.le]; <;> ring

  -- Step 6: u1^T G v1 = sigma1
  have h_cross_term : ∑ i, u1 i * (∑ j, G i j * v1 j) = sigma1 := by
    calc
      ∑ i, u1 i * (∑ j, G i j * v1 j) = ∑ i, ((∑ j, G i j * v1 j) / sigma1) * (∑ j, G i j * v1 j) := by simp [u1]
      _ = (1 / sigma1) * ∑ i, (∑ j, G i j * v1 j) ^ 2 := by rw [Finset.sum_mul]; <;> simp [pow_two]; <;> ring
      _ = (1 / sigma1) * ‖G.mulVec v1‖ ^ 2 := by
        calc ∑ i, (∑ j, G i j * v1 j) ^ 2 = ∑ i, (G.mulVec v1) i ^ 2 := by congr 1; ext i; simp [Matrix.mulVec]; <;> ring
          _ = ‖G.mulVec v1‖ ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
      _ = (1 / sigma1) * lambda1 := by
        have h_ev : (G.transpose * G).mulVec v1 = lambda1 • v1 := by
          calc
            (G.transpose * G).mulVec v1 = (G.transpose * G).mulVec (eigenbasis i_max).ofLp := by rw [v1]
            _ = hHermitian.eigenvalues i_max • (eigenbasis i_max).ofLp := by apply hHermitian.mulVec_eigenvectorBasis
            _ = lambda1 • (eigenbasis i_max).ofLp := by rw [hi_max]
            _ = lambda1 • v1 := by rw [v1]
        have h_norm_sq : ‖G.mulVec v1‖ ^ 2 = lambda1 := by
          calc
            ‖G.mulVec v1‖ ^ 2 = ∑ i, (G.mulVec v1) i ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
            _ = ∑ i, (∑ j, G i j * v1 j) ^ 2 := by congr 1; ext i; simp [Matrix.mulVec]; <;> ring
            _ = ∑ i, (∑ j, G i j * v1 j) * (∑ k, G i k * v1 k) := by simp [pow_two]; congr 1; ext <;> ring
            _ = ∑ j, v1 j * (∑ k, (∑ i, G i j * G i k) * v1 k) := by rw [Finset.sum_mul_sum]; <;> simp [mul_assoc, mul_comm, mul_left_comm]; <;> congr 1; ext <;> ring
            _ = ∑ j, v1 j * (∑ k, (G.transpose * G) j k * v1 k) := by congr 1; ext j; simp [Matrix.mul_apply, Matrix.transpose_apply]; <;> ring
            _ = ∑ j, v1 j * ((G.transpose * G).mulVec v1) j := by ext j; simp [Matrix.mulVec]
            _ = ∑ j, v1 j * (lambda1 * v1 j) := by congr 1; ext j; rw [h_ev]; simp [smul_eq_mul]
            _ = lambda1 * ∑ j, v1 j ^ 2 := by rw [Finset.sum_mul]
            _ = lambda1 * 1 := by rw [h_v1_unit]
            _ = lambda1 := by ring
        exact h_norm_sq
      _ = sigma1 := by rw [sigma1]; field_simp [h_lambda_pos.ne']; <;> ring
        <;> simp [Real.sqrt_eq_iff_sq_eq, h_lambda_nonneg, h_lambda_pos.le]; <;> ring

  -- Step 7: Error equals ||G||_F^2 - sigma1^2
  have h_error : ∑ i, ∑ j, (G i j - sigma1 * u1 i * v1 j) ^ 2 = ∑ i, ∑ j, (G i j) ^ 2 - sigma1 ^ 2 := by
    calc
      ∑ i, ∑ j, (G i j - sigma1 * u1 i * v1 j) ^ 2
        = ∑ i, ∑ j, (G i j ^ 2 - 2 * sigma1 * G i j * u1 i * v1 j + sigma1 ^ 2 * u1 i ^ 2 * v1 j ^ 2) := by simp [pow_two]; <;> ring
      _ = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma1 * ∑ i, ∑ j, G i j * u1 i * v1 j + sigma1 ^ 2 * ∑ i, ∑ j, u1 i ^ 2 * v1 j ^ 2 := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]; <;> ring
      _ = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma1 * (∑ i, u1 i * (∑ j, G i j * v1 j)) * 1 + sigma1 ^ 2 * (∑ i, u1 i ^ 2) * (∑ j, v1 j ^ 2) := by
          have h1 : ∑ i, ∑ j, G i j * u1 i * v1 j = (∑ i, u1 i * (∑ j, G i j * v1 j)) := by
            calc ∑ i, ∑ j, G i j * u1 i * v1 j = ∑ i, u1 i * (∑ j, G i j * v1 j) := by rw [Finset.sum_mul]; <;> simp [mul_assoc, mul_comm, mul_left_comm]; <;> congr 1; ext <;> ring
            _ = ∑ i, u1 i * (∑ j, G i j * v1 j) := by ring
          have h2 : ∑ i, ∑ j, u1 i ^ 2 * v1 j ^ 2 = (∑ i, u1 i ^ 2) * (∑ j, v1 j ^ 2) := by
            rw [Finset.sum_mul_sum]; <;> simp [mul_assoc, mul_comm, mul_left_comm]; <;> congr 1; ext <;> ring
          rw [h1, h2]; <;> simp [Finset.sum_mul, Finset.mul_sum]; <;> ring
      _ = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma1 * sigma1 + sigma1 ^ 2 * 1 * 1 := by rw [h_cross_term, h_u1_unit, h_v1_unit]; <;> ring
      _ = ∑ i, ∑ j, G i j ^ 2 - sigma1 ^ 2 := by ring

  -- Step 8: Optimality
  have h_optimal := h_optimal G sigma1 h_uGv_bound
  refine' ⟨sigma1, u1, v1, h_sigma_pos, h_u1_unit, h_v1_unit, h_error, h_optimal⟩
