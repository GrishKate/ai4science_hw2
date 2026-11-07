import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

open Matrix InnerProductSpace Finset EuclideanSpace
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem GtG_symmetric (G : Matrix m n ℝ) :
  (G.transpose * G).transpose = G.transpose * G := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  <;> simp [Matrix.mul_comm]

theorem GtG_posSemidef (G : Matrix m n ℝ) :
  ∀ x : n → ℝ, 0 ≤ ∑ i, x i * (∑ j, (G.transpose * G) i j * x j) := by
  intro x
  have h : ∑ i, x i * (∑ j, (G.transpose * G) i j * x j) = ∑ k, (∑ i, G k i * x i) ^ 2 := by
    calc
      ∑ i, x i * (∑ j, (G.transpose * G) i j * x j) = ∑ i, x i * (∑ j, (∑ k, G.transpose i k * G k j) * x j) := by
        congr 1; ext j; rw [Matrix.mul_apply]
      _ = ∑ i, x i * (∑ j, (∑ k, G k i * G k j) * x j) := by
        simp [Matrix.transpose_apply]; <;> congr 1 <;> ext <;> ring
      _ = ∑ k, (∑ i, G k i * x i) * (∑ j, G k j * x j) := by
        rw [Finset.sum_mul_sum]; <;> simp [mul_assoc, mul_comm, mul_left_comm]
        <;> congr 1 <;> ext <;> ring
      _ = ∑ k, (∑ i, G k i * x i) ^ 2 := by
        simp [pow_two]; <;> congr 1 <;> ext <;> ring
  rw [h]
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

theorem GtG_IsHermitian (G : Matrix m n ℝ) : (G.transpose * G).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [Matrix.IsSymm]
  <;> rw [GtG_symmetric G]
  <;> simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  <;> ring

theorem frobenius_norm_sq_def (G : Matrix m n ℝ) :
  (∑ i, ∑ j, (G i j) ^ 2) = ‖G‖ ^ 2 := by
  rw [frobenius_norm_def]
  <;> simp [sq]
  <;> ring

/-- Eigenvalues of Gᵀ G are nonnegative. -/
theorem GtG_eigenvalues_nonneg (G : Matrix m n ℝ) :
  ∀ i, 0 ≤ (GtG_IsHermitian G).eigenvalues i := by
  intro i
  have h_ev : (G.transpose * G).mulVec ((GtG_IsHermitian G).eigenvectorBasis i) =
    (GtG_IsHermitian G).eigenvalues i • ((GtG_IsHermitian G).eigenvectorBasis i) := by
    apply (GtG_IsHermitian G).mulVec_eigenvectorBasis
  have h_unit : ‖(GtG_IsHermitian G).eigenvectorBasis i‖ = 1 := by
    apply OrthonormalBasis.norm_eq_one
  let v : EuclideanSpace ℝ n := (GtG_IsHermitian G).eigenvectorBasis i
  have h_v_unit : ∑ j, (v j) ^ 2 = 1 := by
    calc
      ∑ j, (v j) ^ 2 = ∑ j, ‖v j‖ ^ 2 := by simp [sq]
      _ = ‖v‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
      _ = 1 ^ 2 := by rw [h_unit]
      _ = 1 := by ring
  have h_ev2 : (G.transpose * G).mulVec v = (GtG_IsHermitian G).eigenvalues i • v := by
    rw [← h_ev]
    simp [v]
  have h_quadratic : ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) =
      (GtG_IsHermitian G).eigenvalues i := by
    calc
      ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) = ∑ j, v j * ((G.transpose * G).mulVec v) j := by
        ext j
        simp [Matrix.mulVec]
      _ = ∑ j, v j * ((GtG_IsHermitian G).eigenvalues i * v j) := by
        congr 1
        ext j
        rw [h_ev2]
        simp [smul_eq_mul]
      _ = (GtG_IsHermitian G).eigenvalues i * ∑ j, v j ^ 2 := by rw [Finset.sum_mul]
      _ = (GtG_IsHermitian G).eigenvalues i * 1 := by rw [h_v_unit]
      _ = (GtG_IsHermitian G).eigenvalues i := by ring
  have h_psd : 0 ≤ ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) := by
    apply GtG_posSemidef
  rw [h_quadratic] at h_psd
  exact h_psd


theorem h_uGv_bound
  (G : Matrix m n ℝ) (lambda1 sigma1 : ℝ)
  (h_quadratic_bound : ∀ v : EuclideanSpace ℝ n, (∑ j, v j ^ 2) * lambda1 ≥ ∑ j, v j * (∑ k, (G.transpose * G) j k * v k))
  (h_sigma_pos : 0 < sigma1) (h_sigma_sq : sigma1 ^ 2 = lambda1) :
  ∀ (u : m → ℝ) (v : n → ℝ), (∑ i, u i ^ 2) = 1 → (∑ j, v j ^ 2) = 1 → |∑ i, u i * (∑ j, G i j * v j)| ≤ sigma1 := by
    intro u v hu hv
    calc
      |∑ i, u i * (∑ j, G i j * v j)| = |∑ i, u i * (G.mulVec v) i| := by
        congr 1; ext i; simp [Matrix.mulVec]; <;> ring
      _ ≤ ‖(fun i => u i)‖ * ‖G.mulVec v‖ := by apply abs_sum_le_norm_mul_norm
      _ = 1 * ‖G.mulVec v‖ := by
        have : ‖(fun i => u i)‖ = 1 := by
          calc ‖(fun i => u i)‖ ^ 2 = ∑ i, u i ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
            _ = 1 := by rw [hu]
        rw [this]; <;> ring
      _ = ‖G.mulVec v‖ := by ring
      _ ≤ Real.sqrt lambda1 := by
        have : ‖G.mulVec v‖ ^ 2 ≤ lambda1 := by
          calc
            ‖G.mulVec v‖ ^ 2 = ∑ i, (G.mulVec v) i ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
            _ = ∑ i, (∑ j, G i j * v j) ^ 2 := by congr 1; ext i; simp [Matrix.mulVec]; <;> ring
            _ = ∑ i, (∑ j, G i j * v j) * (∑ k, G i k * v k) := by simp [pow_two]; congr 1; ext <;> ring
            _ = ∑ j, v j * (∑ k, (∑ i, G i j * G i k) * v k) := by
                rw [Finset.sum_mul_sum]; <;> simp [mul_assoc, mul_comm, mul_left_comm]; <;> congr 1; ext <;> ring
            _ = ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) := by
                congr 1; ext j; simp [Matrix.mul_apply, Matrix.transpose_apply]; <;> ring
            _ ≤ lambda1 * ∑ j, v j ^ 2 := h_quadratic_bound v
            _ ≤ lambda1 * 1 := by gcongr; exact hv
            _ = lambda1 := by ring
        apply Real.sqrt_le_sqrt
        exact this
      _ = sigma1 := by rw [sigma1]


theorem h_optimal
  (G : Matrix m n ℝ) (sigma1 : ℝ)
  (h_uGv_bound : ∀ (u : m → ℝ) (v : n → ℝ), (∑ i, u i ^ 2) = 1 → (∑ j, v j ^ 2) = 1 → |∑ i, u i * (∑ j, G i j * v j)| ≤ sigma1) :
  ∀ (sigma : ℝ) (u : m → ℝ) (v : n → ℝ), (∑ i, u i ^ 2) = 1 → (∑ j, v j ^ 2) = 1 →
      (∑ i, ∑ j, (G i j - sigma * u i * v j) ^ 2) ≥ (∑ i, ∑ j, (G i j) ^ 2) - sigma1 ^ 2 := by
    intro sigma u v hu hv
    calc
      ∑ i, ∑ j, (G i j - sigma * u i * v j) ^ 2
        = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma * (∑ i, u i * (∑ j, G i j * v j)) + sigma ^ 2 := by
          have h1 : ∑ i, ∑ j, (G i j - sigma * u i * v j) ^ 2
              = ∑ i, ∑ j, (G i j ^ 2 - 2 * sigma * G i j * u i * v j + sigma ^ 2 * u i ^ 2 * v j ^ 2) := by simp [pow_two]; <;> ring
          have h2 : ∑ i, ∑ j, (G i j ^ 2 - 2 * sigma * G i j * u i * v j + sigma ^ 2 * u i ^ 2 * v j ^ 2)
              = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma * ∑ i, u i * (∑ j, G i j * v j) + sigma ^ 2 := by
            calc
              ∑ i, ∑ j, (G i j ^ 2 - 2 * sigma * G i j * u i * v j + sigma ^ 2 * u i ^ 2 * v j ^ 2)
                = ∑ i, ∑ j, G i j ^ 2 - ∑ i, ∑ j, 2 * sigma * G i j * u i * v j + ∑ i, ∑ j, sigma ^ 2 * u i ^ 2 * v j ^ 2 := by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              _ = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma * ∑ i, u i * (∑ j, G i j * v j) + sigma ^ 2 * (∑ i, u i ^ 2) * (∑ j, v j ^ 2) := by
                have h3 : ∑ i, ∑ j, 2 * sigma * G i j * u i * v j = 2 * sigma * ∑ i, u i * (∑ j, G i j * v j) := by
                  calc ∑ i, ∑ j, 2 * sigma * G i j * u i * v j = ∑ i, 2 * sigma * u i * (∑ j, G i j * v j) := by rw [Finset.sum_mul]; <;> simp [mul_assoc, mul_comm, mul_left_comm]; <;> congr 1; ext <;> ring
                  _ = 2 * sigma * ∑ i, u i * (∑ j, G i j * v j) := by rw [Finset.sum_mul]
                have h4 : ∑ i, ∑ j, sigma ^ 2 * u i ^ 2 * v j ^ 2 = sigma ^ 2 * (∑ i, u i ^ 2) * (∑ j, v j ^ 2) := by
                  rw [Finset.sum_mul_sum]; <;> simp [mul_assoc, mul_comm, mul_left_comm]; <;> congr 1; ext <;> ring
                rw [h3, h4]; <;> simp [Finset.sum_mul, Finset.mul_sum]; <;> ring
              _ = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma * ∑ i, u i * (∑ j, G i j * v j) + sigma ^ 2 := by rw [hu, hv]; <;> ring
          rw [h1, h2]
        _ = ∑ i, ∑ j, G i j ^ 2 - 2 * sigma * (∑ i, u i * (∑ j, G i j * v j)) + sigma ^ 2 := by ring
        _ ≥ ∑ i, ∑ j, G i j ^ 2 - sigma1 ^ 2 := by
          have h_cauchy : |∑ i, u i * (∑ j, G i j * v j)| ≤ sigma1 := h_uGv_bound u v hu hv
          have h_ineq : -2 * sigma * (∑ i, u i * (∑ j, G i j * v j)) + sigma ^ 2 ≥ -sigma1 ^ 2 := by
            have h_abs : |∑ i, u i * (∑ j, G i j * v j)| ≤ sigma1 := h_cauchy
            have h_ineq : -2 * sigma * (∑ i, u i * (∑ j, G i j * v j)) + sigma ^ 2 ≥ -2 * |sigma| * sigma1 + sigma ^ 2 := by
              calc
                -2 * sigma * (∑ i, u i * (∑ j, G i j * v j)) + sigma ^ 2
                  ≥ -2 * |sigma| * |∑ i, u i * (∑ j, G i j * v j)| + sigma ^ 2 := by
                    have h1 : sigma * (∑ i, u i * (∑ j, G i j * v j)) ≤ |sigma| * |∑ i, u i * (∑ j, G i j * v j)| := by
                      calc sigma * (∑ i, u i * (∑ j, G i j * v j)) ≤ |sigma * (∑ i, u i * (∑ j, G i j * v j))| := by apply le_abs_self
                        _ = |sigma| * |∑ i, u i * (∑ j, G i j * v j)| := by rw [abs_mul]
                    linarith
                    _ ≥ -2 * |sigma| * |∑ i, u i * (∑ j, G i j * v j)| + sigma ^ 2 := by ring
                _ ≥ -2 * |sigma| * sigma1 + sigma ^ 2 := by gcongr; exact h_abs
            have h_final : -2 * |sigma| * sigma1 + sigma ^ 2 ≥ -sigma1 ^ 2 := by
              calc -2 * |sigma| * sigma1 + sigma ^ 2 = (|sigma| - sigma1) ^ 2 - sigma1 ^ 2 := by ring
                _ ≥ -sigma1 ^ 2 := by apply sub_le_sub_right; nlinarith
            linarith
          calc
            ∑ i, ∑ j, G i j ^ 2 - 2 * sigma * (∑ i, u i * (∑ j, G i j * v j)) + sigma ^ 2
              = ∑ i, ∑ j, G i j ^ 2 + (-2 * sigma * (∑ i, u i * (∑ j, G i j * v j)) + sigma ^ 2) := by ring
            _ ≥ ∑ i, ∑ j, G i j ^ 2 + (-sigma1 ^ 2) := by gcongr; exact h_ineq
            _ = ∑ i, ∑ j, G i j ^ 2 - sigma1 ^ 2 := by ring
