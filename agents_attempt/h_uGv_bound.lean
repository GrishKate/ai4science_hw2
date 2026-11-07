import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import matrix_lemmas

open Matrix InnerProductSpace Finset EuclideanSpace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

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

