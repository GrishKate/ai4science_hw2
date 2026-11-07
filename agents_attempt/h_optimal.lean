import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import matrix_lemmas
import h_uGv_bound

open Matrix InnerProductSpace Finset EuclideanSpace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

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
