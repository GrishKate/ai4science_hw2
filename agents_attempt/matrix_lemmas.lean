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
