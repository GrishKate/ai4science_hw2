import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

open Matrix InnerProductSpace Finset EuclideanSpace
open scoped Matrix.Norms.Frobenius
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
        congr 1
      _ = ∑ i, x i * (∑ j, (∑ k, G k i * G k j) * x j) := by
        simp only [Matrix.transpose_apply]
      _ = ∑ k, (∑ i, G k i * x i) * (∑ j, G k j * x j) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        calc
          _ = ∑ k, ∑ i, ∑ j,
                G k i * x i * (G k j * x j) := by
              simp_rw [Finset.mul_sum]
              conv_lhs =>
                arg 2
                intro i
                rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              simp only [mul_left_comm, mul_comm]
          _ = ∑ k, ∑ i,
                (G k i * x i) * (∑ j, G k j * x j) := by
            simp_rw [Finset.mul_sum]
          _ = ∑ k,
                (∑ i, G k i * x i) *
                (∑ j, G k j * x j) := by
            simp_rw [Finset.sum_mul]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        simp only [mul_comm]
      _ = ∑ k, (∑ i, G k i * x i) ^ 2 := by
        simp only [← sq]
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
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  · simp only [Real.norm_eq_abs, sq_abs]
    norm_num
  · · exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _))


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
  have h_quadratic : ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) =
      (GtG_IsHermitian G).eigenvalues i := by
    calc
      ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) = ∑ j, v j * ((G.transpose * G).mulVec v) j := by
        simp only [Matrix.mulVec, dotProduct]
      _ = ∑ j, v j * ((GtG_IsHermitian G).eigenvalues i * v j) := by
        congr 1
        ext j
        rw [h_ev2]
        simp [smul_eq_mul]
      _ = (GtG_IsHermitian G).eigenvalues i * ∑ j, v j ^ 2 := by
        calc
          ∑ j, v j * ((GtG_IsHermitian G).eigenvalues i * v j)
              = ∑ j, (GtG_IsHermitian G).eigenvalues i * (v j ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
          _ = (GtG_IsHermitian G).eigenvalues i * ∑ j, v j ^ 2 := by
                  rw [Finset.mul_sum]
      _ = (GtG_IsHermitian G).eigenvalues i * 1 := by rw [h_v_unit]
      _ = (GtG_IsHermitian G).eigenvalues i := by ring
  have h_psd : 0 ≤ ∑ j, v j * (∑ k, (G.transpose * G) j k * v k) := by
    apply GtG_posSemidef
  rw [h_quadratic] at h_psd
  exact h_psd
