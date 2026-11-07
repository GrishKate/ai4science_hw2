import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

open Matrix InnerProductSpace Finset EuclideanSpace
open scoped Matrix.Norms.Frobenius
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

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
