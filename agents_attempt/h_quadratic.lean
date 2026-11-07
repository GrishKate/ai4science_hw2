import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import matrix_lemmas

open Matrix InnerProductSpace Finset EuclideanSpace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

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
