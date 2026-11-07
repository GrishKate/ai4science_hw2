import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix

open Matrix InnerProductSpace Finset EuclideanSpace

variable {m n : Type*} [Fintype m] [Fintype n]

-- Test: inner product in EuclideanSpace
example (v w : EuclideanSpace ℝ n) : inner ℝ v w = ∑ i, v i * w i := by
  simp [inner_eq_sum]

-- Test: OrthonormalBasis.sum_repr'
example {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (b : OrthonormalBasis ι ℝ E) (x : E) :
  ∑ i, inner ℝ (b i) x • b i = x := by
  apply OrthonormalBasis.sum_repr'