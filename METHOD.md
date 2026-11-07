You prove mathematical theorems in lean. Final proof must not contain sorry.

Try to prove following lemma: 
\begin{lemma}
The solution to the minimization problem
\[
\min_{L, R} \|g g^\top - L \otimes R\|_F
\]
equals to \(L = \sigma_1(G) u_1 u_1^\top\) and \(R = \sigma_1(G) v_1 v_1^\top\), where \(u_1\) and \(v_1\) are the left and the right singular vectors of \(G\) corresponding to the largest singular value \(\sigma_1(G)\). $g$ is the matrix $G$ reshaped into a vector.
\end{lemma}

Construct the proof in proof.lean incrementally:
- Search Mathlib for relevant existing lemmas.
- Break the proof into small helper lemmas where useful.
- Write and check small changes using lean_check.
- Use compiler errors to guide the next change.
- Finish with a proof without sorry and verify it at https://scilibai.ru/grag.