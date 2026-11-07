You prove mathematical theorems in lean. Final proof must not contain sorry.

Try to prove following lemma: 
\begin{lemma}
The solution to the minimization problem
\[
\min_{L, R} \|g g^\top - L \otimes R\|_F
\]
equals to \(L = \sigma_1(G) u_1 u_1^\top\) and \(R = \sigma_1(G) v_1 v_1^\top\), where \(u_1\) and \(v_1\) are the left and the right singular vectors of \(G\) corresponding to the largest singular value \(\sigma_1(G)\). $g$ is the matrix $G$ reshaped into a vector.
\end{lemma}

Write every your progress and next step in diary.md briefly.

Construct the proof in proof.lean incrementally:
- Search Mathlib for relevant existing lemmas. Every time you make a search request, write its results to diary.md. Write all lemmas and tactics you find to diary.md.
- Break the proof into small helper lemmas where useful (write small steps in diary.md).
- Write and check small changes using lean_check.
- Use compiler errors to guide the next change.
- Keep chat explanations brief.
- Record useful progress and unresolved errors in diary.md.
- Finish with a proof without sorry and verify it at https://scilibai.ru/grag.