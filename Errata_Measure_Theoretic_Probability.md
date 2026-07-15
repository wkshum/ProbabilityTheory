# Errata of "Measure-theoretic probability"

## Chapter 1 

- p.9. In the definition of RS integrabiltiy, the criterion "the upper sum and lower sum converge to the same limit" means that we can find a real number L, such that for any epsilon > 0, there exists delta > 0 so that for all partition P of [a,b] with mesh less than delta, we have |U(P, f, \alpha) - L| < epsilon and |L(P, f, \alpha) - L| < epsilon. See the definition `UpperLowerCommonLimit` in the file [def_1_2.lean](https://github.com/wkshum/ProbabilityTheory/blob/main/ProbabilityTheory/chapter_01/def_1_2.lean). With this mesh-based definition (together with the assumption that \alpha is monotonic), we can derive

 lim L(P,f,\alpha) = lim S(P,f,\alpha) = lim U(P,f,\alpha)

However, in some books, such as Rudin's "Principles of Mathematical Analysis," RS integrability is defined as the condition "the supremum over all lower sum is equal to the infimum over all upper sum". Then, it is possible that the upper sum and lower sum converge to a common limit, but the limit of S(P,f,\alpha)$ does not exist. See  [this question in stackexchange.com](https://math.stackexchange.com/questions/1186536/difference-between-riemann-stieltjes-and-darboux-stieltjes-integral).

- p.10. Theorem 1.2, part 4. The assumptions of the statement is not correct. Revise the assumptions to: Suppose $f$ is RS integrable with respect to $\alpha$ on the interval $[a,b]$. Then $f$ is RS integrable with respect to $\alpha$ on sub-intervals $[a,c]$ and $[c,b]$, and the equality in the theorem holds. This property is verified in the file [thm_1_2_4.lean](https://github.com/wkshum/ProbabilityTheory/blob/main/ProbabilityTheory/chapter_01/thm_1_2_4.lean).

- p.11. Theorem 1.4. On the right-hand side of the equation, the function $f(\alpha)$ should be $f(x)$.

- p.14. In Example 1.3.2, the function $\alpha_2(x)$ for $x$ between $-1.5$ to $1.5$ is defined as $\int_{-1.5}^x e^{-t^2/2}/\sqrt{2\pi} dt$, which is the same as the cumulative distribution function of a standard normal random variable.

## Chapter 2

- p.21, line -8, "... it is poosible to construct algebra that is not a $\sigma$-algebra".

- p.28 first line. The interval on the left hand side of the equation is $(-\infty, b]$.

- p.31 line 2. "... we can wrte $x$ as $x = y+r_1 \bmod 1$".

## Chapter 3
- p.35. In Theorem 3.1, last sentence, the condition $E \in \mathscr{F}$ should be $E \in \mathscr{F}_0$. The condition is for all events E in the algebra $F_0$.

- p.36. In the proof of Theorem 3.2, line 4, the intersection of  $(-\infty, x_i]$ should be $(-\infty, x]$, not $(-\infty, x_i]$

- p.39. In the last line of the statement of Theorem 3.5, $\sigma$-subaddtivity should be $\sigma$-subadditivity.

- p.43. line -15. In Example 3.3.6, the slope 1/6 should be 3/2.

- p.46. Definition 3.10. The definition of pi-system is missing the requirement of nonemptyness. According to wikipeida, a pi system is a nonempty collection of sets that is closed under intersection. The definition of pi system in Mathlib is not the same as in wikipeida. Mathlib requires that a pi system be  closed under intersection of non-disjoint set, without requiring that the collection is nonempty. This variation is more convenient for formalization purpose. We show in our repo that, with the additional assumption that a pi system contains the empty set, Mathlib's definition is equivalent to the usual definition of pi system.


## Chapter 4

- p.61. In the statement of Theorem 4.6, insert $f\cdot g$ after $c\cdot f$. The product $f\cdot g$ is also measurable.
  
- p.63. line 17, replace $s+\epsilon$ by $s-\epsilon$.

## Chapter 7

- p.118. Line -7, replace $\underline{g}(x)$ by $\underline{g}$, and repalce $\overline{g}(x)$ by $\overline{g}$.

- p.120. in the first paragraph of the proof, replace all $g(x)$ by $|g(x)|$.

- p.124. line -5, the last equality "=" in the proof is equality by definition $\triangleq$.

## Chapter 10

- p.165. Theorem 10.2. There is a missing $X$ after $\stackrel{a.s.}{\longrightarrow}$.

## Chapter 11

- p.193. In Exercise 11.7, want we want to prove should be
$(S_n/n)_{n=1}^\infty \text{ converges in probability to } \mu$,
where $S_n$ represents the sum $X_1+X_2+\cdots+X_n$.

## Chapter 12

- p.206. In Theorem 12.6, remove the first line $\mathbf{X}(\omega) = (\mathbf{X}_1(\omega), \mathbf{X}_2(\omega), \ldots, \mathbf{X}_n(\omega))$.

## Chapter 13

- p.221, last line. Remove "($\because B\cap A \in \mathscr{G}$)".
- p.225, last line. $d\lambda(y)$ should be $d\lambda(x)$.
