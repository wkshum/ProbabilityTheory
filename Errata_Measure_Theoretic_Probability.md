# Errata of "Measure-theoretic probability"

## Chapter 1 

- p.9. Change the definition of Riemann-Stieltjes integral to a more restrictive one, by requireing that the upper limit $U(P,f,\alpha)$, the lower limit $L(P,f,\alpha)$, and the tagged sum $S(P,f,\alpha)$ all converges to the same limit. That is take the equality

\lim L(P,f,\alpha) = lim S(P,f,\alpha) = lim U(P,f,\alpha)

as the definition of RS integrable. In practical scenario, we will not encounter any example in which the above three limits are not equal. However, in theory, it is possible that the upper sum and lower sum converge and converge to the same value, but the limit of S(P,f,\alpha)$ does not exist. See  [his question in stackexchange.com](https://math.stackexchange.com/questions/1186536/difference-between-riemann-stieltjes-and-darboux-stieltjes-integral).

- p.10. Theorem 1.2, part 4. The assumptions of the statement is not correct. Revise the assumptions to: Suppose $f$ is RS integrable with respect to $\alpha$ on the interval $[a,b]$. Then $f$ is RS integrable with respect to $\alpha$ on sub-intervals $[a,c]$ and $[c,b]$, and the equality in the theorem holds.

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
