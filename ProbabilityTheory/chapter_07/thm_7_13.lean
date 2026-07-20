import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Integration
import ProbabilityTheory.chapter_06.def_6_3
import ProbabilityTheory.chapter_05.thm_5_2


/-

  # Theorem 7.13 E[XY]=E[X]E[Y] if X, Y are independent

-/

/-
\begin{thmbox}{7.13}
Suppose $X$ and $Y$ are random variables defined on a common probability space $(\Omega,\mathcal{F},P)$. If $X$ and $Y$ are independent and if $E[X]$, $E[Y]$, and $E[XY]$ are all finite, then
\begin{equation}
E[XY]=E[X]E[Y].
\tag{7.10}
\end{equation}
\end{thmbox}

\textit{Proof} We first suppose that $X$ and $Y$ are indicator functions. Suppose $X=1_A$ and $Y=1_B$ for some sets $A$ and $B$. Since $X$ and $Y$ are measurable, the sets $A$ and $B$ are both $\mathcal{F}$-measurable. Moreover, since $X$ and $Y$ are independent, the events $A$ and $B$ are independent. Therefore,
\[
E[1_A1_B] = E[1_{A\cap B}] = P(A\cap B) = P(A)P(B) = E[1_A]E[1_B].
\]

By linearity, (7.10) holds when $X$ and $Y$ are independent simple functions.

Suppose $X$ and $Y$ are nonnegative, measurable, and independent random variables. Let $X_n$'s and $Y_n$'s be simple nonnegative functions obtained by the method mentioned after Definition 6.3. For each $n$, $X_n$ and $Y_n$ are independent because $X_n$ is a function of $X$ and $Y_n$ is a function of $Y$, and $X$ and $Y$ are independent (Theorem 5.2). Furthermore, we have $X_nY_n \nearrow XY$ because $X_n \nearrow X$ and $Y_n \nearrow Y$. By the monotone convergence theorem,
\[
E[XY]
=
\lim_n E[X_nY_n]
=
\lim_n (E[X_n]E[Y_n])
=
(\lim_n E[X_n])(\lim_n E[Y_n]),
\]
which is the same as $E[X]E[Y]$.

Suppose $X$ and $Y$ are in $L^1(P)$. Let $X^+$ and $X^-$ denote the positive and negative parts of $X$, respectively, and let $Y^+$ and $Y^-$ denote the positive and negative parts of $Y$, respectively. We note that the pair of random variables $(X^+,X^-)$ is independent with $(Y^+,Y^-)$ because $X^+=\max(X,0)$ and $X^-=\max(-X,0)$ are functions of $X$ and $Y^+=\max(Y,0)$ and $Y^-=\max(-Y,0)$ are functions of $Y$ (Theorem 5.2). Then, we can write
\[
E[XY]=E[(X^+-X^-)(Y^+-Y^-)]
\]
\[
= E[X^+]E[Y^+] - E[X^+]E[Y^-] - E[X^-]E[Y^+] + E[X^-]E[Y^-]
\]
\[
= (E[X^+]-E[X^-])(E[Y^+]-E[Y^-])
\]
\[
= E[X]E[Y].
\]

This establishes (7.10) for nonnegative random variables $X$ and $Y$. \hfill $\square$
-/

open MeasureTheory

/--  ## Theorem 7.13
for independent real-valued random variables on a common measure space,
the expectation of the product equals the product of expectations.  The textbook
finiteness assumptions are encoded by `Integrable X μ`, `Integrable Y μ`, and
`Integrable (fun ω => X ω * Y ω) μ`.
-/
theorem thm_7_13 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hXY : def_5_2 μ X Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (_hXY_int : Integrable (fun ω => X ω * Y ω) μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by
  simpa [def_5_2] using
    (ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral
      (μ := μ) (X := X) (Y := Y) hXY hX.1 hY.1)
