import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-

 # Definition 8.4  Coupling for continuous and discrete distributions

-/

/-
\begin{defbox}{8.4}
For two continuous random variables $X$ and $Y$ with pdf's $f_X(x)$ and $f_Y(x)$, respectively, a coupling of $X$ and $Y$ is a joint pdf $f_{XY}:\mathbb{R}^2\to [0,\infty)$ such that
\[
\iint_{\mathcal{X}\times \mathcal{Y}} f_{XY}(x,y)\, dx\, dy = 1
\]
\[
f_X(x)=\int_{\mathcal{Y}} f_{XY}(x,y)\, dy,
\qquad \text{and} \qquad
f_Y(y)=\int_{\mathcal{X}} f_{XY}(x,y)\, dx.
\]

Similarly, for two discrete random variables $X$ and $Y$ with pmf's $p_X(x)$ and $p_Y(y)$, respectively, a coupling of $X$ and $Y$ is a joint pmf $p_{XY}(x,y)$ satisfying analogous properties.
\end{defbox}
-/


open MeasureTheory

/-- A joint density coupling for two continuous laws on `ℝ`, encoded by its total mass and the
two marginal density identities. -/
structure ContinuousPdfCoupling (fX fY : ℝ → ENNReal) where
  jointDensity : ℝ → ℝ → ENNReal
  totalMass : ∫⁻ p : ℝ × ℝ, jointDensity p.1 p.2 ∂(volume.prod volume) = 1
  marginal_X : ∀ x : ℝ, fX x = ∫⁻ y : ℝ, jointDensity x y ∂volume
  marginal_Y : ∀ y : ℝ, fY y = ∫⁻ x : ℝ, jointDensity x y ∂volume

/-- A joint pmf coupling for two discrete laws, encoded by the two marginal identities. -/
structure DiscretePmfCoupling {α β : Type*} [Countable α] [Countable β]
    (pX : PMF α) (pY : PMF β) where
  jointPMF : PMF (α × β)
  marginal_X : jointPMF.map Prod.fst = pX
  marginal_Y : jointPMF.map Prod.snd = pY

/-- Exported definition for Definition 8.4: both the continuous-density and discrete-pmf
versions of coupling. -/
def def_8_4 :=
  (ContinuousPdfCoupling, @DiscretePmfCoupling)
