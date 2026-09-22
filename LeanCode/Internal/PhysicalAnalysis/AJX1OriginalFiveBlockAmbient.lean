import AJM4ExactOriginalSolvedGraphConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularFullGraph
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource

/-- The four measured source/residual blocks of AK31. The last coordinate
is the original strengthened full G3, encoding its first angular norm. -/
abbrev OriginalFullSourceBlocks (parameters : PhaseParameters) (lower : ℝ) :=
  WithLp 2 (HighKnownGraphHilbert parameters lower ×
    WithLp 2 (DivisionRow 1 lower × DivisionRow 1 lower))

/-- The original retained X graph together with exactly F0, F2, full F1 and
full G3. The equivalent Hilbert norm adds no incoming or outer trace term. -/
abbrev OriginalFiveBlockAmbient (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) :=
  WithLp 2 (OriginalCoupledSpace lower length positive × OriginalFullSourceBlocks parameters lower)

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)

def originalFiveBlockSum (field : OriginalFiveBlockAmbient parameters lower length positive) : ℝ :=
  ‖field.ofLp.1‖ + ‖field.ofLp.2.ofLp.1.ofLp.1‖ + ‖field.ofLp.2.ofLp.1.ofLp.2‖ +
    ‖field.ofLp.2.ofLp.2.ofLp.1‖ + ‖field.ofLp.2.ofLp.2.ofLp.2‖

theorem originalFiveBlock_norm_sq (field : OriginalFiveBlockAmbient parameters lower length positive) :
    ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2.ofLp.1.ofLp.1‖ ^ 2 +
      ‖field.ofLp.2.ofLp.1.ofLp.2‖ ^ 2 + ‖field.ofLp.2.ofLp.2.ofLp.1‖ ^ 2 +
      ‖field.ofLp.2.ofLp.2.ofLp.2‖ ^ 2 := by
  have outer := WithLp.prod_norm_sq_eq_of_L2 field
  have sources := WithLp.prod_norm_sq_eq_of_L2 field.ofLp.2
  have copied := WithLp.prod_norm_sq_eq_of_L2 field.ofLp.2.ofLp.1
  have residuals := WithLp.prod_norm_sq_eq_of_L2 field.ofLp.2.ofLp.2
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at outer
  change ‖field.ofLp.2‖ ^ 2 = ‖field.ofLp.2.ofLp.1‖ ^ 2 + ‖field.ofLp.2.ofLp.2‖ ^ 2 at sources
  change ‖field.ofLp.2.ofLp.1‖ ^ 2 = ‖field.ofLp.2.ofLp.1.ofLp.1‖ ^ 2 + ‖field.ofLp.2.ofLp.1.ofLp.2‖ ^ 2 at copied
  change ‖field.ofLp.2.ofLp.2‖ ^ 2 = ‖field.ofLp.2.ofLp.2.ofLp.1‖ ^ 2 + ‖field.ofLp.2.ofLp.2.ofLp.2‖ ^ 2 at residuals
  linarith only [outer,sources,copied,residuals]

theorem originalFiveBlock_norm_le_sum (field : OriginalFiveBlockAmbient parameters lower length positive) :
    ‖field‖ ≤ originalFiveBlockSum parameters lower length positive field := by
  have outer := hilbert_norm_le_add field
  have sources := hilbert_norm_le_add field.ofLp.2
  have copied := hilbert_norm_le_add field.ofLp.2.ofLp.1
  have residuals := hilbert_norm_le_add field.ofLp.2.ofLp.2
  unfold originalFiveBlockSum
  linarith only [outer,sources,copied,residuals]

private theorem five_sum_sq_le (a b c d e : ℝ) :
    (a+b+c+d+e)^2 ≤ 5*(a^2+b^2+c^2+d^2+e^2) := by
  nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),sq_nonneg (a-e),
    sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (b-e),sq_nonneg (c-d),sq_nonneg (c-e),sq_nonneg (d-e)]

theorem originalFiveBlock_sum_le (field : OriginalFiveBlockAmbient parameters lower length positive) :
    originalFiveBlockSum parameters lower length positive field ≤ Real.sqrt 5 * ‖field‖ := by
  have square := five_sum_sq_le ‖field.ofLp.1‖ ‖field.ofLp.2.ofLp.1.ofLp.1‖
    ‖field.ofLp.2.ofLp.1.ofLp.2‖ ‖field.ofLp.2.ofLp.2.ofLp.1‖ ‖field.ofLp.2.ofLp.2.ofLp.2‖
  rw [← originalFiveBlock_norm_sq parameters lower length positive field] at square
  change (originalFiveBlockSum parameters lower length positive field)^2 ≤ 5*‖field‖^2 at square
  apply (sq_le_sq₀ (by unfold originalFiveBlockSum; positivity) (by positivity)).mp
  calc
    _ ≤ 5*‖field‖^2 := square
    _ = (Real.sqrt 5 * ‖field‖)^2 := by rw [mul_pow,Real.sq_sqrt (by norm_num)]

end Grad.AnnularFullGraph
