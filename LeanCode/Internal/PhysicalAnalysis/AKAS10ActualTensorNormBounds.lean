import AKAS9LiteralPrincipalTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- Every fixed value/angular/rank payment enters one finite constant. -/
def startupPrincipalFixedConstant : ℝ :=
  1 + ∑ outer : Fin 2, ∑ inner : Fin 2, ∑ row : Fin 3,
    (‖startupPrincipalFixedKernel outer inner row‖ + ‖startupPrincipalFixedFirst outer inner row‖)

theorem startupPrincipalFixedConstant_positive : 0 < startupPrincipalFixedConstant := by
  unfold startupPrincipalFixedConstant
  positivity

theorem startupTripleSummand_le_sum {First Second Third : Type*}
    [Fintype First] [Fintype Second] [Fintype Third]
    (terms : First → Second → Third → ℝ) (nonnegative : ∀ first second third, 0 ≤ terms first second third)
    (first : First) (second : Second) (third : Third) :
    terms first second third ≤ ∑ first, ∑ second, ∑ third, terms first second third := by
  calc
    _ ≤ ∑ third, terms first second third :=
      Finset.single_le_sum (fun third _ => nonnegative first second third) (Finset.mem_univ third)
    _ ≤ ∑ second, ∑ third, terms first second third :=
      Finset.single_le_sum (fun second _ => Finset.sum_nonneg (fun third _ => nonnegative first second third))
        (Finset.mem_univ second)
    _ ≤ _ := Finset.single_le_sum
      (fun first _ => Finset.sum_nonneg (fun second _ => Finset.sum_nonneg (fun third _ => nonnegative first second third)))
      (Finset.mem_univ first)

theorem startupPrincipalFixed_bounds (outer inner : Fin 2) (row : Fin 3) :
    ‖startupPrincipalFixedKernel outer inner row‖ ≤ startupPrincipalFixedConstant ∧
      ‖startupPrincipalFixedFirst outer inner row‖ ≤ startupPrincipalFixedConstant := by
  have bound := startupTripleSummand_le_sum
    (fun outer : Fin 2 => fun inner : Fin 2 => fun row : Fin 3 =>
      ‖startupPrincipalFixedKernel outer inner row‖ + ‖startupPrincipalFixedFirst outer inner row‖)
    (fun outer inner row => add_nonneg (norm_nonneg (startupPrincipalFixedKernel outer inner row))
      (norm_nonneg (startupPrincipalFixedFirst outer inner row))) outer inner row
  have total : ‖startupPrincipalFixedKernel outer inner row‖ + ‖startupPrincipalFixedFirst outer inner row‖ ≤
      startupPrincipalFixedConstant := bound.trans (le_add_of_nonneg_left zero_le_one)
  exact ⟨(le_add_of_nonneg_right (norm_nonneg (startupPrincipalFixedFirst outer inner row))).trans total,
    (le_add_of_nonneg_left (norm_nonneg (startupPrincipalFixedKernel outer inner row))).trans total⟩

theorem startupFiniteComposedBound {Index Input Output : Type*} [Fintype Index]
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    (fixed : Index → Output →L[ℂ] Output) (rows : Index → Input →L[ℂ] Output)
    (constant threshold : ℝ) (constantNonnegative : 0 ≤ constant)
    (fixedBounds : ∀ index, ‖fixed index‖ ≤ constant)
    (rowBounds : ∀ index, ‖rows index‖ ≤ threshold) :
    ‖∑ index, (fixed index).comp (rows index)‖ ≤ (Fintype.card Index : ℝ) * constant * threshold := by
  calc
    _ ≤ ∑ index, ‖(fixed index).comp (rows index)‖ := norm_sum_le _ _
    _ ≤ ∑ _index : Index, constant * threshold := Finset.sum_le_sum (fun index _ =>
      ((fixed index).opNorm_comp_le (rows index)).trans
        (mul_le_mul (fixedBounds index) (rowBounds index) (norm_nonneg (rows index)) constantNonnegative))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Quantitative smallness of the SAME four actual ER11 tensor entries,
 on both L2 and the genuine first graph, at unchanged analytic width. -/
theorem startupActualPrincipalTensor_bounds {parameters : PhaseParameters}
    {L ell rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (threshold : ℝ) (small : ActualStartupRowsSmall ledger inverseCoherent threshold)
    (outer inner : Fin 2) :
    ‖startupActualPrincipalTensorKernel admissible ledger.val ledger.property.1 inverseCoherent outer inner‖ ≤
        3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold) ∧
    ‖startupActualPrincipalTensorFirst admissible ledger.val ledger.property.1 inverseCoherent outer inner‖ ≤
        3 * startupPrincipalFixedConstant * (startupEREmbeddingConstant * threshold) := by
  have rows := startupERRowsSmall ledger inverseCoherent threshold small
  constructor
  · exact startupFiniteComposedBound (startupPrincipalFixedKernel outer inner)
      (startupERKernelRow admissible ledger.val ledger.property.1 inverseCoherent)
      startupPrincipalFixedConstant (startupEREmbeddingConstant * threshold)
      startupPrincipalFixedConstant_positive.le (fun row => (startupPrincipalFixed_bounds outer inner row).1)
      (fun row => (rows row).1.le)
  · exact startupFiniteComposedBound (startupPrincipalFixedFirst outer inner)
      (startupERFirstRow admissible ledger.val ledger.property.1 inverseCoherent)
      startupPrincipalFixedConstant (startupEREmbeddingConstant * threshold)
      startupPrincipalFixedConstant_positive.le (fun row => (startupPrincipalFixed_bounds outer inner row).2)
      (fun row => (rows row).2.le)

end Grad.CartesianStartup
