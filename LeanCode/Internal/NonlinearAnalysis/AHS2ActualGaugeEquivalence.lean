import AHS1GaugeMeanContraction

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)
private abbrev rp := radialKernelParameters parameters r

/-- The two missing angular means are the actual Gamma inverse applied to
literal gauge-row means. This is the existing correction, not a new inverse. -/
def radialGaugeTailCorrection (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3) :
    NegativeTrace (rp parameters r) angular cell 2 :=
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialNegativeGammaInverseKernel parameters L compact state r small)
    (fullNegativeKernelAction (rp parameters r) angular cell
      (radialGaugeMeanRowsKernel parameters L compact state r) input)

theorem radialGaugeTailCorrection_constant (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3) :
    IsAngularConstant (rp parameters r) angular cell
      (radialGaugeTailCorrection parameters L compact state r small angular cell input) := by
  apply (radialNegativeGammaInverseKernel_angularDiagonal parameters L compact state r small).action_constant
  unfold radialGaugeMeanRowsKernel
  rw [fullNegativeKernelAction_comp]
  exact angularMeanKernel_action_constant _ _ _ _

theorem radialGaugeQKernel_action_eq (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3) :
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialGaugeQKernel parameters L compact state r small) input =
    input + fullNegativeKernelAction (rp parameters r) angular cell
      (tailInjectionKernel (rp parameters r))
      (radialGaugeTailCorrection parameters L compact state r small angular cell input) := by
  simp only [radialGaugeQKernel, radialGaugeCorrectionKernel, radialGaugeTailCorrection,
    fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]

theorem radialPhysicalGaugeMeans_add_tail (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3)
    (tail : NegativeTrace (rp parameters r) angular cell 2)
    (supported : IsAngularConstant (rp parameters r) angular cell tail)
    (baseMean : fullNegativeKernelAction (rp parameters r) angular cell
      (angularMeanKernel (rp parameters r) 2)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (gaugeTailProjectionKernel (rp parameters r)) input) = 0) :
    radialPhysicalGaugeMeans parameters L compact state r angular cell
      (input + fullNegativeKernelAction (rp parameters r) angular cell
        (tailInjectionKernel (rp parameters r)) tail) =
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialGaugeMeanRowsKernel parameters L compact state r) input +
      (tail + fullNegativeKernelAction (rp parameters r) angular cell
        (radialGammaDeviationKernel parameters L compact state r) tail) := by
  unfold radialPhysicalGaugeMeans
  rw [map_add, map_add, baseMean, gaugeTailProjection_injection,
    angularMean_action_constant_eq _ _ _ _ supported, zero_add, map_add,
    radialGaugeMeanRows_tail_constant parameters L compact state r angular cell tail supported]
  abel

/-- AE8/AE9, both directions: among all angularly constant tail corrections,
the two original gauge means vanish exactly for the actual constructed correction. -/
theorem radialGauge_constraint_iff (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3)
    (tail : NegativeTrace (rp parameters r) angular cell 2)
    (supported : IsAngularConstant (rp parameters r) angular cell tail)
    (baseMean : fullNegativeKernelAction (rp parameters r) angular cell
      (angularMeanKernel (rp parameters r) 2)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (gaugeTailProjectionKernel (rp parameters r)) input) = 0) :
    radialPhysicalGaugeMeans parameters L compact state r angular cell
      (input + fullNegativeKernelAction (rp parameters r) angular cell
        (tailInjectionKernel (rp parameters r)) tail) = 0 ↔
      tail = radialGaugeTailCorrection parameters L compact state r small angular cell input := by
  rw [radialPhysicalGaugeMeans_add_tail parameters L compact state r angular cell input tail supported baseMean]
  let negativeGamma := fullKernelNegativeIdentityPerturbation (rp parameters r)
    (fullKernelNeg (radialGammaDeviationKernel parameters L compact state r))
  have equation (value : NegativeTrace (rp parameters r) angular cell 2) :
      fullNegativeKernelAction (rp parameters r) angular cell negativeGamma value =
        -(value + fullNegativeKernelAction (rp parameters r) angular cell
          (radialGammaDeviationKernel parameters L compact state r) value) := by
    simp only [negativeGamma, fullKernelNegativeIdentityPerturbation,
      fullNegativeKernelAction_sub, fullNegativeKernelAction_neg,
      fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply]
    abel
  constructor
  · intro zero
    have solved : fullNegativeKernelAction (rp parameters r) angular cell negativeGamma tail =
        fullNegativeKernelAction (rp parameters r) angular cell
          (radialGaugeMeanRowsKernel parameters L compact state r) input := by
      rw [equation]
      exact (eq_neg_of_add_eq_zero_left zero).symm
    have applied := congrArg (fullNegativeKernelAction (rp parameters r) angular cell
      (radialNegativeGammaInverseKernel parameters L compact state r small)) solved
    rw [← ContinuousLinearMap.comp_apply, ← fullNegativeKernelAction_comp,
      (radialNegativeGammaInverseKernel_twoSided parameters L compact state r small).2,
      fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply] at applied
    exact applied
  · intro same
    subst tail
    have applied := congrArg (fun kernel => fullNegativeKernelAction (rp parameters r) angular cell kernel
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialGaugeMeanRowsKernel parameters L compact state r) input))
      (radialNegativeGammaInverseKernel_twoSided parameters L compact state r small).1
    rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
      fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply] at applied
    change fullNegativeKernelAction (rp parameters r) angular cell negativeGamma
      (radialGaugeTailCorrection parameters L compact state r small angular cell input) = _ at applied
    rw [equation] at applied
    rw [← applied]
    exact neg_add_cancel _

theorem radialGaugeQKernel_gauged (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3)
    (baseMean : fullNegativeKernelAction (rp parameters r) angular cell
      (angularMeanKernel (rp parameters r) 2)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (gaugeTailProjectionKernel (rp parameters r)) input) = 0) :
    radialPhysicalGaugeMeans parameters L compact state r angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialGaugeQKernel parameters L compact state r small) input) = 0 := by
  rw [radialGaugeQKernel_action_eq]
  exact (radialGauge_constraint_iff parameters L compact state r small angular cell input _
    (radialGaugeTailCorrection_constant parameters L compact state r small angular cell input)
    baseMean).mpr rfl

end Grad.AnnularReconstruction
