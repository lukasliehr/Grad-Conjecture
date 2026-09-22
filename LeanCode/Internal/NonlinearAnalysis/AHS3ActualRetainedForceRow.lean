import AHS2ActualGaugeEquivalence

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollar Grad.BoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Ledger

/-- AD10's retained force row is literally twice the first row of
(RF)^T F^{-T}, in the original polar frame. -/
def originalRetainedForceRow (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (axialAngle polarAngle : ℝ)
    (point : ClosedDisk) (component : Fin 3) : ℂ :=
  let frame := originalPhysicalFrameMatrix parameters L epsilon field axialAngle point
  let rotated := rotatedPhysicalFrameMatrix parameters 1 1 epsilon field axialAngle point *
    Matrix.diagonal ![1, 1, (L : ℂ)⁻¹]
  2 * ((rotated * polarDomainMatrix polarAngle + frame * polarDomainDerivative polarAngle).transpose *
    ((polarDomainMatrix polarAngle).transpose * frame⁻¹).transpose) 0 component

theorem originalRetainedForceRow_deviation (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (axialAngle polarAngle : ℝ) (point : ClosedDisk) (component : Fin 3) :
    originalRetainedForceRow parameters L epsilon field axialAngle polarAngle point component =
      2 * polarMatrixEntry 0 component polarAngle
        (originalForceMatrix parameters L epsilon field axialAngle point) +
      if component = 1 then 2 else 0 := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  have invId := (originalInverseFamily_matrix_identity parameters L epsilon field margin.2.2 0 axialAngle point).2
  rw [originalInverseFamily_eq_matrixInverse parameters L rho epsilon field low] at invId
  dsimp only [originalRetainedForceRow]
  rw [polarForceProduct _ _ _ invId]
  rw [polarMatrixEntry_matrix]
  have circular : ((polarDomainDerivative polarAngle).transpose * polarDomainMatrix polarAngle) 0 component =
      if component = 1 then 1 else 0 := by
    have circle := Complex.sin_sq_add_cos_sq (polarAngle : ℂ)
    fin_cases component <;>
      simp [polarDomainDerivative, polarDomainMatrix, Matrix.mul_apply, Fin.sum_univ_three,
        physicalRadialVector, physicalTangentialVector, physicalToroidalVector]
    all_goals ring_nf
    all_goals linear_combination circle
  rw [Matrix.add_apply, circular]
  dsimp only [originalForceMatrix]
  split_ifs <;> ring

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev forceFamily := forceMatrixFamily parameters L state.data.epsilon state.data.field
private abbrev forceCoherent := forceMatrixFamily_coherent parameters L state.data.rho
  state.data.epsilon state.data.field state.low

def radialRetainedForceBaseCoefficient (component : Fin 3) : ℤ × ℤ → ℂ :=
  polarEntryScalar parameters (forceFamily parameters L compact state)
    (forceCoherent parameters L compact state) 0 component 0 r.val

theorem radialRetainedForceBaseCoefficient_moments (component : Fin 3) (moment : ℕ) :
    Summable (productMoment parameters moment r.val
      (radialRetainedForceBaseCoefficient parameters L compact state r component)) :=
  polarEntryScalarMoment_summable parameters _ _ 0 component moment 0 r.val r.property.1 r.property.2

/-- The actual r1 coefficient kernel restores +2e_theta, with no assumed row. -/
def radialRetainedForceKernel : RadialKernel parameters r 3 1 :=
  fullKernelAdd
    (fullKernelSmul 2 (radialRowKernel parameters r 3
      (radialRetainedForceBaseCoefficient parameters L compact state r)
      (radialRetainedForceBaseCoefficient_moments parameters L compact state r)))
    (fullKernelSmul 2 (coordinateProjectionKernel (radialKernelParameters parameters r) 3 1))

/-- Exact coefficient fidelity to the original retained AD10 row. -/
theorem radialRetainedForceBaseCoefficient_doubleCoefficient (component : Fin 3) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
      polarMatrixEntry 0 component angle
        (originalForceMatrix parameters L state.data.epsilon state.data.field axialAngle
          (polarClosedPoint r.val angle r.property.1 r.property.2))) mode.2) mode.1 =
      radialRetainedForceBaseCoefficient parameters L compact state r component mode := by
  have exactCoefficient := polarEntry_doubleCoefficient parameters
    (forceFamily parameters L compact state) (forceCoherent parameters L compact state)
    0 component r.val r.property.1 r.property.2 mode
  dsimp only [forceFamily] at exactCoefficient
  simp_rw [forceMatrixFamily_actual parameters L state.data.rho state.data.epsilon state.data.field state.low] at exactCoefficient
  exact exactCoefficient

end Grad.AnnularReconstruction
