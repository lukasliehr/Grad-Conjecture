import AKBC32SameLiteralForceCircle

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay

variable {dimension : ℕ} {parameters : PhaseParameters} {radius : RadialPoint}
    {first second : NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension}
    {circle target : CellL2 dimension}

theorem OriginalNegativeCircle.add (one : OriginalNegativeCircle parameters radius first circle)
    (two : OriginalNegativeCircle parameters radius second target) :
    OriginalNegativeCircle parameters radius (first+second) (circle+target) := by
  intro mode
  rw [negativeTraceCoefficient_add,one mode,two mode]
  exact (smul_add _ _ _).symm

theorem OriginalNegativeCircle.sub (one : OriginalNegativeCircle parameters radius first circle)
    (two : OriginalNegativeCircle parameters radius second target) :
    OriginalNegativeCircle parameters radius (first-second) (circle-target) := by
  intro mode
  rw [negativeTraceCoefficient_sub,one mode,two mode]
  exact (smul_sub _ _ _).symm

theorem OriginalNegativeCircle.smul (one : OriginalNegativeCircle parameters radius first circle) (scalar : ℂ) :
    OriginalNegativeCircle parameters radius (scalar • first) (scalar • circle) := by
  intro mode
  rw [negativeTraceCoefficient_smul,one mode]
  exact smul_comm _ _ _

theorem OriginalNegativeCircle.neg (one : OriginalNegativeCircle parameters radius first circle) :
    OriginalNegativeCircle parameters radius (-first) (-circle) := by
  simpa only [neg_one_smul] using one.smul (-1)

theorem OriginalNegativeCircle.eq_zero (one : OriginalNegativeCircle parameters radius first circle)
    (zero : circle=0) : first=0 := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [one mode,zero]
  simp only [lambdaCircleCoefficient,lp.coeFn_zero,Pi.zero_apply,smul_zero]
  exact (negativeTraceCoefficientCLM (radialKernelParameters parameters radius) 0 0 mode).map_zero.symm

end Grad.OriginalKernelCovariantRecovery
