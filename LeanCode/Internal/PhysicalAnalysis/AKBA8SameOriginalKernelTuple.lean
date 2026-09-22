import AKBA7ActualRawFluxCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularCurrentEnergy
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.OriginalKernelRetainedDecay Grad.SourceCollarAngular Grad.AnnularOriginalSmoothCore
open Grad.NonlinearQuotientBounds Grad.Constraints

theorem originalMeanFreeLowCurves_mean {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : ℝ) (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    originalPhysicalCoefficient (curves.meanFree.fullField bounded) radius (0,cell)=0 := by
  rw [originalPhysicalCoefficient,curves.meanFree.fullField_coefficient bounded radius inside (0,cell),
    curves.meanFree.physicalCurve_coefficient bounded 0 radius inside (0,cell)]
  change (_ : ℂ) • ((if (0:ℤ)=0 then (0:ℂ) else 1) • curves.curve 0 radius (0,cell))=0
  simp

theorem originalCoreLowCurves_mean {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    (field : ACore parameters 1) (mean : angularCore parameters 0 field=0)
    (bounded : lower<1) (radius : ℝ) (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    originalPhysicalCoefficient ((originalCoreLowCurves parameters lower positive bounded field).fullField bounded) radius (0,cell)=0 := by
  rw [originalPhysicalCoefficient,SmoothLowPhysicalRow.fullField_coefficient _ bounded radius inside (0,cell),
    originalCoreLowCurves_physical_coefficient parameters lower positive bounded field radius inside (0,cell),
    ← originalCoreCircleTrace_represents parameters field ⟨radius,positive.le.trans inside.1,inside.2⟩ (0,cell)]
  unfold lambdaCircleCoefficient
  rw [originalCoreCircleTrace_mean parameters field mean _ cell,smul_zero]

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

def originalKernelPField : OriginalPhysicalField :=
  (originalRawFluxCurves parameters length rho epsilon base small lower positive bounded
    (originalVectorLowCurves parameters lower positive bounded vector)
    (originalCoreLowCurves parameters lower positive bounded (originalKernelXi total vector scalar))).2.meanFree.fullField bounded

def originalKernelXiField : OriginalPhysicalField :=
  (originalCoreLowCurves parameters lower positive bounded (originalKernelXi total vector scalar)).fullField bounded

/-- Exact original four-field smooth tuple (p,xi,0,0), with original phase and
all radial/tangential grades. Its membership is constructed, not assumed. -/
def originalKernelSmoothTuple : OriginalSmoothTuple parameters lower := by
  let raw := originalRawFluxCurves parameters length rho epsilon base small lower positive bounded
    (originalVectorLowCurves parameters lower positive bounded vector)
    (originalCoreLowCurves parameters lower positive bounded (originalKernelXi total vector scalar))
  refine ⟨![originalKernelPField parameters length rho epsilon base small lower positive bounded total vector scalar,
    originalKernelXiField parameters lower positive bounded total vector scalar,0,0],?_,?_⟩
  · intro slot
    fin_cases slot
    · exact originalWeightedPhysicalSmooth_of_lowCurves raw.2.meanFree bounded
    · exact originalWeightedPhysicalSmooth_of_lowCurves
        (originalCoreLowCurves parameters lower positive bounded (originalKernelXi total vector scalar)) bounded
    · exact originalWeightedPhysicalSmooth_zero parameters lower
    · exact originalWeightedPhysicalSmooth_zero parameters lower
  · intro slot nonFull radius inside cell
    fin_cases slot
    · exact originalMeanFreeLowCurves_mean raw.2 bounded radius inside cell
    · exact originalCoreLowCurves_mean (originalKernelXi total vector scalar)
        (originalKernelXi_mean total vector scalar) bounded radius inside cell
    · exact (nonFull rfl).elim
    · simp [originalPhysicalCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]

end Grad.OriginalKernelGraphRestriction
