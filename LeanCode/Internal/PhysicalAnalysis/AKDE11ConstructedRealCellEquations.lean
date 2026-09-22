import AKDE10OriginalRawPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
open Set
open scoped ContDiff

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient Grad.RawForward
open Grad.Constraints Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

def realCellVector {parameters : PhaseParameters} (field : ACore parameters 3) :
    SpatialPlane → ℝ → EuclideanSpace ℝ (Fin 3) :=
  fun point cell => physicalRealPart 3 (originalCellField field point cell)

def realCellPotential {parameters : PhaseParameters} (field : ACore parameters 1) :
    SpatialPlane → ℝ → ℝ :=
  fun point cell => (originalScalarCell field point cell).re

variable {parameters : PhaseParameters}

theorem realCellVector_complexify (field : ACore parameters 3)
    (real : cartesianCoreConjugation parameters field = field) :
    complexifyMapping (realCellVector field) = originalCellField field := by
  funext point cell
  exact originalRealExtendedField_complexification field real (assembleSpatialCell point cell)

theorem realCellPotential_complexify (field : ACore parameters 1)
    (real : cartesianCoreConjugation parameters field = field) :
    complexifyPotential (realCellPotential field) = originalScalarCell field := by
  funext point cell
  exact congrArg (fun value : ComplexEuclidean 1 => value 0)
    (originalRealExtendedField_complexification field real (assembleSpatialCell point cell))

theorem realCellVector_smooth (field : ACore parameters 3) :
    ContDiff ℝ ∞ (Function.uncurry (realCellVector field)) :=
  (physicalRealPart 3).contDiff.comp (originalProductField_smooth field)

theorem realCellPotential_smooth (field : ACore parameters 1) :
    ContDiff ℝ ∞ (Function.uncurry (realCellPotential field)) :=
  Complex.reCLM.contDiff.comp (originalScalarProjection.contDiff.comp (originalProductField_smooth field))

/-- Actual original raw core zero is exactly the four literal real cell
rows for the SAME real physical fields, including axis and outer circle. -/
theorem originalRealCellRows_zero (length epsilon : ℝ) (vector : ACore parameters 3) (potential : ACore parameters 1)
    (vectorReal : cartesianCoreConjugation parameters vector = vector)
    (potentialReal : cartesianCoreConjugation parameters potential = potential)
    (zero : originalRawRowsCore parameters length ((epsilon:ℂ),vector,potential) = 0)
    (point : ClosedDisk) (cell : ℝ) :
    actualRealRawRows length epsilon (realCellVector vector) (realCellPotential potential) point.val cell = 0 := by
  have literal := complexRawRows_complexify length epsilon
    (radius := (4/3 : ℝ)) (realCellVector_smooth vector).contDiffOn (realCellPotential_smooth potential).contDiffOn
    point.val (by
      rw [Metric.mem_ball,dist_zero_right]
      exact point.property.trans_lt (by norm_num)) cell
  rw [realCellVector_complexify vector vectorReal,realCellPotential_complexify potential potentialReal] at literal
  have original := originalRawRowsCore_physical length epsilon vector potential point cell
  rw [zero] at original
  funext row
  have equality := congrFun (original.trans literal) row
  have scalarZero : originalScalarCell (0 : ACore parameters 1) point.val cell = 0 := by
    unfold originalScalarCell
    rw [originalCellField_coreValue]
    simp [coreValue]
  change originalScalarCell (0 : ACore parameters 1) point.val cell =
    ((actualRealRawRows length epsilon (realCellVector vector) (realCellPotential potential) point.val cell row : ℝ) : ℂ) at equality
  rw [scalarZero] at equality
  exact Complex.ofReal_injective equality.symm

variable {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain}
    {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

def constructedCellVector (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter) :=
  realCellVector (constructedPhysicalChart scale point).2.1

def constructedCellPotential (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter) :=
  realCellPotential (constructedPhysicalChart scale point).2.2

/-- Four literal equations of the actual SAME original Newton branch. The
only analytic inputs remain the original neighborhood and actual PC inverse. -/
theorem constructedCellRows_zero (scale : OriginalNewtonScale inverse)
    (point : OriginalFiniteParameter) (member : point ∈ scale.openParameterDomain)
    (disk : ClosedDisk) (cell : ℝ) :
    actualRealRawRows cellLength point.2 (constructedCellVector scale point) (constructedCellPotential scale point) disk.val cell = 0 := by
  have stateScalar : (constructedPhysicalChart scale point).1 = (point.2 : ℂ) := by
    rw [constructedPhysicalChart_same scale point member]
    rfl
  have state : ((point.2:ℂ),(constructedPhysicalChart scale point).2.1,(constructedPhysicalChart scale point).2.2) =
      constructedPhysicalChart scale point := by
    apply Prod.ext
    · exact stateScalar.symm
    · rfl
  apply originalRealCellRows_zero cellLength point.2 _ _
    (constructedPhysicalChart_real scale point member).1 (constructedPhysicalChart_real scale point member).2
  rw [state]
  exact constructedPhysicalChart_raw_zero scale point member

end Grad.OriginalCellFamily
