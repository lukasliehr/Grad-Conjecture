import AKBF5FixedCellMomentAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra

 theorem originalValueKernel_cellwise {input output : ℕ} (mapping : OperatorValue input output) :
    StartupCellwise (originalValueKernel mapping) :=
  startupPointKernel_cellwise mapping (LinearIsometryEquiv.refl ℝ _)

theorem originalAverageKernel_cellwise : StartupCellwise originalAverageKernel :=
  ((originalValueKernel_cellwise positiveHelicity).comp (startupAngularKernel_cellwise _ _ _)).add
    ((originalValueKernel_cellwise negativeHelicity).comp (startupAngularKernel_cellwise _ _ _))

theorem originalTangentialKernel_cellwise : StartupCellwise originalTangentialKernel :=
  (((StartupCellwise.id 2).sub (startupPointKernel_cellwise reflectionValueMap cartesianReflectionEquiv)).comp
    originalAverageKernel_cellwise).smul (1/2 : ℂ)

theorem originalComplementKernel_cellwise : StartupCellwise originalComplementKernel :=
  ((originalValueKernel_cellwise planarInclusionMap).comp
    (originalTangentialKernel_cellwise.comp (originalValueKernel_cellwise planarPartMap))).add
  ((originalValueKernel_cellwise toroidalInclusionMap).comp
    ((startupAngularKernel_cellwise _ _ _).comp (originalValueKernel_cellwise toroidalPartMap)))

/-- The valid fixed Q0=diag(I-T,I-Pi), applied to the covariant field. -/
theorem originalCircleKernel_cellwise : StartupCellwise originalCircleKernel :=
  (StartupCellwise.id 3).sub originalComplementKernel_cellwise

theorem originalScalarInverseKernel_cellwise : StartupCellwise originalScalarInverseKernel :=
  (startupAngularKernel_cellwise _ _ _).comp ((StartupCellwise.id 1).sub (startupAngularKernel_cellwise _ _ _))

/-- Actual three-frequency moment family; each coordinate is already in the
full joint-cell L2 carrier. -/
structure StartupMoments (dimension : ℕ) where
  field : StartupL2 dimension
  moment : Fin 3 → StartupL2 dimension
  zero : moment 0 = field
  same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ grade : Fin 3, ∀ cell : ℤ,
    moment grade point cell = Grad.CellWeights.cellWeight cell ^ grade.val • field point cell

def StartupMoments.map {input output : ℕ} (family : StartupMoments input)
    (operator : StartupL2 input →L[ℂ] StartupL2 output) (diagonal : StartupCellwise operator) : StartupMoments output where
  field := operator family.field
  moment grade := operator (family.moment grade)
  zero := congrArg operator family.zero
  same := by
    apply ae_all_iff.mpr
    intro grade
    exact diagonal.moment (fun cell => Grad.CellWeights.cellWeight cell ^ grade.val) family.field (family.moment grade)
      (family.same.mono (fun _ same => same grade))

theorem StartupMoments.map_norm {input output : ℕ} (family : StartupMoments input)
    (operator : StartupL2 input →L[ℂ] StartupL2 output) (diagonal : StartupCellwise operator) (grade : Fin 3) :
    ‖(family.map operator diagonal).moment grade‖ ≤ ‖operator‖ * ‖family.moment grade‖ := operator.le_opNorm _

def StartupMoments.circle (family : StartupMoments 3) : StartupMoments 3 :=
  family.map originalCircleKernel originalCircleKernel_cellwise

def StartupMoments.scalarInverse (family : StartupMoments 1) : StartupMoments 1 :=
  family.map originalScalarInverseKernel originalScalarInverseKernel_cellwise

end Grad.CartesianStartup
