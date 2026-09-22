import AKBP29NativeRemainderMomentPayments
import AKBP27SameWeakMeanFirstRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Actual native fields and completed coefficient outputs, with their
already paid joint-cell moments. The force fields include original Qrad. -/
structure StartupNativeERRows where
  covariant : StartupMoments 3
  knownForce : StartupMoments 2
  forceCorrection : StartupMoments 2
  knownThird : StartupMoments 1
  thirdCorrection : StartupMoments 1
  determinant : StartupMoments 1
  planarFlux : StartupMoments 2
  scalarFlux : StartupMoments 1

namespace StartupNativeERRows
def circle (rows : StartupNativeERRows) : StartupMoments 3 := rows.covariant.circle
def vector (rows : StartupNativeERRows) : StartupMoments 2 := rows.circle.value planarPartMap
def scalar (rows : StartupNativeERRows) : StartupMoments 1 := rows.circle.value toroidalPartMap
def gradient (rows : StartupNativeERRows) : StartupMoments 2 :=
  rows.vector.recoveredGradient (rows.knownForce.sub rows.forceCorrection)
def currentFlux (rows : StartupNativeERRows) : StartupMoments 2 :=
  rows.planarFlux.sub (((rows.forceCorrection.average).value quarterValueMap).smul (1/2))
def sourceFlux (rows : StartupNativeERRows) : StartupMoments 2 :=
  ((rows.knownForce.average).value quarterValueMap).smul (1/2)
def principalTensor (rows : StartupNativeERRows) (outer inside : Fin 2) : StartupL2 3 :=
  startupThreeRowTensor rows.forceCorrection.field rows.thirdCorrection.field rows.currentFlux.field outer inside
def knownTensor (rows : StartupNativeERRows) (outer inside : Fin 2) : StartupL2 3 :=
  startupThreeRowTensor (-rows.knownForce.field) rows.knownThird.field rows.sourceFlux.field outer inside
def tensor (rows : StartupNativeERRows) (outer inside : Fin 2) : StartupL2 3 :=
  rows.principalTensor outer inside + rows.knownTensor outer inside
def tensorMoment (rows : StartupNativeERRows) (grade : Fin 3) (outer inside : Fin 2) : StartupL2 3 :=
  startupThreeRowTensor (rows.forceCorrection.moment grade) (rows.thirdCorrection.moment grade) (rows.currentFlux.moment grade) outer inside +
    startupThreeRowTensor (-(rows.knownForce.moment grade)) (rows.knownThird.moment grade) (rows.sourceFlux.moment grade) outer inside
def flux (rows : StartupNativeERRows) (scale : ℝ) (direction : Fin 2) : StartupL2 3 :=
  startupNativeLowerFlux scale rows.determinant rows.scalar rows.scalarFlux rows.gradient direction
def fluxFirst (rows : StartupNativeERRows) (scale : ℝ) (direction : Fin 2) : StartupL2 3 :=
  startupNativeLowerFluxFirst scale rows.determinant rows.scalar rows.scalarFlux rows.gradient direction

theorem tensor_moment (rows : StartupNativeERRows) (grade : Fin 3) (outer inside : Fin 2) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ grade.val)
      (rows.tensorMoment grade outer inside) (rows.tensor outer inside) :=
  (startupNativeTensor_moment rows.forceCorrection rows.currentFlux rows.thirdCorrection grade outer inside).add
    ((rows.knownForce.related grade).neg.threeRowTensor (fun _ _ _ _ => rfl)
      (rows.knownThird.related grade) (rows.sourceFlux.related grade) outer inside)

theorem tensor_first (rows : StartupNativeERRows) (outer inside : Fin 2) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell)
      (rows.tensorMoment 1 outer inside) (rows.tensor outer inside) := by
  simpa only [Fin.val_one,pow_one] using rows.tensor_moment 1 outer inside

theorem tensor_second (rows : StartupNativeERRows) (outer inside : Fin 2) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2)
      (rows.tensorMoment 2 outer inside) (rows.tensor outer inside) := rows.tensor_moment 2 outer inside

theorem flux_first (rows : StartupNativeERRows) (scale : ℝ) (direction : Fin 2) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell)
      (rows.fluxFirst scale direction) (rows.flux scale direction) :=
  startupNativeLowerFlux_first scale rows.determinant rows.scalar rows.scalarFlux rows.gradient direction

end StartupNativeERRows

structure StartupNativeERRowsRelated (symbol : ℤ → Spatial → ℝ) (weighted original : StartupNativeERRows) : Prop where
  covariant : StartupRadialRelated symbol weighted.covariant.field original.covariant.field
  knownForce : StartupRadialRelated symbol weighted.knownForce.field original.knownForce.field
  forceCorrection : StartupRadialRelated symbol weighted.forceCorrection.field original.forceCorrection.field
  knownThird : StartupRadialRelated symbol weighted.knownThird.field original.knownThird.field
  thirdCorrection : StartupRadialRelated symbol weighted.thirdCorrection.field original.thirdCorrection.field
  determinant : StartupRadialRelated symbol weighted.determinant.field original.determinant.field
  planarFlux : StartupRadialRelated symbol weighted.planarFlux.field original.planarFlux.field
  scalarFlux : StartupRadialRelated symbol weighted.scalarFlux.field original.scalarFlux.field

namespace StartupNativeERRowsRelated
variable {symbol : ℤ → Spatial → ℝ} {weighted original : StartupNativeERRows}
variable (same : StartupNativeERRowsRelated symbol weighted original)
variable (radial : ∀ cell (first second : Spatial), ‖first‖ = ‖second‖ → symbol cell first = symbol cell second)

include same radial in
theorem circle : StartupRadialRelated symbol weighted.circle.field original.circle.field := same.covariant.radialCircle radial
include same radial in
theorem vector : StartupRadialRelated symbol weighted.vector.field original.vector.field := (same.circle radial).value planarPartMap
include same radial in
theorem scalar : StartupRadialRelated symbol weighted.scalar.field original.scalar.field := (same.circle radial).value toroidalPartMap
include same radial in
theorem gradient : StartupRadialRelated symbol weighted.gradient.field original.gradient.field :=
  (same.vector radial).recoveredGradient radial (same.knownForce.sub same.forceCorrection)
include same radial in
theorem currentFlux : StartupRadialRelated symbol weighted.currentFlux.field original.currentFlux.field :=
  same.planarFlux.sub (((same.forceCorrection.radialAverage radial).value quarterValueMap).smul (1/2))
include same radial in
theorem sourceFlux : StartupRadialRelated symbol weighted.sourceFlux.field original.sourceFlux.field :=
  ((same.knownForce.radialAverage radial).value quarterValueMap).smul (1/2)
include same radial in
theorem tensor (outer inside : Fin 2) : StartupRadialRelated symbol (weighted.tensor outer inside) (original.tensor outer inside) :=
  (same.forceCorrection.threeRowTensor radial same.thirdCorrection (same.currentFlux radial) outer inside).add
    (same.knownForce.neg.threeRowTensor radial same.knownThird (same.sourceFlux radial) outer inside)
include same radial in
theorem flux (scale : ℝ) (direction : Fin 2) : StartupRadialRelated symbol (weighted.flux scale direction) (original.flux scale direction) :=
  startupNativeLowerFlux_phase radial scale weighted.determinant weighted.scalar weighted.scalarFlux
    original.determinant original.scalar original.scalarFlux weighted.gradient original.gradient
    same.determinant (same.scalar radial) same.scalarFlux (same.gradient radial) direction
end StartupNativeERRowsRelated

structure StartupNativeWeakRows (scale : ℝ) (psi : StartupL2 1) (rows : StartupNativeERRows) : Prop where
  force : StartupWeakProjectedForceEquation psi (originalValueKernel planarPartMap rows.covariant.field)
    (rows.knownForce.field-rows.forceCorrection.field)
  third : StartupWeakThirdEquation (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
    (originalScalarInverseKernel psi) (originalValueKernel toroidalPartMap rows.covariant.field)
    (rows.knownThird.field+rows.thirdCorrection.field)
  determinant : StartupWeakDeterminantEquation (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
    (originalValueKernel planarPartMap rows.covariant.field) (originalValueKernel toroidalPartMap rows.covariant.field)
    rows.determinant.field rows.planarFlux.field rows.scalarFlux.field
  mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0

theorem StartupNativeWeakRows.divDiv {scale : ℝ} {psi : StartupL2 1} {rows : StartupNativeERRows}
    (weak : StartupNativeWeakRows scale psi rows) :
    StartupWeakDivDivEquation rows.circle.field 0 rows.tensor (rows.flux scale) :=
  startupSame_weakMean_firstRows_divDiv scale psi rows.knownThird.field rows.thirdCorrection.field rows.determinant.field
    rows.scalarFlux.field rows.covariant.field rows.knownForce.field rows.forceCorrection.field rows.planarFlux.field
    (rows.scalar.moment 1) (rows.scalarFlux.moment 1) (rows.gradient.moment 1)
    rows.scalar.first_related rows.scalarFlux.first_related rows.gradient.first_related
    weak.force weak.third weak.determinant weak.mean

end Grad.CartesianStartup
