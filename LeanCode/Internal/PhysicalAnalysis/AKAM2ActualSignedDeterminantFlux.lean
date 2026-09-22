import AKAM1FullMatrixFluxIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.ActualSmoothPhysicalField Grad.ActualPhysicalField Grad.ActualCartesianDescent
open Grad.ActualCartesianIntegrability Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.BoundaryTrace
open Grad.SourceCollarFullSource Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℕ → ℝ) (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow 3 (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 3 (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

include compatible in
theorem cartesianCovariantRows_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (lower second) (lower first) (decreasing ordered)
      (cartesianCovariantRow (lower second) (rows second)) = cartesianCovariantRow (lower first) (rows first) := by
  rw [cartesianCovariantRow_restriction,compatible first second ordered]

/-- The SAME AM20 signed flux B w, with the mandatory Cartesian covariant Q a_c. -/
def cofactorFluxCell (cell : ℤ) : SpatialPlane → ComplexEuclidean 3 :=
  matrixFluxCell parameters (originalCofactorFamily parameters length epsilon base)
    (originalCofactorFamily_estimate parameters length rho epsilon base small).actualCoherent
    lower positive bounded cofinal (fun index => cartesianCovariantRow (lower index) (rows index))
    (fun index => (curves index).cartesianCovariant) cell

include compatible in
theorem cofactorFluxCell_integrable_pair (K : ℝ) (estimate : ∀ index,‖rows index‖ ≤ K) (cell : ℤ) :
    IntegrableOn (cofactorFluxCell parameters length rho epsilon base small lower positive bounded cofinal rows curves cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖cofactorFluxCell parameters length rho epsilon base small lower positive bounded cofinal rows curves cell point‖) openUnitDisk := by
  apply matrixFluxCell_integrable_pair parameters (originalCofactorFamily parameters length epsilon base)
    (originalCofactorFamily_estimate parameters length rho epsilon base small).actualCoherent
    lower positive bounded cofinal decreasing (fun index => cartesianCovariantRow (lower index) (rows index))
    (fun index => (curves index).cartesianCovariant)
    (cartesianCovariantRows_compatible lower decreasing rows compatible) (5*K)
  intro index
  exact (cartesianCovariantRow_bound (lower index) (rows index)).trans
    (mul_le_mul_of_nonneg_left (estimate index) (by norm_num))

include compatible in
/-- Exact Fourier coefficient of delta H Q a_c, retaining the original determinant sign. -/
theorem cofactorFluxCell_actual (cell : ℤ) (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) (polar : ℝ) :
    cofactorFluxCell parameters length rho epsilon base small lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      angularCoefficient (fun axial => WithLp.toLp 2
        ((originalPhysicalSignedCofactor parameters length epsilon base axial
          (polarClosedPoint radius polar ((positive index).le.trans inside.1) inside.2)).mulVec
          (cartesianCovariantValue polar ((curves index).fullField (bounded index) (radius,polar,axial))))) cell := by
  rw [cofactorFluxCell,matrixFluxCell_actual parameters (originalCofactorFamily parameters length epsilon base)
    (originalCofactorFamily_estimate parameters length rho epsilon base small).actualCoherent
    lower positive bounded cofinal decreasing (fun index => cartesianCovariantRow (lower index) (rows index))
    (fun index => (curves index).cartesianCovariant)
    (cartesianCovariantRows_compatible lower decreasing rows compatible) cell index radius inside polar]
  congr 1
  funext axial
  rw [originalCofactorFamily_eq_signedCofactor parameters length rho epsilon base small,
    (curves index).fullField_cartesianCovariant (bounded index) radius inside (polar,axial)]

/-- AM20 has exactly the original L,L,1 column normalization. -/
def determinantFluxProjection (length : ℝ) (component : Fin 3) : ComplexEuclidean 3 →L[ℝ] ℂ :=
  (((if component=2 then 1 else (length : ℂ)) •
    PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) component)).restrictScalars ℝ

def determinantFluxComponent (cell : ℤ) (component : Fin 3) (point : SpatialPlane) : ℂ :=
  determinantFluxProjection length component
    (cofactorFluxCell parameters length rho epsilon base small lower positive bounded cofinal rows curves cell point)

include compatible in
theorem determinantFluxComponent_integrable_pair (K : ℝ) (estimate : ∀ index,‖rows index‖ ≤ K) (cell : ℤ) (component : Fin 3) :
    IntegrableOn (determinantFluxComponent parameters length rho epsilon base small lower positive bounded cofinal rows curves cell component) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖determinantFluxComponent parameters length rho epsilon base small lower positive bounded cofinal rows curves cell component point‖) openUnitDisk := by
  have given := cofactorFluxCell_integrable_pair parameters length rho epsilon base small lower positive bounded cofinal decreasing rows curves compatible K estimate cell
  exact Grad.PhysicalAxisEquation.boundedPhysicalFlux_integrable_pair openUnitDisk _ given.1 given.2
    (fun _ => determinantFluxProjection length component) aestronglyMeasurable_const
    ‖determinantFluxProjection length component‖ (Eventually.of_forall (fun _ => le_rfl))

include compatible in
theorem determinantFluxComponent_actual (cell : ℤ) (component : Fin 3) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (polar : ℝ) :
    determinantFluxComponent parameters length rho epsilon base small lower positive bounded cofinal rows curves cell component
      (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      (if component=2 then 1 else (length : ℂ)) *
      (angularCoefficient (fun axial => WithLp.toLp 2
        ((originalPhysicalSignedCofactor parameters length epsilon base axial
          (polarClosedPoint radius polar ((positive index).le.trans inside.1) inside.2)).mulVec
          (cartesianCovariantValue polar ((curves index).fullField (bounded index) (radius,polar,axial))))) cell) component := by
  unfold determinantFluxComponent
  rw [cofactorFluxCell_actual parameters length rho epsilon base small lower positive bounded cofinal decreasing rows curves compatible cell index radius inside polar]
  rfl

end Grad.ActualCartesianFlux
