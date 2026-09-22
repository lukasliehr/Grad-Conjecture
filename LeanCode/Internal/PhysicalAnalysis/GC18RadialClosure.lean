import GC18LaplacianGenerator

noncomputable section

set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Frame
open Grad.RepresentedKernel.SpatialProduct Grad.Constraints Grad.NonlinearDivision
open Grad.NonlinearRadial Grad.NonlinearQuotientBounds Grad.PhysicalFamily

theorem angular_single_zero_column (L sigma gamma ell : ℝ) (grade : ℕ) (cell other : ℤ)
    {input output : ℕ} (field : SmoothOperatorJet input output) (column : PhysicalValue input)
    (point : ClosedDisk) :
    coefficientDerivative (coefficientAngularMap L sigma gamma ell grade input output
      (singleJetCoefficient L sigma gamma ell grade cell field)) other (zeroDerivativeIndexAt grade) point column =
      if other = cell then (angularClosedJet 0 (operatorJetColumn field column)).value point else 0 := by
  rw [angular_single_column]
  change (if other = cell then closedDerivative (angularClosedJet 0 (operatorJetColumn field column))
    0 (derivativeWord (zeroDerivativeIndexAt grade)) point else 0) = _
  have word : derivativeWord (zeroDerivativeIndexAt grade) = emptyCartesianWord :=
    funext (fun index => Fin.elim0 (show Fin 0 from index))
  rw [word, closedDerivative_zero_order]

theorem angular_operatorJetColumn_radial {input output : ℕ} (field : SmoothOperatorJet input output)
    (column : PhysicalValue input) : IsRotationInvariant (angularClosedJet 0 (operatorJetColumn field column)) := by
  intro angle point
  have equality := angularClosedJet_rotation_value 0 (operatorJetColumn field column) angle point
  simpa only [Grad.NonlinearDivision.rotatedPoint, Grad.GaugeCoefficients.Radial.rotatedPoint,
    physicalRotation_eq_orthogonal, planeRotationEquiv_apply, angularCharacter_zero_mode, one_smul] using equality

/-- A continuous linear residual for the exact radial-division identity. -/
def radialDivisionResidual {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input output : ℕ) (cell : ℤ) (point : ClosedDisk) :
    Coefficient L sigma gamma ell 2 input output →L[ℂ] OperatorValue input output :=
  ((seedCellCLM L sigma gamma ell 2 input output cell (zeroDerivativeIndexAt 2) point -
    seedCellCLM L sigma gamma ell 2 input output cell (zeroDerivativeIndexAt 2) closedOrigin).comp
      (coefficientAngularMap L sigma gamma ell 2 input output)) -
  ((‖point.val‖ ^ 2 : ℝ) : ℂ) • ((seedCellCLM L sigma gamma ell 0 input output cell (zeroDerivativeIndexAt 0) point).comp
    ((coefficientRadialMap admissible 0 input output).comp
      ((coefficientLaplacianMap L sigma gamma ell 0 input output).comp
        (coefficientAngularMap L sigma gamma ell 2 input output))))

theorem radialDivisionResidual_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input output : ℕ) (cell other : ℤ) (field : SmoothOperatorJet input output) (point : ClosedDisk) :
    radialDivisionResidual admissible input output other point
      (singleJetCoefficient L sigma gamma ell 2 cell field) = 0 := by
  apply ContinuousLinearMap.ext
  intro column
  change (coefficientDerivative (coefficientAngularMap L sigma gamma ell 2 input output
      (singleJetCoefficient L sigma gamma ell 2 cell field)) other (zeroDerivativeIndexAt 2) point column -
    coefficientDerivative (coefficientAngularMap L sigma gamma ell 2 input output
      (singleJetCoefficient L sigma gamma ell 2 cell field)) other (zeroDerivativeIndexAt 2) closedOrigin column) -
    ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientDerivative (coefficientRadialMap admissible 0 input output
      (coefficientLaplacianMap L sigma gamma ell 0 input output
        (coefficientAngularMap L sigma gamma ell 2 input output
          (singleJetCoefficient L sigma gamma ell 2 cell field)))) other (zeroDerivativeIndexAt 0) point column = 0
  rw [angular_single_zero_column, angular_single_zero_column, radial_laplacian_angular_single_column]
  by_cases same : other = cell
  · simp only [if_pos same]
    rw [radialJet_identity_sub_origin _ (angular_operatorJetColumn_radial field column) point,
      Complex.coe_smul, sub_self]
  · simp only [if_neg same, sub_self, smul_zero]

theorem radialDivisionResidual_core {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input output : ℕ) (cell : ℤ) (point : ClosedDisk)
    (core : smoothCore L sigma gamma ell 2 input output) :
    radialDivisionResidual admissible input output cell point
      (coreInclusion L sigma gamma ell 2 input output core) = 0 := by
  let mapping := (radialDivisionResidual admissible input output cell point).toLinearMap.comp
    (coreInclusion L sigma gamma ell 2 input output)
  change mapping core = 0
  have membership := core.property
  generalize valueEq : core.val = value at membership
  have proof : ∀ (membership : value ∈ smoothCore L sigma gamma ell 2 input output),
      mapping ⟨value, membership⟩ = 0 := by
    intro membership
    refine Submodule.span_induction (p := fun value membership => mapping ⟨value, membership⟩ = 0)
      ?_ ?_ ?_ ?_ membership
    · intro generator member
      rcases member with ⟨⟨other, field⟩, rfl⟩
      exact radialDivisionResidual_single admissible input output other cell field point
    · exact mapping.map_zero
    · intro first second firstIn secondIn firstZero secondZero
      change mapping (⟨first, firstIn⟩ + ⟨second, secondIn⟩) = 0
      rw [map_add, firstZero, secondZero, add_zero]
    · intro scalar value member vanish
      change mapping (scalar • ⟨value, member⟩) = 0
      rw [map_smul, vanish]
      exact smul_zero (M := ℂ) (A := OperatorValue input output) scalar
  have coreEq : core = ⟨value, membership⟩ := Subtype.ext valueEq
  rw [coreEq]
  exact proof membership

/-- AO9 on the actual coefficient completion, by density of its original
smooth closed-jet graph. No radial smoothness is assumed of a rough input. -/
theorem coefficientRadialDivision {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input output : ℕ) (coefficient : Coefficient L sigma gamma ell 2 input output)
    (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative (coefficientAngularMap L sigma gamma ell 2 input output coefficient)
        cell (zeroDerivativeIndexAt 2) point -
      coefficientDerivative (coefficientAngularMap L sigma gamma ell 2 input output coefficient)
        cell (zeroDerivativeIndexAt 2) closedOrigin =
      ((‖point.val‖ ^ 2 : ℝ) : ℂ) • coefficientDerivative
        (coefficientRadialMap admissible 0 input output
          (coefficientLaplacianMap L sigma gamma ell 0 input output
            (coefficientAngularMap L sigma gamma ell 2 input output coefficient)))
        cell (zeroDerivativeIndexAt 0) point := by
  have equality := (finiteCellCore_dense (L := L) (sigma := sigma) (gamma := gamma) (ell := ell) 2 input output).equalizer
    (radialDivisionResidual admissible input output cell point).continuous continuous_const
    (funext (fun core => radialDivisionResidual_core admissible input output cell point core))
  have vanish := congrFun equality coefficient
  exact sub_eq_zero.mp vanish

end Grad.GaugeCoefficients.Physical.RadialLedger
