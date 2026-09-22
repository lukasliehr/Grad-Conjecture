import SCS22OriginalFlatConsumer

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarRestriction
open Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def polarCirclePoint (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (angle : CellCircle) : ClosedDisk :=
  ⟨radius • boundaryCirclePoint angle, by
    change ‖radius • boundaryCirclePoint angle‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg nonnegative, boundaryCirclePoint_norm, mul_one]
    exact bounded⟩

theorem polarCirclePoint_continuous (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Continuous (polarCirclePoint radius nonnegative bounded) :=
  ((continuous_const : Continuous (fun _ : CellCircle => radius)).smul boundaryCirclePoint_continuous).subtype_mk _

theorem polarCirclePoint_coe (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    polarCirclePoint radius nonnegative bounded (angle : CellCircle) = polarClosedPoint radius angle nonnegative bounded := by
  apply Subtype.ext
  change radius • boundaryCirclePoint (angle : CellCircle) = polarPlane (radius, angle)
  rw [boundaryCirclePoint_coe, polarPlane_eq]
  rfl

variable (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
  (component : Fin 3) (cell : ℤ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)

def kappaCircleTerm (slot : Fin 2 × Fin 2) : C(CellCircle, ℂ) where
  toFun angle := cellCharacter (kappaLaurentFrequency component slot) angle *
    (coefficientColumnJet parameters
      (mappedCofactorFamily parameters L epsilon field (scalarRowMapping (tangentialLaurentVector slot.1)))
      (mappedCofactorFamily_coherent parameters L rho epsilon field _ small) cell
      (kappaLaurentRight component slot.2)).value (polarCirclePoint radius nonnegative bounded angle) 0
  continuous_toFun := (cellCharacter _).continuous.mul
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp
      ((coefficientColumnJet parameters _
        (mappedCofactorFamily_coherent parameters L rho epsilon field _ small) cell _).value.continuous.comp
        (polarCirclePoint_continuous radius nonnegative bounded)))

def kappaCircle : C(CellCircle, ℂ) :=
  ∑ slot, kappaCircleTerm parameters L rho epsilon field small component cell radius nonnegative bounded slot

theorem kappaCircle_coe (angle : ℝ) :
    kappaCircle parameters L rho epsilon field small component cell radius nonnegative bounded (angle : CellCircle) =
      kappaPolarCell parameters L rho epsilon field small component cell (radius, angle) 0 := by
  simp only [kappaCircle, ContinuousMap.sum_apply, kappaCircleTerm, ContinuousMap.coe_mk,
    kappaPolarCell, Finset.sum_apply]
  change _ = (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0)
    (∑ slot, kappaPolarCellTerm parameters L rho epsilon field small component slot cell (radius, angle))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro slot _
  rw [cellCharacter_coe, polarCirclePoint_coe]
  simp only [kappaPolarCellTerm, angularCharacterField, originalPolarValue_closed _ radius angle nonnegative bounded]
  rfl

theorem kappaCircle_coefficient (mode : ℤ) :
    fourierCoeff (kappaCircle parameters L rho epsilon field small component cell radius nonnegative bounded) mode =
      kappaScalar parameters L rho epsilon field small component 0 radius (mode, cell) := by
  rw [← angularCoefficient_circle]
  simp_rw [kappaCircle_coe]
  have projection := angularCoefficient_component
    (fun angle => kappaPolarCell parameters L rho epsilon field small component cell (radius, angle))
    ((kappaPolarCell_smooth parameters L rho epsilon field small component cell).continuous.comp
      (continuous_const.prodMk continuous_id)) 0 mode
  exact projection.symm.trans (congrArg (fun value : ComplexEuclidean 1 => value 0)
    (kappaPolarCell_coefficient parameters L rho epsilon field small component cell mode 0 radius))

end Grad.SourceCollarFullSource
