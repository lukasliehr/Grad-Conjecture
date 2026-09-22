import AKAK12LiteralDeterminantFourierRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.BoundaryTrace Grad.SourceCollarFullSource

theorem axialAngleJet_periodic (order : ℕ) (field : ℝ × ℝ → ComplexEuclidean 1)
    (shift : ℝ × ℝ) (periodic : Function.Periodic field shift) :
    Function.Periodic (angularJet order field) shift := by
  intro point
  have same : (fun input : ℝ × ℝ => field (input+shift)) = field := funext periodic
  unfold angularJet
  rw [← iteratedFDeriv_comp_add_right order shift point,same]

theorem rawDeterminantPhysicalRHS_periodic (length radius : ℝ)
    (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1) (shift : ℝ × ℝ)
    (periodic : ∀ index, Function.Periodic (fields index) shift) :
    Function.Periodic (rawDeterminantPhysicalRHS length radius fields) shift := by
  intro angles
  unfold rawDeterminantPhysicalRHS
  rw [periodic 0 angles,axialAngleJet_periodic 1 (fields 1) shift (periodic 1) angles,
    polarAngleJet_periodic 1 (fields 2) shift (periodic 2) angles,
    polarAngleJet_periodic 1 (fields 3) shift (periodic 3) angles]

def determinantPhysicalRHS (length radius : ℝ) (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1) :
    ℝ × ℝ → ComplexEuclidean 1 := removePolarMean (rawDeterminantPhysicalRHS length radius fields)

variable (length radius : ℝ) (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (angular : ∀ index, Function.Periodic (fields index) (2 * Real.pi,0))
    (cell : ∀ index, Function.Periodic (fields index) (0,2 * Real.pi))

include smooth in
theorem determinantPhysicalRHS_continuous : Continuous (determinantPhysicalRHS length radius fields) :=
  removePolarMean_continuous _ (rawDeterminantPhysicalRHS_continuous length radius fields smooth)

include angular in
theorem determinantPhysicalRHS_angular (axial : ℝ) :
    Function.Periodic (fun polar => determinantPhysicalRHS length radius fields (polar,axial)) (2 * Real.pi) := by
  intro polar
  change rawDeterminantPhysicalRHS length radius fields (polar+2*Real.pi,axial) - _ = _
  have same := rawDeterminantPhysicalRHS_periodic length radius fields (2*Real.pi,0) angular (polar,axial)
  simp only [Prod.mk_add_mk,add_zero] at same
  rw [same]
  rfl

include cell in
theorem determinantPhysicalRHS_cell (polar : ℝ) :
    Function.Periodic (fun axial => determinantPhysicalRHS length radius fields (polar,axial)) (2 * Real.pi) := by
  intro axial
  have same (query : ℝ) : rawDeterminantPhysicalRHS length radius fields (query,axial+2*Real.pi) =
      rawDeterminantPhysicalRHS length radius fields (query,axial) := by
    simpa only [Prod.mk_add_mk,add_zero] using
      rawDeterminantPhysicalRHS_periodic length radius fields (0,2*Real.pi) cell (query,axial)
  change rawDeterminantPhysicalRHS length radius fields (polar,axial+2*Real.pi) -
    angularCoefficient (fun query => rawDeterminantPhysicalRHS length radius fields (query,axial+2*Real.pi)) 0 =
    rawDeterminantPhysicalRHS length radius fields (polar,axial) -
    angularCoefficient (fun query => rawDeterminantPhysicalRHS length radius fields (query,axial)) 0
  rw [same polar,funext same]

include smooth angular cell in
theorem determinantPhysicalRHS_coefficient (mode : ℤ × ℤ) :
    doubleCoefficient (determinantPhysicalRHS length radius fields) mode =
      (if mode.1 = 0 then (0 : ℂ) else 1) •
        ((-((radius : ℂ)⁻¹)) • doubleCoefficient (fields 0) mode -
          (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • doubleCoefficient (fields 1) mode) -
          (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • doubleCoefficient (fields 2) mode) +
          frequencyNumerator (some false) mode • doubleCoefficient (fields 3) mode) := by
  have projected : doubleCoefficient (determinantPhysicalRHS length radius fields) mode =
      if mode.1 = 0 then 0 else doubleCoefficient (rawDeterminantPhysicalRHS length radius fields) mode :=
    doubleCoefficient_removePolarMean (rawDeterminantPhysicalRHS length radius fields)
      (rawDeterminantPhysicalRHS_continuous length radius fields smooth) mode
  rw [projected,rawDeterminantPhysicalRHS_coefficient length radius fields smooth angular cell]
  split_ifs <;> simp

end Grad.ActualPolarEquations
