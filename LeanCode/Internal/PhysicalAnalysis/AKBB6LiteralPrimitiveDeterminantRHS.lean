import AKBB5PrimitiveDeterminantSymbol
import AKAV1LiteralOriginalG3Periodic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.ActualPolarEquations Grad.ActualOriginalThirdSource

/-- Literal p equation before its compulsory mean projection; fields are
(p,b3,rV,G3) in the original normalizations. -/
def rawPrimitiveDeterminantRHS (length radius : ℝ)
    (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  (-((radius : ℂ)⁻¹)) • fields 0 angles -
    (length : ℂ)⁻¹ • angularJet 1 (fields 1) angles -
    (radius : ℂ)⁻¹ • fields 2 angles + fields 3 angles

def primitiveDeterminantRHS (length radius : ℝ) (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1) :
    ℝ × ℝ → ComplexEuclidean 1 := removePolarMean (rawPrimitiveDeterminantRHS length radius fields)

variable (length radius : ℝ) (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))

include smooth

theorem rawPrimitiveDeterminantRHS_continuous : Continuous (rawPrimitiveDeterminantRHS length radius fields) :=
  ((((smooth 0).continuous.const_smul (-((radius : ℂ)⁻¹))).sub
    ((angularJet_smooth 1 (fields 1) (smooth 1)).continuous.const_smul ((length : ℂ)⁻¹))).sub
      ((smooth 2).continuous.const_smul ((radius : ℂ)⁻¹))) |>.add (smooth 3).continuous

theorem primitiveDeterminantRHS_continuous : Continuous (primitiveDeterminantRHS length radius fields) :=
  removePolarMean_continuous _ (rawPrimitiveDeterminantRHS_continuous length radius fields smooth)

omit smooth in
theorem rawPrimitiveDeterminantRHS_periodic (shift : ℝ × ℝ)
    (periodic : ∀ index, Function.Periodic (fields index) shift) :
    Function.Periodic (rawPrimitiveDeterminantRHS length radius fields) shift := by
  intro angles
  unfold rawPrimitiveDeterminantRHS
  rw [periodic 0 angles,axialAngleJet_periodic 1 (fields 1) shift (periodic 1) angles,
    periodic 2 angles,periodic 3 angles]

omit smooth in
theorem primitiveDeterminantRHS_periodic
    (angular : ∀ index, Function.Periodic (fields index) (2 * Real.pi,0))
    (cell : ∀ index, Function.Periodic (fields index) (0,2 * Real.pi)) :
    (∀ axial, Function.Periodic (fun polar => primitiveDeterminantRHS length radius fields (polar,axial)) (2*Real.pi)) ∧
    (∀ polar, Function.Periodic (fun axial => primitiveDeterminantRHS length radius fields (polar,axial)) (2*Real.pi)) := by
  apply removePolarMean_periodic
  · intro axial polar
    simpa only [Prod.mk_add_mk,add_zero] using
      rawPrimitiveDeterminantRHS_periodic length radius fields (2*Real.pi,0) angular (polar,axial)
  · intro polar axial
    simpa only [Prod.mk_add_mk,add_zero] using
      rawPrimitiveDeterminantRHS_periodic length radius fields (0,2*Real.pi) cell (polar,axial)

omit smooth in
private theorem primitiveCoefficientAlgebra (a b c d : ℝ × ℝ → ComplexEuclidean 1)
    (ca : Continuous a) (cb : Continuous b) (cc : Continuous c) (cd : Continuous d) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => a angles - b angles - c angles + d angles) mode =
      doubleCoefficient a mode - doubleCoefficient b mode - doubleCoefficient c mode + doubleCoefficient d mode := by
  rw [doubleCoefficient_add (fun angles => a angles - b angles - c angles) d ((ca.sub cb).sub cc) cd mode,
    doubleCoefficient_sub (fun angles => a angles - b angles) c (ca.sub cb) cc mode,
    doubleCoefficient_sub a b ca cb mode]

theorem rawPrimitiveDeterminantRHS_coefficient
    (cell : ∀ index, Function.Periodic (fields index) (0,2 * Real.pi)) (mode : ℤ × ℤ) :
    doubleCoefficient (rawPrimitiveDeterminantRHS length radius fields) mode =
      (-((radius : ℂ)⁻¹)) • doubleCoefficient (fields 0) mode -
        (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • doubleCoefficient (fields 1) mode) -
        (radius : ℂ)⁻¹ • doubleCoefficient (fields 2) mode + doubleCoefficient (fields 3) mode := by
  unfold rawPrimitiveDeterminantRHS
  rw [primitiveCoefficientAlgebra
    (fun angles => (-((radius : ℂ)⁻¹)) • fields 0 angles)
    (fun angles => (length : ℂ)⁻¹ • angularJet 1 (fields 1) angles)
    (fun angles => (radius : ℂ)⁻¹ • fields 2 angles)
    (fields 3)
    ((smooth 0).continuous.const_smul (-((radius : ℂ)⁻¹)))
    ((angularJet_smooth 1 (fields 1) (smooth 1)).continuous.const_smul ((length : ℂ)⁻¹))
    ((smooth 2).continuous.const_smul ((radius : ℂ)⁻¹)) (smooth 3).continuous mode,
    doubleCoefficient_const_smul,doubleCoefficient_const_smul,doubleCoefficient_const_smul,
    axialAngleJet_doubleCoefficient 1 (fields 1) (smooth 1) (cell 1)]
  · simp only [pow_one,frequencyNumerator]
  · exact (smooth 2).continuous
  · exact (angularJet_smooth 1 (fields 1) (smooth 1)).continuous
  · exact (smooth 0).continuous

theorem primitiveDeterminantRHS_coefficient
    (cell : ∀ index, Function.Periodic (fields index) (0,2 * Real.pi)) (mode : ℤ × ℤ) :
    doubleCoefficient (primitiveDeterminantRHS length radius fields) mode =
      primitiveDeterminantModeRHS length radius mode (fun index => doubleCoefficient (fields index) mode) := by
  have projected : doubleCoefficient (removePolarMean (rawPrimitiveDeterminantRHS length radius fields)) mode =
      if mode.1 = 0 then 0 else doubleCoefficient (rawPrimitiveDeterminantRHS length radius fields) mode :=
    doubleCoefficient_removePolarMean (rawPrimitiveDeterminantRHS length radius fields)
      (rawPrimitiveDeterminantRHS_continuous length radius fields smooth) mode
  change doubleCoefficient (removePolarMean (rawPrimitiveDeterminantRHS length radius fields)) mode = _
  rw [projected,rawPrimitiveDeterminantRHS_coefficient length radius fields smooth cell]
  unfold primitiveDeterminantModeRHS
  split_ifs <;> simp

end Grad.ActualPolarFlux
