import AKAK7SamePhysicalXiRadialPDE

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

/-- Literal axial derivative Fourier law, with the original axial circle. -/
theorem axialAngleJet_doubleCoefficient (order : ℕ) (field : ℝ × ℝ → ComplexEuclidean 1)
    (smooth : ContDiff ℝ ∞ field) (periodic : Function.Periodic field (0,2 * Real.pi)) (mode : ℤ × ℤ) :
    doubleCoefficient (angularJet order field) mode =
      (Complex.I * (mode.2 : ℂ))^order • doubleCoefficient field mode := by
  unfold doubleCoefficient
  simp_rw [angularCoefficient_angularJet order field smooth periodic]
  exact angularCoefficient_smul_continuous _ _ _

theorem doubleCoefficient_const_smul (scalar : ℂ) (field : ℝ × ℝ → ComplexEuclidean 1)
    (continuousField : Continuous field) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => scalar • field angles) mode = scalar • doubleCoefficient field mode :=
  doubleCoefficient_valueMap (scalar • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) field continuousField mode

private theorem determinantCoefficientAlgebra (a b c d : ℝ × ℝ → ComplexEuclidean 1)
    (ca : Continuous a) (cb : Continuous b) (cc : Continuous c) (cd : Continuous d) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => a angles - b angles - c angles + d angles) mode =
      doubleCoefficient a mode - doubleCoefficient b mode - doubleCoefficient c mode + doubleCoefficient d mode := by
  rw [doubleCoefficient_add (fun angles => a angles - b angles - c angles) d ((ca.sub cb).sub cc) cd mode,
    doubleCoefficient_sub (fun angles => a angles - b angles) c (ca.sub cb) cc mode,
    doubleCoefficient_sub a b ca cb mode]

/-- The literal determinant radial RHS. Coordinates are (x,c,rV,g). -/
def rawDeterminantPhysicalRHS (length radius : ℝ) (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1)
    (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  (-((radius : ℂ)⁻¹)) • fields 0 angles -
    (length : ℂ)⁻¹ • angularJet 1 (fields 1) angles -
    (radius : ℂ)⁻¹ • polarAngleJet 1 (fields 2) angles + polarAngleJet 1 (fields 3) angles

variable (length radius : ℝ) (fields : Fin 4 → ℝ × ℝ → ComplexEuclidean 1)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))

include smooth

theorem rawDeterminantPhysicalRHS_continuous : Continuous (rawDeterminantPhysicalRHS length radius fields) := by
  have cx : Continuous (fun angles => (-((radius : ℂ)⁻¹)) • fields 0 angles) := (smooth 0).continuous.const_smul (-((radius : ℂ)⁻¹))
  have cc : Continuous (fun angles => (length : ℂ)⁻¹ • angularJet 1 (fields 1) angles) :=
    (angularJet_smooth 1 (fields 1) (smooth 1)).continuous.const_smul ((length : ℂ)⁻¹)
  have cv : Continuous (fun angles => (radius : ℂ)⁻¹ • polarAngleJet 1 (fields 2) angles) :=
    (polarAngleJet_smooth 1 (fields 2) (smooth 2)).continuous.const_smul ((radius : ℂ)⁻¹)
  have cg := (polarAngleJet_smooth 1 (fields 3) (smooth 3)).continuous
  exact ((cx.sub cc).sub cv).add cg

theorem rawDeterminantPhysicalRHS_coefficient
    (angular : ∀ index, Function.Periodic (fields index) (2 * Real.pi,0))
    (cell : ∀ index, Function.Periodic (fields index) (0,2 * Real.pi)) (mode : ℤ × ℤ) :
    doubleCoefficient (rawDeterminantPhysicalRHS length radius fields) mode =
      (-((radius : ℂ)⁻¹)) • doubleCoefficient (fields 0) mode -
        (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • doubleCoefficient (fields 1) mode) -
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • doubleCoefficient (fields 2) mode) +
        frequencyNumerator (some false) mode • doubleCoefficient (fields 3) mode := by
  have cx : Continuous (fun angles => (-((radius : ℂ)⁻¹)) • fields 0 angles) := (smooth 0).continuous.const_smul (-((radius : ℂ)⁻¹))
  have cc : Continuous (fun angles => (length : ℂ)⁻¹ • angularJet 1 (fields 1) angles) :=
    (angularJet_smooth 1 (fields 1) (smooth 1)).continuous.const_smul ((length : ℂ)⁻¹)
  have cv : Continuous (fun angles => (radius : ℂ)⁻¹ • polarAngleJet 1 (fields 2) angles) :=
    (polarAngleJet_smooth 1 (fields 2) (smooth 2)).continuous.const_smul ((radius : ℂ)⁻¹)
  have cg := (polarAngleJet_smooth 1 (fields 3) (smooth 3)).continuous
  unfold rawDeterminantPhysicalRHS
  rw [determinantCoefficientAlgebra
    (fun angles => (-((radius : ℂ)⁻¹)) • fields 0 angles)
    (fun angles => (length : ℂ)⁻¹ • angularJet 1 (fields 1) angles)
    (fun angles => (radius : ℂ)⁻¹ • polarAngleJet 1 (fields 2) angles)
    (polarAngleJet 1 (fields 3)) cx cc cv cg mode,
    doubleCoefficient_const_smul,doubleCoefficient_const_smul,doubleCoefficient_const_smul,
    axialAngleJet_doubleCoefficient 1 (fields 1) (smooth 1) (cell 1),
    polarAngleJet_doubleCoefficient 1 (fields 2) (smooth 2) (angular 2),
    polarAngleJet_doubleCoefficient 1 (fields 3) (smooth 3) (angular 3)]
  · simp only [pow_one,frequencyNumerator]
  · exact (polarAngleJet_smooth 1 (fields 2) (smooth 2)).continuous
  · exact (angularJet_smooth 1 (fields 1) (smooth 1)).continuous
  · exact (smooth 0).continuous

end Grad.ActualPolarEquations
