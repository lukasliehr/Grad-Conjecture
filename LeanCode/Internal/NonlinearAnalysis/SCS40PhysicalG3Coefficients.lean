import SCS39DoubleCoefficientAlgebra

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.QuotientProjection Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryTrace

variable (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
  (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
  (source : SmoothQuotient parameters) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)

theorem physicalCorrection_coefficient {grade : ℕ} (large : 3 ≤ grade) (mode : ℤ × ℤ) :
    doubleCoefficient (physicalCorrection parameters L epsilon field source radius nonnegative bounded) mode =
      actualSourceProductCoefficient parameters L rho epsilon field small large (quotientEta parameters grade source)
        radius nonnegative bounded 0 mode +
      actualSourceProductCoefficient parameters L rho epsilon field small large (quotientEta parameters grade source)
        radius nonnegative bounded 1 mode -
      actualSourceProductCoefficient parameters L rho epsilon field small large (quotientEta parameters grade source)
        radius nonnegative bounded 2 mode -
      angularCoefficient (originalDividedSourceCells parameters L large (quotientEta parameters grade source)
        mode.2 radius nonnegative bounded 1) mode.1 := by
  let products : Fin 3 → ℝ × ℝ → ComplexEuclidean 1 := fun component angles =>
    physicalKappaDeviation parameters L epsilon field radius nonnegative bounded component angles •
      physicalDividedSources parameters L source radius nonnegative bounded component angles
  have continuousProducts (component : Fin 3) : Continuous (products component) :=
    (physicalKappaDeviation_continuous parameters L rho epsilon field small radius nonnegative bounded component).smul
      (physicalDividedSources_continuous parameters L source radius nonnegative bounded component)
  have continuousCircle := physicalDividedSources_continuous parameters L source radius nonnegative bounded 1
  change doubleCoefficient (fun angles => products 0 angles + products 1 angles - products 2 angles -
    physicalDividedSources parameters L source radius nonnegative bounded 1 angles) mode = _
  rw [doubleCoefficient_sub (fun angles => products 0 angles + products 1 angles - products 2 angles)
    (physicalDividedSources parameters L source radius nonnegative bounded 1)
    (((continuousProducts 0).add (continuousProducts 1)).sub (continuousProducts 2)) continuousCircle,
    doubleCoefficient_sub (fun angles => products 0 angles + products 1 angles) (products 2)
    ((continuousProducts 0).add (continuousProducts 1)) (continuousProducts 2),
    doubleCoefficient_add (products 0) (products 1) (continuousProducts 0) (continuousProducts 1)]
  have productLaw (component : Fin 3) : doubleCoefficient (products component) mode =
      actualSourceProductCoefficient parameters L rho epsilon field small large (quotientEta parameters grade source)
        radius nonnegative bounded component mode :=
    (actualSourceProductCoefficient_physical parameters L rho epsilon field small large source radius nonnegative bounded component mode).symm
  rw [productLaw 0, productLaw 1, productLaw 2, originalDividedSourceCells_core]
  congr 1
  unfold doubleCoefficient
  simp_rw [physicalDividedSources_axialCoefficient]

def physicalG3 (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  (L : ℂ)⁻¹ • corePolarValue parameters (source 2) radius nonnegative bounded angles +
    removePolarMean (physicalCorrection parameters L epsilon field source radius nonnegative bounded) angles

include small in
theorem physicalG3_continuous : Continuous (physicalG3 parameters L epsilon field source radius nonnegative bounded) :=
  ((continuous_const : Continuous (fun _ : ℝ × ℝ => (L : ℂ)⁻¹)).smul
    (corePolarValue_continuous parameters (source 2) radius nonnegative bounded)).add
    (removePolarMean_continuous _ (physicalCorrection_continuous parameters L rho epsilon field small source radius nonnegative bounded))

theorem actualG3Coefficient_physical {grade : ℕ} (large : 3 ≤ grade) (mode : ℤ × ℤ) :
    actualG3Coefficient parameters L rho epsilon field small large (quotientEta parameters grade source)
      radius nonnegative bounded mode =
    doubleCoefficient (physicalG3 parameters L epsilon field source radius nonnegative bounded) mode := by
  have scalarContinuous : Continuous (fun angles => (L : ℂ)⁻¹ • corePolarValue parameters (source 2) radius nonnegative bounded angles) :=
    (continuous_const : Continuous (fun _ : ℝ × ℝ => (L : ℂ)⁻¹)).smul
      (corePolarValue_continuous parameters (source 2) radius nonnegative bounded)
  change _ = doubleCoefficient (fun angles => (L : ℂ)⁻¹ • corePolarValue parameters (source 2) radius nonnegative bounded angles +
    removePolarMean (physicalCorrection parameters L epsilon field source radius nonnegative bounded) angles) mode
  rw [doubleCoefficient_add (fun angles => (L : ℂ)⁻¹ • corePolarValue parameters (source 2) radius nonnegative bounded angles)
    (removePolarMean (physicalCorrection parameters L epsilon field source radius nonnegative bounded)) scalarContinuous
    (removePolarMean_continuous _ (physicalCorrection_continuous parameters L rho epsilon field small source radius nonnegative bounded))]
  have projected := doubleCoefficient_removePolarMean
    (physicalCorrection parameters L epsilon field source radius nonnegative bounded)
    (physicalCorrection_continuous parameters L rho epsilon field small source radius nonnegative bounded) mode
  change doubleCoefficient (removePolarMean (physicalCorrection parameters L epsilon field source radius nonnegative bounded)) mode =
    if mode.1 = 0 then 0 else doubleCoefficient (physicalCorrection parameters L epsilon field source radius nonnegative bounded) mode at projected
  rw [projected, physicalCorrection_coefficient parameters L rho epsilon field small source radius nonnegative bounded large]
  unfold actualG3Coefficient
  congr 1
  unfold doubleCoefficient
  have inner (polar : ℝ) : angularCoefficient (fun axial => (L : ℂ)⁻¹ •
      corePolarValue parameters (source 2) radius nonnegative bounded (polar, axial)) mode.2 =
      (L : ℂ)⁻¹ • ((source 2).val mode.2).value (polarClosedPoint radius polar nonnegative bounded) := by
    change angularCoefficient ((L : ℂ)⁻¹ • (fun axial => corePolarValue parameters (source 2)
      radius nonnegative bounded (polar, axial))) mode.2 = _
    rw [angularCoefficient_smul_continuous, corePolarValue_axialCoefficient]
  simp_rw [inner]
  rw [show (fun polar => (L : ℂ)⁻¹ • ((source 2).val mode.2).value
      (polarClosedPoint radius polar nonnegative bounded)) = (L : ℂ)⁻¹ •
      (fun polar => ((source 2).val mode.2).value (polarClosedPoint radius polar nonnegative bounded)) from rfl,
    angularCoefficient_smul_continuous]
  congr 2
  funext angle
  rw [show quotientEta parameters grade source 2 = aGradeEta parameters (GradeCore.ofCoreLinear (source 2)) from rfl,
    completedOriginalCell_core]
  rfl

end Grad.SourceCollarFullSource
