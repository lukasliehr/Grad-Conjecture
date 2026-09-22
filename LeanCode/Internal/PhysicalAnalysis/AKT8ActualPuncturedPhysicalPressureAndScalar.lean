import AKT7ActualPhysicalFourierSummability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
open Grad.SourceCollarCoefficients Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularHighGenerators Grad.AnnularRestriction
open Grad.AnnularSmoothCore Grad.AnnularIncomingIntegrability Grad.AnnularPhysicalFourier Grad.BoundaryTrace

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (decreasing : Antitone lower) (cofinal : Tendsto lower atTop (𝓝 0))
    (fields : ∀ index, CoupledSpace (lower index) length (positive index) lengthPositive)
    (allGrades : ∀ index grade, ∃ weighted : CoupledSpace (lower index) length (positive index) lengthPositive,
      CoupledInsertedGrade (lower index) length (positive index) lengthPositive grade (fields index) weighted)
    (compatible : ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing fields)

/-- The actual pressure is reconstructed by the full original Fourier
series after the original mean-free angular inverse, p=R^{-1}X. -/
def puncturedPhysicalPressure (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean 1 :=
  physicalCharacterSeries (fun mode => physicalAngularPrimitive parameters
    (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 point.1).1 mode) point.2

/-- The actual original xi field of the SAME punctured annular family. -/
def puncturedPhysicalScalar (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean 1 :=
  physicalCharacterSeries (fun mode =>
    (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 point.1).2 mode) point.2

include compatible

/-- Two genuine normalized Fourier integrals recover the original pressure
coefficient, rather than an unverified formal Fourier label. -/
theorem puncturedPhysicalPressure_coefficient (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient (fun polar =>
      puncturedPhysicalPressure parameters length lengthPositive lower positive bounded cofinal fields allGrades (radius,polar,axial)) mode.1) mode.2 =
    physicalAngularPrimitive parameters
      (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).1 mode :=
  physicalCharacterSeries_coefficient _
    (puncturedPressure_summable parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible radius inside) mode

theorem puncturedPhysicalScalar_coefficient (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient (fun polar =>
      puncturedPhysicalScalar parameters length lengthPositive lower positive bounded cofinal fields allGrades (radius,polar,axial)) mode.1) mode.2 =
    (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).2 mode :=
  physicalCharacterSeries_coefficient _
    (puncturedPhysicalPair_summable parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible radius inside).2 mode

/-- The original corrected flux is recovered exactly from pressure. -/
theorem puncturedPhysicalPressure_fluxCoefficient (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode : ℤ × ℤ) :
    (Complex.I * (mode.1 : ℂ)) • angularCoefficient (fun axial => angularCoefficient (fun polar =>
      puncturedPhysicalPressure parameters length lengthPositive lower positive bounded cofinal fields allGrades (radius,polar,axial)) mode.1) mode.2 =
    (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).1 mode := by
  rw [puncturedPhysicalPressure_coefficient parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible radius inside mode]
  exact physicalAngularPrimitive_R parameters _
    (fun cell => (puncturedPhysicalPair_meanFree parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible 0 radius inside cell).1) mode

omit decreasing compatible in
theorem puncturedPhysicalPressure_periodic (radius : ℝ) :
    (∀ axial, Function.Periodic (fun polar => puncturedPhysicalPressure parameters length lengthPositive lower positive bounded cofinal fields allGrades (radius,polar,axial)) (2*Real.pi)) ∧
    (∀ polar, Function.Periodic (fun axial => puncturedPhysicalPressure parameters length lengthPositive lower positive bounded cofinal fields allGrades (radius,polar,axial)) (2*Real.pi)) := by
  unfold puncturedPhysicalPressure
  exact ⟨fun axial => physicalCharacterSeries_angular_periodic (fun mode => physicalAngularPrimitive parameters
      (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).1 mode) axial,
    fun polar => physicalCharacterSeries_cell_periodic (fun mode => physicalAngularPrimitive parameters
      (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).1 mode) polar⟩

omit decreasing compatible in
theorem puncturedPhysicalScalar_periodic (radius : ℝ) :
    (∀ axial, Function.Periodic (fun polar => puncturedPhysicalScalar parameters length lengthPositive lower positive bounded cofinal fields allGrades (radius,polar,axial)) (2*Real.pi)) ∧
    (∀ polar, Function.Periodic (fun axial => puncturedPhysicalScalar parameters length lengthPositive lower positive bounded cofinal fields allGrades (radius,polar,axial)) (2*Real.pi)) := by
  unfold puncturedPhysicalScalar
  exact ⟨fun axial => physicalCharacterSeries_angular_periodic (fun mode =>
      (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).2 mode) axial,
    fun polar => physicalCharacterSeries_cell_periodic (fun mode =>
      (puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).2 mode) polar⟩

end Grad.ActualPuncturedFamily
