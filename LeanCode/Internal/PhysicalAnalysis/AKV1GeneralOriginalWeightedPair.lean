import AKR37LiteralTotalCoreOriginalGraphClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSystem Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)

/-- The actual original field, at its original phase and every inserted Fourier grade.
The definition has no source-core or solution regularity hypothesis. -/
def conjugatedOriginalPairCurve (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  (conjugatedCoupledXSection parameters lower length positive bounded lengthPositive grade field
      (radialClamp lower bounded.le radius),
    conjugatedCoupledXiSection parameters lower length positive bounded lengthPositive grade field
      (radialClamp lower bounded.le radius))

def originalPairCurve (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive grade field
      (radialClamp lower bounded.le radius),
    sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive grade field
      (radialClamp lower bounded.le radius))

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
  CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

theorem conjugatedOriginalPairCurve_continuous (grade : ℕ) :
    Continuous (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) :=
  ((conjugatedCoupledXSection_continuous parameters lower length positive bounded lengthPositive field allGrades grade).prodMk
    (conjugatedCoupledXiSection_continuous parameters lower length positive bounded lengthPositive field allGrades grade)).comp
    (radialClamp_continuous lower bounded.le)

theorem conjugatedOriginalPairCurve_coefficient (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius) =
      Real.exp (radialPhase parameters radius mode.2) •
        (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field grade ⟨radius,inside⟩ mode,
          sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field grade ⟨radius,inside⟩ mode) := by
  unfold conjugatedOriginalPairCurve
  rw [radialClamp_eq lower bounded.le radius inside]
  exact Prod.ext
    (conjugatedCoupledXSection_physical parameters lower length positive bounded lengthPositive field allGrades grade _ mode)
    (conjugatedCoupledXiSection_physical parameters lower length positive bounded lengthPositive field allGrades grade _ mode)

theorem conjugatedOriginalPairCurve_grade (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius) =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade • hilbertPairCoefficient mode
        (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field 0 radius) := by
  rw [conjugatedOriginalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades grade radius inside mode,
    conjugatedOriginalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades 0 radius inside mode,
    sameCoupledXCoefficient_grade, sameCoupledXiCoefficient_grade, Complex.ofReal_pow]
  apply Prod.ext
  · exact smul_comm (Real.exp (radialPhase parameters radius mode.2))
      ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade)
      (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 ⟨radius,inside⟩ mode)
  · exact smul_comm (Real.exp (radialPhase parameters radius mode.2))
      ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade)
      (sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 ⟨radius,inside⟩ mode)

theorem conjugatedOriginalPairCurve_shift (grade reserve : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+reserve) radius) =
      (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^reserve • hilbertPairCoefficient mode
        (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius) := by
  rw [conjugatedOriginalPairCurve_grade parameters lower length positive bounded lengthPositive field allGrades (grade+reserve) radius inside mode,
    conjugatedOriginalPairCurve_grade parameters lower length positive bounded lengthPositive field allGrades grade radius inside mode,
    pow_add, mul_smul]
  exact smul_comm ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^grade)
    ((Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)^reserve) _

theorem conjugatedOriginalPairCurve_reserve (grade reserve : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    physicalPairReserve parameters reserve
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+reserve) radius) =
      conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius :=
  physicalPairReserve_same parameters reserve _ _
    (conjugatedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive field allGrades grade reserve radius inside)

end Grad.AnnularGeneralSourceRegularity
