import AKV39SameUnweightedRadialRegularity
import AJU10ClosedHilbertFourierReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.BoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceCollarAngular
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators Grad.PhaseAlgebra
open Grad.AnnularCoupledInverse Grad.AnnularCrossOrbit Grad.AnnularWeightedSmoothness Grad.AnnularPhysicalFourier
open Grad.AnnularClosedJointRegularity

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)

def originalPhysicalComponentCurve (component : Fin 2) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  if component = 0 then (originalPairCurve parameters lower length positive bounded lengthPositive field grade radius).1
  else (originalPairCurve parameters lower length positive bounded lengthPositive field grade radius).2

def originalPhysicalComponentField (component : Fin 2) : ℝ × (ℝ × ℝ) → ComplexEuclidean 1 :=
  hilbertPhysicalField lower bounded (originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field component)

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))
include allGrades smooth

theorem originalPhysicalComponentCurve_smooth (component : Fin 2) (grade : ℕ) :
    ContDiffOn ℝ ∞ (originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field component grade) (Icc lower 1) := by
  have regular := originalPairCurve_smooth_of_conjugated parameters lower length positive bounded lengthPositive field allGrades smooth grade
  unfold originalPhysicalComponentCurve
  split_ifs
  · exact regular.fst
  · exact regular.snd

omit smooth in
theorem originalPhysicalComponentCurve_grade (component : Fin 2) (grade : ℕ) (radius : ℝ)
    (_inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field component grade radius mode =
      ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field component 0 radius mode := by
  unfold originalPhysicalComponentCurve originalPairCurve
  split_ifs
  · exact sameCoupledPhysicalXSection_grade parameters lower length positive bounded lengthPositive field allGrades grade _ mode
  · exact sameCoupledPhysicalXiSection_grade parameters lower length positive bounded lengthPositive field allGrades grade _ mode

theorem originalPhysicalComponentField_smooth (component : Fin 2) :
    ContDiffOn ℝ ∞ (originalPhysicalComponentField parameters lower length positive bounded lengthPositive field component)
      (annularJointClosed lower) :=
  hilbertPhysicalField_smooth_closed lower positive bounded _
    (originalPhysicalComponentCurve_smooth parameters lower length positive bounded lengthPositive field allGrades smooth component)
    (originalPhysicalComponentCurve_grade parameters lower length positive bounded lengthPositive field allGrades component)

theorem originalPhysicalComponentField_coefficient (component : Fin 2) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun axial => angularCoefficient
      (fun polar => originalPhysicalComponentField parameters lower length positive bounded lengthPositive field component (radius,polar,axial)) mode.1) mode.2 =
      originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field component 0 radius mode :=
  hilbertPhysicalField_coefficient lower bounded _
    (originalPhysicalComponentCurve_smooth parameters lower length positive bounded lengthPositive field allGrades smooth component)
    (originalPhysicalComponentCurve_grade parameters lower length positive bounded lengthPositive field allGrades component) radius inside mode

end Grad.AnnularGeneralSourceRegularity
