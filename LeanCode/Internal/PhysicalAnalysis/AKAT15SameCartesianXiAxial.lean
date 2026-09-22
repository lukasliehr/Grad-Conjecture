import AKAT14ActualOriginalProjectedForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.ActualCartesianDescent Grad.AnnularClosedJointRegularity
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

include allGrades smooth

/-- The genuine axial Cartesian derivative of SAME Xi equals its original
normalized seven-field coordinate, with no differentiability assumption. -/
theorem fullSeven_physicalXi_cartesianAxial
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    fderiv ℝ (cartesianPhysicalField
      (originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1))
      (polarPlane (radius,polar),axial) (0,1) =
      (seven.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,polar,axial) := by
  let xi := originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1
  have regular : ContDiffOn ℝ ∞ xi (Ioo lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
    (originalPhysicalComponentField_smooth parameters lower length positive bounded lengthPositive field allGrades smooth 1).mono
      (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩)
  have periodic : ∀ r z,Function.Periodic (fun theta => xi (r,theta,z)) (2*Real.pi) :=
    fun r z => hilbertPhysicalField_angular_periodic lower bounded _ r z
  exact (cartesianPhysicalField_axial_hasDerivAt xi lower 1 regular periodic radius
    (positive.trans inside.1) inside polar axial).unique
    (fullSeven_physicalXi_axial parameters lower length positive bounded lengthPositive data field allGrades smooth seven
      radius ⟨inside.1.le,inside.2.le⟩ polar axial)

end Grad.ActualCartesianEquations
