import AKAT5SameCartesianCovariantRotation

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

/-- The actual Cartesian gradient of SAME Xi, after substituting its genuine
radial slope and the original seven-field angular coordinate. -/
theorem fullSeven_physicalXi_cartesianGradient
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ)
    (slope : ComplexEuclidean 1)
    (radialLaw : HasDerivWithinAt
      (fun query => originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1 (query,polar,axial))
      slope (Icc lower 1) radius) :
    planarGradientValue (fderiv ℝ (cartesianPhysicalField
      (originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1)) (polarPlane (radius,polar),axial)) =
      cartesianCovariantValue polar (WithLp.toLp 2 ![slope 0,
        (seven.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial) 0,0]) := by
  let xi := originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1
  have regular : ContDiffOn ℝ ∞ xi (Ioo lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
    (originalPhysicalComponentField_smooth parameters lower length positive bounded lengthPositive field allGrades smooth 1).mono
      (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩)
  have periodic : ∀ r z,Function.Periodic (fun theta => xi (r,theta,z)) (2*Real.pi) :=
    fun r z => hilbertPhysicalField_angular_periodic lower bounded _ r z
  have actual := cartesianPhysicalField_gradient_from_derivatives xi lower 1 regular periodic radius
    (positive.trans inside.1) inside polar axial slope _
    (radialLaw.hasDerivAt (Icc_mem_nhds inside.1 inside.2))
    (fullSeven_physicalXi_angular parameters lower length positive bounded lengthPositive data field allGrades smooth seven
      radius ⟨inside.1.le,inside.2.le⟩ polar axial)
  have nonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (positive.trans inside.1).ne'
  simpa only [PiLp.smul_apply,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ nonzero,one_mul] using actual

end Grad.ActualCartesianEquations
