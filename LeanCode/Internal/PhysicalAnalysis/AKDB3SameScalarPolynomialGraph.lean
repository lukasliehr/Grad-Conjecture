import AKDB2SmoothPolynomialGraphAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.PhysicalFamily Grad.ActualSmoothPhysicalField

/-- Literal multiplication by the two coordinates of Jy followed by their
contraction with the planar field. This map is bounded on the original disk. -/
def startupTangentialPolynomialKernel : StartupL2 2 →L[ℂ] StartupL2 1 :=
  (startupSmoothDiskMultiplier 1 (angularRotationCoordinate 0) (angularRotationCoordinate 0).contDiff).comp
    (originalValueKernel (startupComponentEntry 0 0)) +
  (startupSmoothDiskMultiplier 1 (angularRotationCoordinate 1) (angularRotationCoordinate 1).contDiff).comp
    (originalValueKernel (startupComponentEntry 0 1))

theorem startupTangentialPolynomial_pairing (field : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 test (startupTangentialPolynomialKernel field) =
      ∑ direction : Fin 2, startupCoordinateTestPairing cell direction
        (multiplyTest (angularRotationCoordinate direction) (angularRotationCoordinate direction).contDiff test) field := by
  simp only [startupTangentialPolynomialKernel,add_apply,ContinuousLinearMap.comp_apply,map_add,
    startupSmoothDiskMultiplier_pairing,startupComponentEntry_pairing,ite_true,one_mul,Fin.sum_univ_two]

theorem startupTangentialPolynomial_preservesGraph : StartupPreservesGraph startupTangentialPolynomialKernel :=
  ((startupSmoothDiskMultiplier_preservesGraph 1 _ _).comp (originalValue_preservesGraph _)).add
    ((startupSmoothDiskMultiplier_preservesGraph 1 _ _).comp (originalValue_preservesGraph _))

/-- The SAME native psi is exactly a polynomial of the recovered gradient,
so its all-order regularity follows without a radius division at the axis. -/
theorem startupSame_scalarForce_polynomial_eq (psi : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation (originalScalarInverseKernel psi) vector right)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0) :
    psi = startupTangentialPolynomialKernel (startupRecoveredGradient vector right) := by
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  have unique : coordinate=0 := Subsingleton.elim _ _
  subst coordinate
  rw [startupTangentialPolynomial_pairing]
  exact startupSame_scalarForce_polynomial psi vector right equation mean cell test

/-- Every existing mixed spatial/cell graph of the actual recovered gradient
supplies the corresponding graph of the literal scalar psi. -/
theorem startupSame_scalarForce_graph (psi : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation (originalScalarInverseKernel psi) vector right)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0)
    (order weight : ℕ) (gradient : GraphGrade 2 order weight openUnitDisk)
    (same : base 2 order openUnitDisk (fun _ => weight) gradient = startupRecoveredGradient vector right) :
    ∃ scalar : GraphGrade 1 order weight openUnitDisk,
      base 1 order openUnitDisk (fun _ => weight) scalar = psi := by
  obtain ⟨scalar,actual⟩ := startupTangentialPolynomial_preservesGraph order weight gradient
  refine ⟨scalar,?_⟩
  rw [same,← startupSame_scalarForce_polynomial_eq psi vector right equation mean] at actual
  exact actual

end Grad.CartesianStartup
