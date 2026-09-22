import AUB11ActualSmoothRobinConsumer

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskMultiplier Grad.OrdinaryDiskFaithfulness
open Grad.NonlinearDivision (laplacianJet)
open Grad.NonlinearQuotientBounds
local instance (priority := 2000) scalarUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

/-- Actual Cartesian Laplacian on the original completed ordinary grades. -/
def unitCartesianLaplacian (grade : ℕ) : unitDiskSobolev (grade + 2) →L[ℂ] unitDiskSobolev grade :=
  (unitPartial grade 0).comp (unitPartial (grade + 1) 0) +
    (unitPartial grade 1).comp (unitPartial (grade + 1) 1)

theorem unitCartesianLaplacian_core (grade : ℕ) (core : ClosedJet 1) :
    unitCartesianLaplacian grade (unitDiskCoreInto (grade + 2) core) = unitDiskCoreInto grade (laplacianJet core) := by
  have first := (congrArg (unitPartial grade 0) (unitPartial_core (grade + 1) 0 core)).trans
    (unitPartial_core grade 0 (partialJet 0 core))
  have second := (congrArg (unitPartial grade 1) (unitPartial_core (grade + 1) 1 core)).trans
    (unitPartial_core grade 1 (partialJet 1 core))
  exact (congrArg₂ (fun first second : unitDiskSobolev grade => first + second) first second).trans
    ((unitDiskCoreInto grade).map_add (partialJet 0 (partialJet 0 core)) (partialJet 1 (partialJet 1 core))).symm

theorem unitCartesianLaplacian_core_bulk (grade : ℕ) (core : ClosedJet 1) :
    unitDiskBulk grade (unitCartesianLaplacian grade (unitDiskCoreInto (grade + 2) core)) =
      closedL2Core (laplacianJet core) :=
  (congrArg (unitDiskBulk grade) (unitCartesianLaplacian_core grade core)).trans (unitDiskBulk_core grade _)

/-- The literal scalar equation operator -Delta+k²B, with accepted B's
zero extension on the five excluded angular modes. -/
def unitScalarOperator (grade : ℕ) (parameter : ℝ) : unitDiskSobolev (grade + 2) →L[ℂ] unitDiskSobolev grade :=
  ((parameter ^ 2 : ℝ) : ℂ) • ((unitB grade).comp (unitLower (Nat.le_add_right grade 2))) -
    unitCartesianLaplacian grade

theorem unitScalarOperator_apply (grade : ℕ) (parameter : ℝ) (field : unitDiskSobolev (grade + 2)) :
    unitScalarOperator grade parameter field =
      ((parameter ^ 2 : ℝ) : ℂ) • unitB grade (unitLower (Nat.le_add_right grade 2) field) -
        unitCartesianLaplacian grade field := rfl

theorem unitScalarOperator_bulk (grade : ℕ) (parameter : ℝ) (field : unitDiskSobolev (grade + 2)) :
    unitDiskBulk grade (unitScalarOperator grade parameter field) =
      ((parameter ^ 2 : ℝ) : ℂ) • diskB (unitDiskBulk (grade + 2) field) -
        unitDiskBulk grade (unitCartesianLaplacian grade field) := by
  have multiplier : unitDiskBulk grade (unitB grade (unitLower (Nat.le_add_right grade 2) field)) =
      diskB (unitDiskBulk (grade + 2) field) :=
    (unitB_bulk grade _).trans (congrArg diskB (unitLower_bulk (Nat.le_add_right grade 2) field))
  exact ((unitDiskBulk grade).map_sub _ _).trans
    (congrArg (fun first : DiskL2 1 => first - unitDiskBulk grade (unitCartesianLaplacian grade field))
      (((unitDiskBulk grade).map_smul _ _).trans
        (congrArg (fun value : DiskL2 1 => ((parameter ^ 2 : ℝ) : ℂ) • value) multiplier)))

private theorem parameterOperator_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (first second : E →L[ℂ] F)
    (parameter ceiling : ℝ) (bounded : |parameter| ≤ ceiling) (field : E) :
    ‖((parameter ^ 2 : ℝ) : ℂ) • first field - second field‖ ≤
      (ceiling ^ 2 * ‖first‖ + ‖second‖) * ‖field‖ := by
  have parameterSquare : parameter ^ 2 ≤ ceiling ^ 2 := by nlinarith [abs_nonneg parameter, sq_abs parameter]
  have triangle := norm_sub_le (((parameter ^ 2 : ℝ) : ℂ) • first field) (second field)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg parameter)] at triangle
  have product := mul_le_mul parameterSquare (first.le_opNorm field) (norm_nonneg _) (sq_nonneg ceiling)
  exact triangle.trans ((add_le_add product (second.le_opNorm field)).trans_eq (by ring))

def scalarOperatorConstant (grade : ℕ) (ceiling : ℝ) : ℝ :=
  ceiling ^ 2 * ‖(unitB grade).comp (unitLower (Nat.le_add_right grade 2))‖ + ‖unitCartesianLaplacian grade‖

theorem scalarOperatorConstant_nonnegative (grade : ℕ) (ceiling : ℝ) : 0 ≤ scalarOperatorConstant grade ceiling :=
  add_nonneg (mul_nonneg (sq_nonneg ceiling)
    (norm_nonneg ((unitB grade).comp (unitLower (Nat.le_add_right grade 2)))))
    (norm_nonneg (unitCartesianLaplacian grade))

theorem unitScalarOperator_bound (grade : ℕ) (ceiling : ℝ) (parameter : ℝ) (bounded : |parameter| ≤ ceiling)
    (field : unitDiskSobolev (grade + 2)) :
    ‖unitScalarOperator grade parameter field‖ ≤ scalarOperatorConstant grade ceiling * ‖field‖ :=
  @parameterOperator_bound (unitDiskSobolev (grade + 2)) (unitDiskSobolev grade)
    inferInstance inferInstance (unitNormedSpace (grade + 2)) (unitNormedSpace grade)
    ((unitB grade).comp (unitLower (Nat.le_add_right grade 2)))
    (unitCartesianLaplacian grade) parameter ceiling bounded field

end Grad.InhomogeneousHighRobin
