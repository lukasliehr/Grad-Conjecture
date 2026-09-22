import ANJ1CompletedScalarOperator

noncomputable section
set_option maxHeartbeats 1000000
open Set
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskMultiplier Grad.OrdinaryDiskFaithfulness Grad.AngularSobolevTruncation
local instance (priority := 2000) highScalarUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

def unitHigh (grade : ℕ) : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade :=
  ContinuousLinearMap.id ℂ _ - ordinarySelected grade lowAngularModes

theorem unitHigh_core (grade : ℕ) (core : ClosedJet 1) :
    unitHigh grade (unitDiskCoreInto grade core) = unitDiskCoreInto grade (excludedAngularJet lowAngularModes core) :=
  (congrArg (fun selected : unitDiskSobolev grade => unitDiskCoreInto grade core - selected)
    (ordinarySelected_core grade lowAngularModes core)).trans
    ((unitDiskCoreInto grade).map_sub core (selectedAngularJet lowAngularModes core)).symm

private theorem highProjection_difference (field : DiskL2 1) :
    field - diskSelectedModes lowAngularModes field = highL2Projection field := by
  rw [highL2Projection_apply, diskSelectedModes_apply]

theorem unitHigh_bulk (grade : ℕ) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (unitHigh grade field) = highL2Projection (unitDiskBulk grade field) :=
  ((unitDiskBulk grade).map_sub field (ordinarySelected grade lowAngularModes field)).trans
    ((congrArg (fun selected : DiskL2 1 => unitDiskBulk grade field - selected)
      (ordinarySelected_bulk grade lowAngularModes field)).trans (highProjection_difference _))

theorem unitHigh_fixed (parameters : PhaseParameters) (grade : ℕ) (field : unitDiskSobolev grade)
    (high : unitDiskBulk grade field ∈ highDiskL2) : unitHigh grade field = field := by
  apply ordinaryBulk_injective parameters grade
  exact (unitHigh_bulk grade field).trans (highL2Projection_fixed ⟨unitDiskBulk grade field, high⟩)

theorem unitHigh_high (grade : ℕ) (field : unitDiskSobolev grade) : unitDiskBulk grade (unitHigh grade field) ∈ highDiskL2 :=
  (unitHigh_bulk grade field).symm ▸ highL2Projection_mem (unitDiskBulk grade field)

/-- Rotational invariance of the actual Cartesian Laplacian survives ordinary completion. -/
theorem unitCartesianLaplacian_mode (grade : ℕ) (mode : ℤ) (field : unitDiskSobolev (grade + 2)) :
    unitCartesianLaplacian grade (ordinaryMode (grade + 2) mode field) =
      ordinaryMode grade mode (unitCartesianLaplacian grade field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange (grade + 2))
    (isClosed_eq ((unitCartesianLaplacian grade).continuous.comp (ordinaryMode (grade + 2) mode).continuous)
      ((ordinaryMode grade mode).continuous.comp (unitCartesianLaplacian grade).continuous)) _ field
  intro core
  exact (congrArg (unitCartesianLaplacian grade) (ordinaryMode_core (grade + 2) mode core)).trans
    ((unitCartesianLaplacian_core grade (angularClosedJet mode core)).trans
      ((congrArg (unitDiskCoreInto grade) (laplacianJet_angular mode core)).trans
        ((ordinaryMode_core grade mode _).symm.trans
          (congrArg (ordinaryMode grade mode) (unitCartesianLaplacian_core grade core)).symm)))

theorem ordinaryMode_zero_of_high (parameters : PhaseParameters) (grade : ℕ)
    (field : unitDiskSobolev grade) (high : unitDiskBulk grade field ∈ highDiskL2)
    (mode : ℤ) (low : mode ∈ lowAngularModes) : ordinaryMode grade mode field = 0 := by
  apply ordinaryBulk_injective parameters grade
  exact (ordinaryMode_bulk grade mode field).trans ((high mode low).trans (map_zero (unitDiskBulk grade)).symm)

theorem unitCartesianLaplacian_high (parameters : PhaseParameters) (grade : ℕ)
    (field : unitDiskSobolev (grade + 2)) (high : unitDiskBulk (grade + 2) field ∈ highDiskL2) :
    unitDiskBulk grade (unitCartesianLaplacian grade field) ∈ highDiskL2 := by
  intro mode low
  have zeroMode := (unitCartesianLaplacian_mode grade mode field).symm.trans
    ((congrArg (unitCartesianLaplacian grade) (ordinaryMode_zero_of_high parameters (grade + 2) field high mode low)).trans
      (map_zero (unitCartesianLaplacian grade)))
  exact (ordinaryMode_bulk grade mode _).symm.trans
    ((congrArg (unitDiskBulk grade) zeroMode).trans (map_zero (unitDiskBulk grade)))

theorem diskB_high (field : DiskL2 1) : diskB field ∈ highDiskL2 := by
  intro mode low
  rw [diskB_coefficient]
  simp only [highMultiplier, low, if_true, Complex.ofReal_zero, zero_smul]

theorem unitScalarOperator_high (parameters : PhaseParameters) (grade : ℕ) (parameter : ℝ)
    (field : unitDiskSobolev (grade + 2)) (high : unitDiskBulk (grade + 2) field ∈ highDiskL2) :
    unitDiskBulk grade (unitScalarOperator grade parameter field) ∈ highDiskL2 := by
  exact (unitScalarOperator_bulk grade parameter field).symm ▸
    highDiskL2.sub_mem (highDiskL2.smul_mem _ (diskB_high (unitDiskBulk (grade + 2) field)))
      (unitCartesianLaplacian_high parameters grade field high)

end Grad.InhomogeneousHighRobin
