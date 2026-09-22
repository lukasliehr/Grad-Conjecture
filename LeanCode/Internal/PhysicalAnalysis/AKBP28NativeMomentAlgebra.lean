import AKBP26SameRadialRemainderCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem StartupMoments.related {dimension : ℕ} (family : StartupMoments dimension) (grade : Fin 3) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ grade.val) (family.moment grade) family.field :=
  family.same.mono (fun _ same => same grade)

theorem StartupMoments.first_related {dimension : ℕ} (family : StartupMoments dimension) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) (family.moment 1) family.field := by
  simpa only [Fin.val_one,pow_one] using family.related 1

theorem StartupMoments.second_related {dimension : ℕ} (family : StartupMoments dimension) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2) (family.moment 2) family.field :=
  family.related 2

theorem StartupMoments.second_first_related {dimension : ℕ} (family : StartupMoments dimension) :
    StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) (family.moment 2) (family.moment 1) := by
  filter_upwards [family.same] with point same
  intro cell
  rw [same 2 cell,same 1 cell]
  simp only [Fin.val_one,pow_one,smul_smul]
  exact congrArg (fun value : ℝ => value • family.field point cell) (pow_two (Grad.CellWeights.cellWeight cell))

theorem StartupMoments.phase_moment {dimension : ℕ} {symbol : ℤ → Spatial → ℝ}
    (weighted original : StartupMoments dimension) (same : StartupRadialRelated symbol weighted.field original.field)
    (grade : Fin 3) : StartupRadialRelated symbol (weighted.moment grade) (original.moment grade) := by
  filter_upwards [same,weighted.same,original.same] with point same weightedValue originalValue
  intro cell
  rw [weightedValue grade cell,originalValue grade cell,same cell]
  exact smul_comm _ _ _

def StartupMoments.add {dimension : ℕ} (first second : StartupMoments dimension) : StartupMoments dimension where
  field := first.field + second.field
  moment grade := first.moment grade + second.moment grade
  zero := by rw [first.zero,second.zero]
  same := by
    apply ae_all_iff.mpr
    intro grade
    exact (first.related grade).add (second.related grade)

def StartupMoments.sub {dimension : ℕ} (first second : StartupMoments dimension) : StartupMoments dimension where
  field := first.field - second.field
  moment grade := first.moment grade - second.moment grade
  zero := by rw [first.zero,second.zero]
  same := by
    apply ae_all_iff.mpr
    intro grade
    exact (first.related grade).sub (second.related grade)

def StartupMoments.smul {dimension : ℕ} (family : StartupMoments dimension) (scalar : ℂ) : StartupMoments dimension where
  field := scalar • family.field
  moment grade := scalar • family.moment grade
  zero := by rw [family.zero]
  same := by
    apply ae_all_iff.mpr
    intro grade
    exact (family.related grade).smul scalar

def StartupMoments.value {input output : ℕ} (family : StartupMoments input) (mapping : OperatorValue input output) : StartupMoments output :=
  family.map (originalValueKernel mapping) (originalValueKernel_cellwise mapping)

def StartupMoments.average (family : StartupMoments 2) : StartupMoments 2 :=
  family.map originalAverageKernel originalAverageKernel_cellwise

def StartupMoments.primitive (family : StartupMoments 2) : StartupMoments 2 where
  field := startupCovariantPrimitiveKernel family.field
  moment grade := startupCovariantPrimitiveKernel (family.moment grade)
  zero := congrArg startupCovariantPrimitiveKernel family.zero
  same := by
    apply ae_all_iff.mpr
    intro grade
    exact (family.related grade).radialPrimitive (fun _ _ _ _ => rfl)

def StartupMoments.qrad (family : StartupMoments 2) : StartupMoments 2 :=
  family.map startupGenuineQradKernel
    ((StartupCellwise.id 2).add ((originalValueKernel_cellwise quarterValueMap).comp
      (originalTangentialKernel_cellwise.comp (originalValueKernel_cellwise quarterValueMap))))

def StartupMoments.recoveredGradient (vector right : StartupMoments 2) : StartupMoments 2 :=
  (vector.sub vector.average).add ((right.add ((vector.value quarterValueMap).smul 2)).primitive)

theorem StartupMoments.recoveredGradient_field (vector right : StartupMoments 2) :
    (vector.recoveredGradient right).field = startupRecoveredGradient vector.field right.field := rfl

theorem StartupMoments.recoveredGradient_moment (vector right : StartupMoments 2) (grade : Fin 3) :
    (vector.recoveredGradient right).moment grade = startupRecoveredGradient (vector.moment grade) (right.moment grade) := rfl

end Grad.CartesianStartup
