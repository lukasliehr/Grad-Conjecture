import ANJ8CompletedWeakEquation

noncomputable section
set_option maxHeartbeats 1200000
open Set
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.CircularNormalLift Grad.NonlinearRange
local instance (priority := 2000) physicalTraceUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

def completedH1 (grade : ℕ) : unitDiskSobolev (grade + 2) →L[ℂ] diskGrade :=
  unitLower (show 1 ≤ grade + 2 by omega)

theorem completedH1_core (grade : ℕ) (core : ClosedJet 1) :
    completedH1 grade (unitDiskCoreInto (grade + 2) core) = diskCoreInto core :=
  unitLower_core (show 1 ≤ grade + 2 by omega) core

theorem completedH1_bulk (grade : ℕ) (field : unitDiskSobolev (grade + 2)) :
    diskBulk (completedH1 grade field) = unitDiskBulk (grade + 2) field := by
  apply isClosed_property (unitDiskCoreInto_denseRange (grade + 2))
    (isClosed_eq (diskBulk.continuous.comp (completedH1 grade).continuous) (unitDiskBulk (grade + 2)).continuous) _ field
  intro core
  exact (congrArg diskBulk (completedH1_core grade core)).trans
    ((Grad.CircularHighRegularity.diskBulk_core core).trans (unitDiskBulk_core (grade + 2) core).symm)

def completedEulerH1 : unitDiskSobolev 2 →L[ℂ] diskGrade := ordinaryEuler 1

theorem completedEulerH1_core (core : ClosedJet 1) :
    completedEulerH1 (unitDiskCoreInto 2 core) = diskCoreInto (eulerJet core) := ordinaryEuler_core 1 core

def completedRobinH1 : unitDiskSobolev 2 →L[ℂ] diskGrade := completedEulerH1 + (2 : ℂ) • completedH1 0

def completedRobinL2 : unitDiskSobolev 2 →L[ℂ] BoundaryL2 := diskBoundary.comp completedRobinH1

theorem completedRobinH1_trace (field : unitDiskSobolev 2) :
    diskTrace (completedRobinH1 field) = ordinaryRobinTrace 0 field := by
  exact (diskTrace.map_add (completedEulerH1 field) ((2 : ℂ) • completedH1 0 field)).trans
    (congrArg (fun value => diskTrace (completedEulerH1 field) + value) (diskTrace.map_smul (2 : ℂ) (completedH1 0 field)))

theorem diskBoundary_equal_of_trace (first second : diskGrade) (same : diskTrace first = diskTrace second) :
    diskBoundary first = diskBoundary second := by
  have traceZero := (diskTrace.map_sub first second).trans
    ((congrArg (fun value => value - diskTrace second) same).trans (sub_self _))
  have fourierZero : diskBoundaryFourier (first - second) = 0 :=
    (congrArg boundaryUnweight traceZero).trans (boundaryUnweight.map_zero)
  have normZero : ‖diskBoundary (first - second)‖ ^ 2 = 0 := (diskBoundary_fourier_norm_sq (first - second)).trans
    ((congrArg (fun value : BoundaryFourierL2 => (2 * Real.pi) * ‖value‖ ^ 2) fourierZero).trans (by simp))
  have boundaryZero := norm_eq_zero.mp (sq_eq_zero_iff.mp normZero)
  exact sub_eq_zero.mp ((diskBoundary.map_sub first second).symm.trans boundaryZero)

theorem completedRobinL2_equal_of_trace (first second : unitDiskSobolev 2)
    (same : ordinaryRobinTrace 0 first = ordinaryRobinTrace 0 second) :
    completedRobinL2 first = completedRobinL2 second :=
  diskBoundary_equal_of_trace _ _ ((completedRobinH1_trace first).trans (same.trans (completedRobinH1_trace second).symm))

theorem completedRobinL2_core (core : ClosedJet 1) :
    completedRobinL2 (unitDiskCoreInto 2 core) = coreBoundaryL2 (eulerJet core) + (2 : ℂ) • coreBoundaryL2 core := by
  have field := congrArg₂ (fun first second : diskGrade => first + (2 : ℂ) • second)
    (completedEulerH1_core core) (completedH1_core 0 core)
  have linear := (diskBoundary.map_add (diskCoreInto (eulerJet core)) ((2 : ℂ) • diskCoreInto core)).trans
    (congrArg (fun value => diskBoundary (diskCoreInto (eulerJet core)) + value)
      (diskBoundary.map_smul (2 : ℂ) (diskCoreInto core)))
  exact (congrArg diskBoundary field).trans (linear.trans
    (congrArg₂ (fun first second : BoundaryL2 => first + (2 : ℂ) • second)
      (diskBoundary_core (eulerJet core)) (diskBoundary_core core)))

theorem unitH1_bulk (field : unitDiskSobolev 1) : unitDiskBulk 1 field = diskBulk field := by
  apply isClosed_property (unitDiskCoreInto_denseRange 1)
    (isClosed_eq (unitDiskBulk 1).continuous diskBulk.continuous) _ field
  intro core
  exact (unitDiskBulk_core 1 core).trans (Grad.CircularHighRegularity.diskBulk_core core).symm

/-- Actual high L2 membership already determines high H1 membership. -/
theorem diskGrade_high_of_bulk (parameters : PhaseParameters) (field : diskGrade)
    (high : diskBulk field ∈ highDiskL2) : field ∈ highDiskGrade := by
  have projected : unitHigh 1 field ∈ highDiskGrade := by
    apply isClosed_property (unitDiskCoreInto_denseRange 1)
      (highDiskCore.range.isClosed_topologicalClosure.preimage (unitHigh 1).continuous) _ field
    intro core
    have coreMember : unitDiskCoreInto 1 (excludedAngularJet lowAngularModes core) ∈ highDiskGrade :=
      Submodule.le_topologicalClosure highDiskCore.range ⟨core, rfl⟩
    exact (congrArg (fun value : unitDiskSobolev 1 => value ∈ highDiskGrade) (unitHigh_core 1 core)).mpr coreMember
  have highActual : unitDiskBulk 1 field ∈ highDiskL2 :=
    (congrArg (fun value : DiskL2 1 => value ∈ highDiskL2) (unitH1_bulk field)).mpr high
  have same := unitHigh_fixed parameters 1 field highActual
  exact (congrArg (fun value : unitDiskSobolev 1 => value ∈ highDiskGrade) same).mp projected

end Grad.InhomogeneousHighRobin
