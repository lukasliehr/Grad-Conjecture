import AJE52CompleteSmoothSourceDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy
attribute [local instance] originalAmbientRealNormed

abbrev RadialFourierSourceCore := (ℤ × ℤ) →₀ SmoothRadialCore 1

def meanFreeRadialCore (core : RadialFourierSourceCore) : RadialFourierSourceCore :=
  core.filter (fun mode => mode.1 ≠ 0)

theorem meanFreeRadialCore_apply (core : RadialFourierSourceCore) (mode : ℤ × ℤ) :
    meanFreeRadialCore core mode = if mode.1 = 0 then 0 else core mode := by
  unfold meanFreeRadialCore
  rw [Finsupp.filter_apply]
  split_ifs <;> simp_all

theorem meanFreeGraphCore_exact (parameters : PhaseParameters) (lower : ℝ) (core : RadialFourierSourceCore) :
    sourceMeanFreeLp (finiteSourceCore parameters 1 lower 0 0 core) =
      finiteSourceCore parameters 1 lower 0 0 (meanFreeRadialCore core) := by
  apply lp.ext
  funext mode
  rw [sourceMeanFreeLp_apply,finiteSourceCore_apply,finiteSourceCore_apply,meanFreeRadialCore_apply]
  split_ifs <;> simp only [map_zero]

theorem meanFreeRadialCore_exact (lower : ℝ) (core : RadialFourierSourceCore) :
    sourceMeanFreeLp (finiteSmoothRadialSource 1 lower core) =
      finiteSmoothRadialSource 1 lower (meanFreeRadialCore core) := by
  apply lp.ext
  funext mode
  rw [sourceMeanFreeLp_apply,finiteSmoothRadialSource_mode,finiteSmoothRadialSource_mode,meanFreeRadialCore_apply]
  split_ifs <;> simp only [map_zero]

abbrev OriginalSmoothSourceCore (parameters : PhaseParameters) :=
  (((RadialFourierSourceCore × RadialFourierSourceCore) × (RadialFourierSourceCore × RadialFourierSourceCore)) ×
    ((Finset (ℤ × ℤ) × HighBoundaryPrimitive parameters 0 0) ×
      ((HighAnnularMode →₀ ComplexEuclidean 1) × (LowAnnularIndex →₀ ComplexEuclidean 1))))

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : OriginalSmoothSourceCore parameters)

def originalSmoothStrongData : OriginalStrongCarrier parameters lower 0 0 :=
  (originalSmoothStrongDenseMap parameters lower positive bounded).mapping core

theorem originalSmoothStrongData_graphs :
    (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.1 =
      finiteSourceCore parameters 1 lower 0 0 core.1.1.1 ∧
    (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.2 =
      finiteSourceCore parameters 1 lower 0 0 (meanFreeRadialCore core.1.1.2) :=
  ⟨rfl,meanFreeGraphCore_exact parameters lower core.1.1.2⟩

theorem originalSmoothStrongData_forcing :
    (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.1 =
      finiteSmoothRadialSource 1 lower (meanFreeRadialCore core.1.2.1) ∧
    (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.2 =
      finiteSmoothRadialSource 1 lower (meanFreeRadialCore core.1.2.2) :=
  ⟨meanFreeRadialCore_exact lower core.1.2.1,meanFreeRadialCore_exact lower core.1.2.2⟩

/-- The copied F0 and F2 are actual radial smooth graph cores, with the
same value, radial derivative and completed endpoints. -/
theorem originalSmoothStrongData_graph_modes (mode : ℤ × ℤ) :
    (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.1 mode =
      weightedRadialCoreInto 1 lower (core.1.1.1 mode) ∧
    (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.2 mode =
      weightedRadialCoreInto 1 lower (meanFreeRadialCore core.1.1.2 mode) := by
  rw [(originalSmoothStrongData_graphs parameters lower positive bounded core).1,
    (originalSmoothStrongData_graphs parameters lower positive bounded core).2,finiteSourceCore_apply,finiteSourceCore_apply]
  exact ⟨rfl,rfl⟩

theorem originalSmoothStrongData_forcing_radial (mode : ℤ × ℤ) :
    (ContDiff ℝ ∞ (meanFreeRadialCore core.1.2.1 mode).val.val.1 ∧
      ∀ᵐ radius ∂volume.restrict (Icc lower 1),
        (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.1 mode radius =
          (meanFreeRadialCore core.1.2.1 mode).val.val.1 radius) ∧
    (ContDiff ℝ ∞ (meanFreeRadialCore core.1.2.2 mode).val.val.1 ∧
      ∀ᵐ radius ∂volume.restrict (Icc lower 1),
        (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.2 mode radius =
          (meanFreeRadialCore core.1.2.2 mode).val.val.1 radius) := by
  rw [(originalSmoothStrongData_forcing parameters lower positive bounded core).1,
    (originalSmoothStrongData_forcing parameters lower positive bounded core).2]
  exact ⟨finiteSmoothRadialSource_radial 1 lower (meanFreeRadialCore core.1.2.1) mode,
    finiteSmoothRadialSource_radial 1 lower (meanFreeRadialCore core.1.2.2) mode⟩

variable (length : ℝ) (lengthPositive : 0 < length)

theorem strongSmoothDenseMap_same_graphs :
    ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core).val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 =
      finiteSourceCore parameters 1 lower 0 0 core.1.1.1 ∧
    ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core).val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 =
      finiteSourceCore parameters 1 lower 0 0 (meanFreeRadialCore core.1.1.2) := by
  have same := strongSmoothDenseMap_actual parameters lower length positive bounded lengthPositive core
  have graphs := originalSmoothStrongData_graphs parameters lower positive bounded core
  exact ⟨(congrArg (fun data : StrongDataCarrier parameters lower positive bounded 0 0 =>
    data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1) same).trans graphs.1,
    (congrArg (fun data : StrongDataCarrier parameters lower positive bounded 0 0 =>
    data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2) same).trans graphs.2⟩

end Grad.AnnularStrongOrbit
