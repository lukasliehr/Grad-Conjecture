import AAR8OriginalPhysicalFirstRow
import AAG15PhysicalFunctional

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem finiteEnergy_single (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    finiteAnnularEnergyCore lower length positive (Finsupp.single mode core) =
      lp.single 2 mode (annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core) := by
  classical
  apply lp.ext
  funext index
  rw [finiteEnergy_mode]
  simp only [Finsupp.single_apply, lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, Ne.symm same, if_false, map_zero]

theorem annularEnergy_single_inner (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1)
    (field : annularEnergySpace lower length positive) :
    inner ℂ (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) field =
      inner ℂ (weightedCurveComplex 1 lower core.val.2)
        (annularEnergyDerivative lower length positive field mode) +
      inner ℂ (weightedCurveComplex 1 lower
        (continuousCurveWeight 1 (annularPotentialWeight lower length positive mode.val.1 mode.val.2) core.val.1))
        (annularEnergyMass lower length positive field mode) +
      inner ℂ ((Real.sqrt 2 : ℂ) • core.val.1 1)
        (annularEnergyOuter lower length positive field mode) := by
  classical
  change inner ℂ (finiteAnnularEnergyCore lower length positive (Finsupp.single mode core)) field.val = _
  rw [finiteEnergy_single, lp.inner_single_left]
  change _ + (_ + _) = _ + _ + _
  exact (add_assoc _ _ _).symm

theorem complexLpTwoMap_single {Source Target : Type*}
    [NormedAddCommGroup Source] [NormedSpace ℂ Source]
    [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (mapping : HighAnnularMode → Source →L[ℂ] Target) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode field, ‖mapping mode field‖ ≤ bound * ‖field‖)
    (mode : HighAnnularMode) (field : Source) :
    complexLpTwoMap mapping bound nonnegative bounded (lp.single 2 mode field) =
      lp.single 2 mode (mapping mode field) := by
  classical
  apply lp.ext
  funext index
  change mapping index ((lp.single 2 mode field : lp (fun _ : HighAnnularMode => Source) 2) index) = _
  simp only [lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, if_false, map_zero]

theorem annularEnergyDerivative_single (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyDerivative lower length positive (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode (weightedCurveComplex 1 lower core.val.2) := by
  change annularAmbientDerivative lower (finiteAnnularEnergyCore lower length positive (Finsupp.single mode core)) = _
  rw [finiteEnergy_single]
  exact complexLpTwoMap_single _ _ _ _ mode _

theorem annularEnergyMass_single (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyMass lower length positive (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode (weightedCurveComplex 1 lower
        (continuousCurveWeight 1 (annularPotentialWeight lower length positive mode.val.1 mode.val.2) core.val.1)) := by
  change annularAmbientMass lower (finiteAnnularEnergyCore lower length positive (Finsupp.single mode core)) = _
  rw [finiteEnergy_single]
  exact complexLpTwoMap_single _ _ _ _ mode _

theorem annularEnergyValue_single (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1) :
    annularEnergyValue lower length positive (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      lp.single 2 mode (weightedCurveComplex 1 lower core.val.1) := by
  classical
  apply lp.ext
  funext index
  rw [annularEnergyValue_core_mode]
  simp only [Finsupp.single_apply, lp.single_apply, Pi.single_apply]
  by_cases same : index = mode
  · subst index
    simp only [ite_true]
  · simp only [same, Ne.symm same, if_false]
    exact map_zero (weightedCurveComplex 1 lower)

end Grad.AnnularReconstruction
