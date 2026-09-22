import AJZ1GenuineRadialSourceRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph
open Grad.AnnularVariational Grad.AnnularStrongOrbit

/-- All original Fourier modes, with the same phase and split/inserted
weights, retain both genuine radial graph coordinates. -/
def sourceGraphRestriction (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (angular cell grade : ℕ) :
    AnnularTotalSourceH1 parameters dimension lower angular cell grade →L[ℝ]
      AnnularTotalSourceH1 parameters dimension upper angular cell grade :=
  lpTwoMap (fun _ => sourceRadialRestriction dimension lower upper included) 1 zero_le_one
    (fun _ field => by simpa only [one_mul] using sourceRadialRestriction_bound dimension lower upper included field)

theorem sourceGraphRestriction_apply (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (mode : ℤ × ℤ) :
    sourceGraphRestriction parameters dimension lower upper included angular cell grade field mode =
      sourceRadialRestriction dimension lower upper included (field mode) := rfl

theorem sourceGraphRestriction_coordinate (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) (slot : Fin 2) :
    annularSourceCoordinate parameters dimension upper angular cell slot
        (sourceGraphRestriction parameters dimension lower upper included angular cell grade field) =
      collarBulkRestriction (ℤ × ℤ) dimension lower upper included
        (annularSourceCoordinate parameters dimension lower angular cell slot field) := by
  apply lp.ext
  funext mode
  exact sourceRadialRestriction_coordinate dimension lower upper included (field mode) slot

theorem sourceGraphRestriction_bound (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    ‖sourceGraphRestriction parameters dimension lower upper included angular cell grade field‖ ≤ ‖field‖ := by
  unfold sourceGraphRestriction
  simpa only [one_mul] using lpTwoMap_bound
    (fun _ : ℤ × ℤ => sourceRadialRestriction dimension lower upper included) 1 zero_le_one
    (fun _ value => by simpa only [one_mul] using sourceRadialRestriction_bound dimension lower upper included value) field

theorem sourceGraphRestriction_core (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper) (angular cell grade : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    sourceGraphRestriction parameters dimension lower upper included angular cell grade
        (physicalTotalSourceCore parameters dimension lower angular cell grade core) =
      physicalTotalSourceCore parameters dimension upper angular cell grade core := by
  apply lp.ext
  funext mode
  rw [sourceGraphRestriction_apply, physicalTotalSourceCore_apply,
    sourceRadialRestriction_core, physicalTotalSourceCore_apply]

theorem sourceGraphRestriction_id (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    sourceGraphRestriction parameters dimension lower lower le_rfl angular cell grade field = field := by
  apply lp.ext
  funext mode
  exact sourceRadialRestriction_id dimension lower (field mode)

theorem sourceGraphRestriction_comp (parameters : PhaseParameters) (dimension : ℕ)
    (lower middle upper : ℝ) (first : lower ≤ middle) (second : middle ≤ upper) (angular cell grade : ℕ)
    (field : AnnularTotalSourceH1 parameters dimension lower angular cell grade) :
    sourceGraphRestriction parameters dimension middle upper second angular cell grade
        (sourceGraphRestriction parameters dimension lower middle first angular cell grade field) =
      sourceGraphRestriction parameters dimension lower upper (first.trans second) angular cell grade field := by
  apply lp.ext
  funext mode
  exact sourceRadialRestriction_comp dimension lower middle upper first second (field mode)

theorem sourceGraphRestriction_splitInclusion (parameters : PhaseParameters) (dimension : ℕ)
    (lower upper : ℝ) (included : lower ≤ upper)
    (lowAngular lowCell highAngular highCell grade : ℕ)
    (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularTotalSourceH1 parameters dimension lower highAngular highCell grade) :
    sourceGraphRestriction parameters dimension lower upper included lowAngular lowCell grade
        (annularSourceInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) =
      annularSourceInclusion parameters dimension upper lowAngular lowCell highAngular highCell angularLe cellLe
        (sourceGraphRestriction parameters dimension lower upper included highAngular highCell grade field) := by
  apply lp.ext
  funext mode
  rw [sourceGraphRestriction_apply, annularSourceInclusion_apply,
    annularSourceInclusion_apply, sourceGraphRestriction_apply, map_smul]

end Grad.AnnularRestriction
