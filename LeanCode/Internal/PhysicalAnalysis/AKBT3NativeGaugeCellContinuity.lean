import AKBT2ActualNativeWeightedRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.BoundaryTrace

/-- The actual full coefficient product preserves punctured joint continuity;
no continuity of a merely measurable L2 representative is asserted. -/
theorem startupRawMatrix_punctured_continuous {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output)
    (raw : ℝ × Spatial → PhysicalValue input)
    (continuousRaw : ContinuousOn raw {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}}) :
    ContinuousOn (startupRawMatrix family raw) {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let point : {pair : ℝ × Spatial // pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} → ClosedDisk :=
    fun pair => ⟨pair.val.2,openDiskMembershipClosed pair.val.2 pair.property.1⟩
  have pointContinuous : Continuous point := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have coefficientContinuous := (startupPhysicalCoefficient_joint admissible (family 0)).comp
    ((continuous_fst.comp continuous_subtype_val).prodMk pointContinuous)
  have product := coefficientContinuous.clm_apply (continuousOn_iff_continuous_domRestrict.mp continuousRaw)
  change Continuous (fun pair : {pair : ℝ × Spatial // pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} => startupRawMatrix family raw pair.val)
  have same : (fun pair : {pair : ℝ × Spatial // pair.2 ∈ openUnitDisk \ {(0 : Spatial)}} => startupRawMatrix family raw pair.val) =
      (fun pair => coefficientPhysicalValue (family 0) pair.val.1 (point pair) (raw pair.val)) := by
    funext pair
    exact startupRawMatrix_value family raw pair.val.1 (point pair)
  rw [same]
  exact product

/-- Every Fourier cell of a punctured continuous full physical family is
continuous on the punctured disk, by the original compact angular integral. -/
theorem startupRawCell_punctured_continuous {dimension : ℕ}
    (raw : ℝ × Spatial → PhysicalValue dimension)
    (continuousRaw : ContinuousOn raw {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}})
    (cell : ℤ) :
    ContinuousOn (fun point => angularCoefficient (fun angle => raw (angle,point)) cell)
      (openUnitDisk \ {(0 : Spatial)}) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have : LocallyCompactSpace ↥(openUnitDisk \ {(0 : Spatial)}) :=
    (openUnitDisk_isOpen.sdiff isClosed_singleton).locallyCompactSpace
  have joint : Continuous (fun pair : {point : Spatial // point ∈ openUnitDisk \ {(0 : Spatial)}} × ℝ => raw (pair.2,pair.1.val)) :=
    continuousRaw.comp_continuous (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
      (fun pair => pair.1.property)
  simp_rw [angularCoefficient_compact_general]
  exact continuous_const.smul (continuous_parametric_integral_of_continuous
    (((cellExponential_smooth (-cell)).continuous.comp continuous_snd).smul joint) isCompact_Icc)

end Grad.CartesianStartup
