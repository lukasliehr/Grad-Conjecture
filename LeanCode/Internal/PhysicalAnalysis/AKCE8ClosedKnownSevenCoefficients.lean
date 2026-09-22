import AKCE7SamePhysicalKnownCoefficients
import AKCE6SameKnownGraphOuterTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators Grad.AnnularCurrentSource Grad.AnnularLowEnergy

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

def strongKnownGraphPair : HighRadialSourceGraphs parameters lower 0 :=
  (highKnownF0GraphProjection parameters lower 0 0 data.val.ofLp.1,
    highKnownF2GraphProjection parameters lower 0 0 data.val.ofLp.1)

 theorem fullSeven_known_closed (radius : ℝ) (inside : radius∈Icc lower 1) (mode : ℤ×ℤ) (slot : Fin 3) :
    matrixUnit (0 : Fin 1) (⟨slot.val+4,by omega⟩ : Fin 7) (seven.physicalCurve 0 radius mode)=
      ![knownGraphPhysicalSection parameters lower positive bounded 1
          (strongKnownGraphPair parameters lower positive bounded data).1 mode radius,
        (Complex.I*(mode.1:ℂ)) • knownGraphPhysicalSection parameters lower positive bounded 1
          (strongKnownGraphPair parameters lower positive bounded data).1 mode radius,
        knownGraphPhysicalSection parameters lower positive bounded 0
          (strongKnownGraphPair parameters lower positive bounded data).2 mode radius] slot := by
  let graphs := strongKnownGraphPair parameters lower positive bounded data
  let rhs := fun location => ![knownGraphPhysicalSection parameters lower positive bounded 1 graphs.1 mode location,
    (Complex.I*(mode.1:ℂ)) • knownGraphPhysicalSection parameters lower positive bounded 1 graphs.1 mode location,
    knownGraphPhysicalSection parameters lower positive bounded 0 graphs.2 mode location] slot
  have rhsContinuous : Continuous rhs := by
    fin_cases slot
    · exact knownGraphPhysicalSection_continuous parameters lower positive bounded 1 graphs.1 mode
    · exact (continuous_const : Continuous (fun _ : ℝ => Complex.I*(mode.1:ℂ))).smul
        (knownGraphPhysicalSection_continuous parameters lower positive bounded 1 graphs.1 mode)
    · exact knownGraphPhysicalSection_continuous parameters lower positive bounded 0 graphs.2 mode
  apply collarCurve_eq_of_ae lower bounded _ rhs
    ((matrixUnit (0 : Fin 1) (⟨slot.val+4,by omega⟩ : Fin 7)).continuous.comp_continuousOn
      ((lp.evalCLM ℂ (fun _ : ℤ×ℤ => ComplexEuclidean 7) 2 mode).continuous.comp_continuousOn
        (seven.physicalCurve_smooth bounded 0).continuousOn)) rhsContinuous.continuousOn _ inside
  filter_upwards [seven.physicalCurve_actual bounded 0,
    fullStrongSevenInput_known_physical parameters lower length positive bounded lengthPositive data field,
    StrongDataCarrier.compatibility parameters lower positive bounded.le 0 0 data,
    knownF0Bulk_section_ae parameters lower positive bounded graphs.1 mode,
    knownRF0Bulk_section_ae parameters lower positive bounded graphs.1 mode,
    knownF2Bulk_section_ae parameters lower positive bounded graphs.2 mode,
    ae_restrict_mem measurableSet_Icc] with location represented actual compatibility f0 rf0 f2 member
  change matrixUnit (0 : Fin 1) (⟨slot.val+4,by omega⟩ : Fin 7) (seven.physicalCurve 0 location mode)=rhs location
  rw [represented mode]
  simp only [pow_zero,one_smul]
  rw [actual mode slot]
  have source0 := (compatibility mode).1
  have source1 := (compatibility mode).2.1
  have source2 := (compatibility mode).2.2
  change strongKnownBulk parameters lower positive bounded.le data 0 mode location=
    ((location ^ (-9/4 : ℝ) : ℝ) : ℂ) • unweightedSourceF0Bulk parameters lower graphs.1 mode location at source0
  change strongKnownBulk parameters lower positive bounded.le data 1 mode location=
    ((location ^ (-9/4 : ℝ) : ℝ) : ℂ) • unweightedSourceRF0Bulk parameters lower graphs.1 mode location at source1
  change strongKnownBulk parameters lower positive bounded.le data 2 mode location=
    ((location ^ (-9/4 : ℝ) : ℝ) : ℂ) • unweightedSourceF2Bulk parameters lower graphs.2 mode location at source2
  have power : lowPowerCurve lower (-9/4 : ℝ) positive location=location ^ (-9/4 : ℝ) := by
    change (max lower location) ^ (-9/4 : ℝ)=_
    rw [max_eq_right member.1]
  fin_cases slot
  · change (lowRhoPhysicalWeight parameters lower positive location mode : ℂ)⁻¹ •
      strongKnownBulk parameters lower positive bounded.le data 0 mode location=_
    rw [source0,f0]
    change _=knownGraphPhysicalSection parameters lower positive bounded 1 graphs.1 mode location
    rw [knownGraphPhysicalSection,power]
  · change (lowRhoPhysicalWeight parameters lower positive location mode : ℂ)⁻¹ •
      strongKnownBulk parameters lower positive bounded.le data 1 mode location=_
    rw [source1,rf0]
    change _=(Complex.I*(mode.1:ℂ)) • knownGraphPhysicalSection parameters lower positive bounded 1 graphs.1 mode location
    rw [knownGraphPhysicalSection,power]
    rw [smul_comm ((location ^ (-9/4 : ℝ) : ℝ) : ℂ) (Complex.I*(mode.1:ℂ)),
      smul_comm ((lowRhoPhysicalWeight parameters lower positive location mode : ℂ)⁻¹) (Complex.I*(mode.1:ℂ))]
  · change (lowRhoPhysicalWeight parameters lower positive location mode : ℂ)⁻¹ •
      strongKnownBulk parameters lower positive bounded.le data 2 mode location=_
    rw [source2,f2]
    change _=knownGraphPhysicalSection parameters lower positive bounded 0 graphs.2 mode location
    rw [knownGraphPhysicalSection,power]

 theorem fullSeven_known_outer (mode : ℤ×ℤ) (slot : Fin 3) :
    matrixUnit (0 : Fin 1) (⟨slot.val+4,by omega⟩ : Fin 7) (seven.physicalCurve 0 1 mode)=
      sourceBoundaryCoefficient parameters 0
        (highGraphOuterTuple parameters lower positive bounded 0
          (strongKnownGraphPair parameters lower positive bounded data) slot) mode := by
  rw [fullSeven_known_closed parameters lower length positive bounded lengthPositive data field seven 1 ⟨bounded.le,le_rfl⟩ mode slot]
  fin_cases slot
  · exact (knownGraphPhysicalSection_outer parameters lower positive bounded 1 _ mode).trans
      (originalGraphOuter_f0 parameters lower positive bounded _ mode).symm
  · exact (congrArg (fun value : ComplexEuclidean 1 => (Complex.I*(mode.1:ℂ)) • value)
      (knownGraphPhysicalSection_outer parameters lower positive bounded 1 _ mode)).trans
      (originalGraphOuter_rf0 parameters lower positive bounded _ mode).symm
  · exact (knownGraphPhysicalSection_outer parameters lower positive bounded 0 _ mode).trans
      (originalGraphOuter_f2 parameters lower positive bounded _ mode).symm

end Grad.OriginalCoreRealization
