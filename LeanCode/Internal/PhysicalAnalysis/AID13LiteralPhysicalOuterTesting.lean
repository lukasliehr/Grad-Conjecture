import AID12ActualPhysicalGreenIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCurrentGreen
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCircularForm
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighRegularity Grad.AnnularSourceGraph
open Grad.AnnularConverse Grad.AnnularCurrentBoundary Grad.AnnularUniformBoundary Grad.BoundaryKernelAction

theorem highBoundaryIntoPositive_single (parameters : PhaseParameters) (angular cell : ℕ)
    (mode : HighAnnularMode) (vector : ComplexEuclidean 1) :
    highBoundaryIntoPositive parameters angular cell (lp.single 2 mode vector) =
      (lp.single 2 mode.val vector : PositiveTrace parameters angular cell 1) := by
  classical
  apply lp.ext
  funext index
  by_cases high : 3 ≤ |index.1|
  · have law := highBoundaryIntoPositive_high parameters angular cell (lp.single 2 mode vector) (⟨index, high⟩ : HighAnnularMode)
    change highBoundaryIntoPositive parameters angular cell (lp.single 2 mode vector) index = _ at law
    rw [law]
    simp only [lp.single_apply, Pi.single_apply]
    by_cases same : index = mode.val
    · simp only [same, ite_true]
    · have subtypeDifferent : (⟨index, high⟩ : HighAnnularMode) ≠ mode := fun equality => same (congrArg Subtype.val equality)
      simp only [same, subtypeDifferent, if_false]
  · have different : index ≠ mode.val := by
      intro same
      subst index
      exact high mode.property
    rw [highBoundaryIntoPositive_low parameters angular cell _ index high]
    simp only [lp.single_apply, Pi.single_apply, different, if_false]

/-- Exact one-mode physical outer pairing, including the original sharp frequency factor. -/
theorem physicalOuterTest_single (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (angular cell : ℕ)
    (mode : HighAnnularMode) (core : complexSmoothRadialCore 1)
    (boundary : NegativeTrace parameters angular cell 1) :
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive angular cell
      (bEnergyNormalize lower L positive (annularEnergyCoreInto lower L positive (Finsupp.single mode core)))) boundary =
      inner ℂ (core.val.1 1)
        ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • boundary mode.val) := by
  rw [actualCurrentHighOuterTrace_same, bEnergyDecode_normalize, annularEnergyTrace_single, highBoundaryIntoPositive_single]
  have pairing := lp.inner_single_left (𝕜 := ℂ) (G := fun _ : ℤ × ℤ => ComplexEuclidean 1)
    mode.val ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • core.val.1 1) boundary
  exact pairing.trans (realScalar_pairing _ _ _)

/-- Free original outer tests force the actual endpoint of rX. No endpoint coordinate is an input. -/
theorem physicalFluxMomentGraph_outer (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : DivisionRow 3 lower) (boundary : NegativeTrace parameters 0 0 1)
    (equation : CompactPhysicalPacketEquation parameters lower L positive lengthPositive widthHalf widthLength field)
    (law : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test.val) field =
      inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test.val) boundary)
    (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
      (physicalFluxMomentGraph parameters lower L positive lengthPositive widthHalf widthLength
        (lowerHalf.trans_lt (by norm_num)) field equation mode) =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • boundary mode.val := by
  let profile := annularOuterProfile lower
  let smooth := annularOuterProfile_smooth lower
  apply ext_inner_left ℂ
  intro vector
  have testLaw := law ⟨bEnergyNormalize lower L positive (annularScalarTest lower L positive mode profile smooth vector),
    normalizedScalarTest_inner_zero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive mode profile smooth
      (annularOuterProfile_inner lower) vector⟩
  change inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength
    (bEnergyNormalize lower L positive (annularEnergyCoreInto lower L positive
      (Finsupp.single mode (smoothScalarRadialCore profile smooth vector))))) field =
    inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0
      (bEnergyNormalize lower L positive (annularEnergyCoreInto lower L positive
        (Finsupp.single mode (smoothScalarRadialCore profile smooth vector))))) boundary at testLaw
  rw [physicalFlux_packet_green parameters lower L positive lengthPositive widthHalf widthLength
    (lowerHalf.trans_lt (by norm_num)) field equation mode, physicalOuterTest_single] at testLaw
  change inner ℂ (profile 1 • vector) _ - inner ℂ (profile lower • vector) _ = inner ℂ (profile 1 • vector) _ at testLaw
  rw [show profile 1 = 1 from annularOuterProfile_outer lower (lowerHalf.trans_lt (by norm_num)),
    show profile lower = 0 from annularOuterProfile_inner lower,
    one_smul, zero_smul, inner_zero_left, sub_zero] at testLaw
  exact testLaw

end Grad.AnnularCurrentGreen
