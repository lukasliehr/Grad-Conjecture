import AKAE3ExactCartesianPolarDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianDescent
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryLift
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.BoundaryTrace

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

include bounded compatible in
theorem physicalFamilyCurve_agree (first second grade : ℕ) (radius : ℝ)
    (firstInside : radius ∈ Icc (lower first) 1) (secondInside : radius ∈ Icc (lower second) 1) :
    (curves first).physicalCurve grade radius = (curves second).physicalCurve grade radius := by
  rcases le_total first second with order|order
  · exact ((curves second).physicalCurve_restriction (curves first) (bounded second) (bounded first)
      (decreasing order) (compatible first second order) grade radius firstInside).symm
  · exact (curves first).physicalCurve_restriction (curves second) (bounded first) (bounded second)
      (decreasing order) (compatible second first order) grade radius secondInside

include compatible in
theorem physicalFamilyField_agree (first second : ℕ) (radius : ℝ)
    (firstInside : radius ∈ Icc (lower first) 1) (secondInside : radius ∈ Icc (lower second) 1) (angles : ℝ × ℝ) :
    (curves first).fullField (bounded first) (radius,angles) = (curves second).fullField (bounded second) (radius,angles) := by
  rcases le_total first second with order|order
  · exact ((curves second).fullField_restriction (curves first) (bounded second) (bounded first)
      (decreasing order) (compatible first second order) radius angles.1 angles.2 firstInside).symm
  · exact (curves first).fullField_restriction (curves second) (bounded first) (bounded second)
      (decreasing order) (compatible second first order) radius angles.1 angles.2 secondInside

 def physicalFamilySections (grade : ℕ) (index : ℕ) : C(Icc (lower index) (1 : ℝ),CellL2 dimension) :=
  ⟨fun radius => (curves index).physicalCurve grade radius.val,
    (curves index).physicalCurve_smooth (bounded index) grade |>.continuousOn.domRestrict⟩

def gluedPhysicalFamilyCurve (grade : ℕ) : ℝ → CellL2 dimension :=
  gluedClosedSections lower cofinal (physicalFamilySections parameters lower positive bounded rows curves grade)

def gluedPhysicalFamilyField (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean dimension :=
  if inside : point.1 ∈ Ioc (0 : ℝ) 1 then
    (curves (selectedInnerCollar lower cofinal point.1 inside.1)).fullField
      (bounded (selectedInnerCollar lower cofinal point.1 inside.1)) point
  else 0

include compatible in
theorem gluedPhysicalFamilyCurve_same (grade index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) :
    gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves grade radius =
      (curves index).physicalCurve grade radius :=
  gluedClosedSections_same lower cofinal (physicalFamilySections parameters lower positive bounded rows curves grade) positive
    (fun first second radius one two => physicalFamilyCurve_agree parameters lower positive bounded decreasing rows curves compatible
      first second grade radius one two) index radius inside

include compatible in
theorem gluedPhysicalFamilyField_same (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) (angles : ℝ × ℝ) :
    gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves (radius,angles) =
      (curves index).fullField (bounded index) (radius,angles) := by
  have punctured : radius ∈ Ioc (0 : ℝ) 1 := ⟨(positive index).trans_le inside.1,inside.2⟩
  rw [gluedPhysicalFamilyField,dif_pos punctured]
  exact physicalFamilyField_agree parameters lower positive bounded decreasing rows curves compatible
    _ index radius ⟨(selectedInnerCollar_lt lower cofinal radius punctured.1).le,punctured.2⟩ inside angles

 theorem gluedPhysicalFamilyField_periodic (radius axial : ℝ) :
    Function.Periodic (fun polar => gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves (radius,polar,axial)) (2*Real.pi) := by
  intro polar
  change gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves (radius,polar+2*Real.pi,axial) =
    gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves (radius,polar,axial)
  unfold gluedPhysicalFamilyField
  split_ifs with inside
  · exact (curves _).fullField_angular_shift (bounded _) radius polar axial
  · rfl

include compatible in
theorem gluedPhysicalFamilyField_smooth :
    ContDiffOn ℝ ∞ (gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ × ℝ))) := by
  intro point inside
  let index := selectedInnerCollar lower cofinal point.1 inside.1.1
  have below : lower index < point.1 := selectedInnerCollar_lt lower cofinal point.1 inside.1.1
  have localSmooth : ContDiffAt ℝ ∞ ((curves index).fullField (bounded index)) point :=
    ((curves index).fullField_smooth (bounded index)).contDiffAt
      (mem_of_superset ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨below,inside.1.2⟩,mem_univ _⟩)
        (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,member.2⟩))
  apply ContDiffAt.contDiffWithinAt
  apply localSmooth.congr_of_eventuallyEq
  filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨below,inside.1.2⟩] with other member
  exact gluedPhysicalFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible
    index other.1 ⟨member.1.le,member.2.le⟩ other.2

def gluedCartesianFamilyField : SpatialPlane × ℝ → ComplexEuclidean dimension :=
  cartesianPhysicalField (gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves)

include compatible in
theorem gluedCartesianFamilyField_smoothAt (point : SpatialPlane × ℝ) (nonzero : point.1 ≠ 0) (inside : ‖point.1‖ < 1) :
    ContDiffAt ℝ ∞ (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves) point :=
  cartesianPhysicalField_smoothAt _ 0 1
    (gluedPhysicalFamilyField_smooth parameters lower positive bounded cofinal decreasing rows curves compatible)
    (gluedPhysicalFamilyField_periodic parameters lower positive bounded cofinal rows curves) point nonzero ⟨norm_pos_iff.mpr nonzero,inside⟩

include compatible in
theorem gluedCartesianFamilyField_same (index : ℕ) (point : SpatialPlane × ℝ) (inside : ‖point.1‖ ∈ Icc (lower index) 1) :
    gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves point =
      (curves index).cartesianField (bounded index) point := by
  unfold gluedCartesianFamilyField SmoothLowPhysicalRow.cartesianField cartesianPhysicalField cartesianFromPolar
  rw [complexCoordinate_norm]
  exact gluedPhysicalFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible
    index ‖point.1‖ inside _

include compatible in
theorem gluedPhysicalFamilyField_coefficient (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves (radius,angles)) mode =
      gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves 0 radius mode := by
  simp_rw [gluedPhysicalFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index radius inside]
  rw [(curves index).fullField_doubleCoefficient (bounded index) radius inside mode,
    gluedPhysicalFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 index radius inside]

end Grad.ActualCartesianDescent
