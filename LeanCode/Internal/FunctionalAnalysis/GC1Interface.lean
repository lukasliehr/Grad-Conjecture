import TCX1Proof
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

namespace Grad.GenericCarriers

open Grad.PDEBootstrap (Spatial)

universe valueUniverse indexUniverse

abbrev PhysicalValue (dimension : ℕ) := EuclideanSpace ℂ (Fin dimension)

abbrev Cells (Value : Type valueUniverse) [NormedAddCommGroup Value] : Type valueUniverse :=
  lp (fun _ : ℤ => Value) 2

abbrev Tensor (rank : ℕ) (Value : Type valueUniverse) [NormedAddCommGroup Value] :=
  PiLp 2 (fun _ : Fin rank → Fin 2 => Value)

abbrev DomainL2 (Value : Type valueUniverse) [NormedAddCommGroup Value]
    (domain : Set Spatial) : Type valueUniverse := Lp Value 2 (volume.restrict domain)

abbrev GraphTuple (Index : Type indexUniverse) [Fintype Index]
    (Fiber : Index → Type valueUniverse) [∀ index, NormedAddCommGroup (Fiber index)] :=
  PiLp 2 Fiber

abbrev CellValues (dimension : ℕ) := Cells (PhysicalValue dimension)

abbrev OrderedCellValues (dimension rank : ℕ) := Tensor rank (CellValues dimension)

abbrev FieldL2 (dimension : ℕ) (domain : Set Spatial) :=
  DomainL2 (CellValues dimension) domain

abbrev OrderedFields (dimension rank : ℕ) (domain : Set Spatial) :=
  Tensor rank (FieldL2 dimension domain)

abbrev OrderedValueField (dimension rank : ℕ) (domain : Set Spatial) :=
  DomainL2 (OrderedCellValues dimension rank) domain

abbrev GraphFields (dimension count : ℕ) (ranks : Fin count → ℕ) (domain : Set Spatial) :=
  GraphTuple (Fin count) (fun entry => OrderedFields dimension (ranks entry) domain)

def physicalOfCoordinates (dimension : ℕ) (coordinates : Fin dimension → ℂ) : PhysicalValue dimension :=
  WithLp.toLp 2 coordinates

def physicalProjection (dimension : ℕ) (coordinate : Fin dimension) : PhysicalValue dimension →L[ℂ] ℂ :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) coordinate

def cellsOfCoordinates {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (coordinates : ℤ → Value) (membership : Memℓp coordinates 2) : Cells Value :=
  ⟨coordinates, membership⟩

def cellSingle (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (cell : ℤ) : Value →L[ℂ] Cells Value :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℤ => Value) 2 cell

def cellProjection (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (cell : ℤ) : Cells Value →L[ℂ] Value :=
  lp.evalCLM ℂ (fun _ : ℤ => Value) 2 cell

def tensorOfCoordinates {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (rank : ℕ) (coordinates : (Fin rank → Fin 2) → Value) : Tensor rank Value :=
  WithLp.toLp 2 coordinates

def tensorProjection (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (rank : ℕ) (word : Fin rank → Fin 2) : Tensor rank Value →L[ℂ] Value :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin rank → Fin 2 => Value) word

def graphOfCoordinates {Index : Type indexUniverse} [Fintype Index]
    {Fiber : Index → Type valueUniverse} [∀ index, NormedAddCommGroup (Fiber index)]
    (coordinates : ∀ index, Fiber index) : GraphTuple Index Fiber :=
  WithLp.toLp 2 coordinates

def graphProjection (Index : Type indexUniverse) [Fintype Index]
    (Fiber : Index → Type valueUniverse) [∀ index, NormedAddCommGroup (Fiber index)]
    [∀ index, NormedSpace ℂ (Fiber index)] (index : Index) :
    GraphTuple Index Fiber →L[ℂ] Fiber index := PiLp.proj (𝕜 := ℂ) 2 Fiber index

def fieldOfRepresentative {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (domain : Set Spatial) (representative : Spatial → Value)
    (membership : MemLp representative 2 (volume.restrict domain)) : DomainL2 Value domain :=
  membership.toLp representative

def fieldCellProjection (dimension : ℕ) (domain : Set Spatial) (cell : ℤ) :
    FieldL2 dimension domain →L[ℂ] DomainL2 (PhysicalValue dimension) domain :=
  (cellProjection (PhysicalValue dimension) cell).compLpL 2 (volume.restrict domain)

def fieldTensorProjection (dimension rank : ℕ) (domain : Set Spatial)
    (word : Fin rank → Fin 2) : OrderedValueField dimension rank domain →L[ℂ] FieldL2 dimension domain :=
  (tensorProjection (CellValues dimension) rank word).compLpL 2 (volume.restrict domain)

def CoordinateGoal : Prop :=
  (∀ (dimension : ℕ) (coordinates : Fin dimension → ℂ) (coordinate : Fin dimension),
    physicalProjection dimension coordinate (physicalOfCoordinates dimension coordinates) =
      coordinates coordinate) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value]
      (coordinates : ℤ → Value) (membership : Memℓp coordinates 2) (cell : ℤ),
    cellsOfCoordinates coordinates membership cell = coordinates cell) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
      (cells : Cells Value) (cell : ℤ), cellProjection Value cell cells = cells cell) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
      (cell other : ℤ) (value : Value),
    cellSingle Value cell value other = if other = cell then value else 0) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value]
      (rank : ℕ) (coordinates : (Fin rank → Fin 2) → Value) (word : Fin rank → Fin 2),
    tensorProjection Value rank word (tensorOfCoordinates rank coordinates) = coordinates word) ∧
  (∀ (Index : Type indexUniverse) [Fintype Index] (Fiber : Index → Type valueUniverse)
      [∀ index, NormedAddCommGroup (Fiber index)] [∀ index, NormedSpace ℂ (Fiber index)]
      (coordinates : ∀ index, Fiber index) (index : Index),
    graphProjection Index Fiber index (graphOfCoordinates coordinates) = coordinates index)

def RepresentativeGoal : Prop :=
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] (domain : Set Spatial)
      (representative : Spatial → Value) (membership : MemLp representative 2 (volume.restrict domain)),
    ∀ᵐ point ∂volume.restrict domain,
      fieldOfRepresentative domain representative membership point = representative point) ∧
  (∀ (dimension : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain),
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      fieldCellProjection dimension domain cell field point = field point cell) ∧
  (∀ (dimension rank : ℕ) (domain : Set Spatial) (field : OrderedValueField dimension rank domain),
    ∀ᵐ point ∂volume.restrict domain, ∀ word : Fin rank → Fin 2,
      fieldTensorProjection dimension rank domain word field point = field point word)

def NormSquareGoal : Prop :=
  (∀ (dimension : ℕ) (value : PhysicalValue dimension),
    ‖value‖ ^ 2 = ∑ coordinate : Fin dimension, ‖value coordinate‖ ^ 2) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] (cells : Cells Value),
    ‖cells‖ ^ 2 = ∑' cell : ℤ, ‖cells cell‖ ^ 2) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] (rank : ℕ) (tensor : Tensor rank Value),
    ‖tensor‖ ^ 2 = ∑ word : Fin rank → Fin 2, ‖tensor word‖ ^ 2) ∧
  (∀ (Index : Type indexUniverse) [Fintype Index] (Fiber : Index → Type valueUniverse)
      [∀ index, NormedAddCommGroup (Fiber index)] (graph : GraphTuple Index Fiber),
    ‖graph‖ ^ 2 = ∑ index : Index, ‖graph index‖ ^ 2) ∧
  (∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
      (domain : Set Spatial) (field : DomainL2 Value domain),
    ‖field‖ ^ 2 = ∫ point : Spatial, ‖field point‖ ^ 2 ∂volume.restrict domain) ∧
  (∀ (dimension rank : ℕ) (tensor : OrderedCellValues dimension rank),
    ‖tensor‖ ^ 2 = ∑ word : Fin rank → Fin 2, ∑' cell : ℤ, ‖tensor word cell‖ ^ 2) ∧
  (∀ (dimension count : ℕ) (ranks : Fin count → ℕ) (domain : Set Spatial)
      (graph : GraphFields dimension count ranks domain),
    ‖graph‖ ^ 2 = ∑ entry : Fin count, ∑ word : Fin (ranks entry) → Fin 2,
      ∫ point : Spatial, ‖graph entry word point‖ ^ 2 ∂volume.restrict domain)

def CompleteSeparable (Value : Type valueUniverse) [UniformSpace Value] : Prop :=
  CompleteSpace Value ∧ SecondCountableTopology Value ∧ SeparableSpace Value

def TopologyGoal : Prop :=
  (∀ dimension : ℕ, CompleteSeparable (PhysicalValue dimension) ∧
    CompleteSeparable (CellValues dimension) ∧
    ∀ rank : ℕ, CompleteSeparable (Tensor rank (PhysicalValue dimension)) ∧
      CompleteSeparable (OrderedCellValues dimension rank)) ∧
  (∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    CompleteSeparable (FieldL2 dimension domain) ∧
    (∀ rank : ℕ, CompleteSeparable (OrderedFields dimension rank domain) ∧
      CompleteSeparable (OrderedValueField dimension rank domain)) ∧
    ∀ (count : ℕ) (ranks : Fin count → ℕ),
      CompleteSeparable (GraphFields dimension count ranks domain))

def CompatibilityGoal : Prop :=
  CellValues 3 = Grad.PDEBootstrap.CellValues ∧
  FieldL2 3 Set.univ = Grad.PDEBootstrap.FieldL2 ∧
  (∀ rank : ℕ, OrderedCellValues 3 rank = Grad.TensorLpExchange.OrderedCellValues rank) ∧
  (∀ rank : ℕ, OrderedFields 3 rank Set.univ = Grad.KernelArrays.OrderedFields rank) ∧
  (∀ rank : ℕ, OrderedValueField 3 rank Set.univ = Grad.TensorLpExchange.OrderedValueField rank) ∧
  GraphTuple (Fin 3) (fun _ => FieldL2 3 Set.univ) = Grad.PDEBootstrap.FirstJet

def BlockGoal : Prop :=
  CoordinateGoal.{valueUniverse, indexUniverse} ∧ RepresentativeGoal.{valueUniverse} ∧
  NormSquareGoal.{valueUniverse, indexUniverse} ∧ TopologyGoal ∧ CompatibilityGoal

end Grad.GenericCarriers
