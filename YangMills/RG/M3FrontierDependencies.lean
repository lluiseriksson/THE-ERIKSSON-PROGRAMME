/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier

/-!
# Executable dependency graph for the raw-source M3 frontier

This file is an audit layer for `CMP116RawSourceM3Frontier`.  It records the
frontier fields as named graph nodes, classifies each field by role, and lists
the source-independent dependency spine currently used by the raw-H# frontier
projection and the wrapper `lattice_mass_gap_of_cmp116RawSourceM3Frontier`.

The graph is not a source theorem.  It deliberately does not add any new field
to the frontier and does not make `hraw`, H#, `SingleScaleUVDecay`, or the M3
mass-gap conclusion into source assumptions.
-/

namespace YangMills.RG

/-- Coarse audit class for a remaining frontier field. -/
inductive M3FrontierHypothesisKind where
  | analytic
  | geometric
  | measureTheoretic
  | rgFlow
deriving DecidableEq, BEq, Repr

/-- One constructor for each field of `CMP116RawSourceM3Frontier`. -/
inductive CMP116RawSourceM3FrontierField where
  | covarianceRootCertificate
  | rawSource
  | spectatorSupportSubset
  | fluctuationSupportSubset
  | weightNonneg
  | activeSupportSubsetOmega
  | activeSupportSubsetSkeleton
  | weightDomination
  | holesPairwiseDisjoint
  | noEdgesBetweenHoles
  | holesNonempty
  | appendixFGeometricSmallness
  | activityStronglyMeasurable
  | probabilityLaw
  | amplitudeNonneg
  | amplitudeLeOne
  | profileConstantNonneg
  | hbarNonneg
  | kappaMargin
  | kappa0GtOne
  | couplingPositive
  | halfBudget
  | profileBound
  | epsilonPositive
  | timeDecayPositive
  | betaFlowPositive
  | couplingSmall
  | couplingRecursion
  | irBound
  | rootedHsharpRemainderIdentity
deriving DecidableEq, BEq, Repr

namespace CMP116RawSourceM3FrontierField

/-- Stable list of all raw-source M3 frontier fields. -/
def all : List CMP116RawSourceM3FrontierField :=
  [ covarianceRootCertificate
  , rawSource
  , spectatorSupportSubset
  , fluctuationSupportSubset
  , weightNonneg
  , activeSupportSubsetOmega
  , activeSupportSubsetSkeleton
  , weightDomination
  , holesPairwiseDisjoint
  , noEdgesBetweenHoles
  , holesNonempty
  , appendixFGeometricSmallness
  , activityStronglyMeasurable
  , probabilityLaw
  , amplitudeNonneg
  , amplitudeLeOne
  , profileConstantNonneg
  , hbarNonneg
  , kappaMargin
  , kappa0GtOne
  , couplingPositive
  , halfBudget
  , profileBound
  , epsilonPositive
  , timeDecayPositive
  , betaFlowPositive
  , couplingSmall
  , couplingRecursion
  , irBound
  , rootedHsharpRemainderIdentity
  ]

/-- Classification of each frontier field by the role it plays in the M3 path. -/
def kind : CMP116RawSourceM3FrontierField → M3FrontierHypothesisKind
  | covarianceRootCertificate => .analytic
  | rawSource => .analytic
  | spectatorSupportSubset => .geometric
  | fluctuationSupportSubset => .geometric
  | weightNonneg => .analytic
  | activeSupportSubsetOmega => .geometric
  | activeSupportSubsetSkeleton => .geometric
  | weightDomination => .geometric
  | holesPairwiseDisjoint => .geometric
  | noEdgesBetweenHoles => .geometric
  | holesNonempty => .geometric
  | appendixFGeometricSmallness => .geometric
  | activityStronglyMeasurable => .measureTheoretic
  | probabilityLaw => .measureTheoretic
  | amplitudeNonneg => .analytic
  | amplitudeLeOne => .analytic
  | profileConstantNonneg => .analytic
  | hbarNonneg => .analytic
  | kappaMargin => .analytic
  | kappa0GtOne => .rgFlow
  | couplingPositive => .rgFlow
  | halfBudget => .analytic
  | profileBound => .analytic
  | epsilonPositive => .rgFlow
  | timeDecayPositive => .rgFlow
  | betaFlowPositive => .rgFlow
  | couplingSmall => .rgFlow
  | couplingRecursion => .rgFlow
  | irBound => .rgFlow
  | rootedHsharpRemainderIdentity => .analytic

end CMP116RawSourceM3FrontierField

/-- Source fields plus the derived formal consumers they feed. -/
inductive M3FrontierDependencyNode where
  | field : CMP116RawSourceM3FrontierField → M3FrontierDependencyNode
  | rawSourceScaleFamily
  | rawHsharpFrontierProjection
  | rawSourceHsharpUVDecay
  | marginalM3Assembly
deriving DecidableEq, BEq, Repr

namespace M3FrontierDependencyNode

/-- Every node in the current dependency graph. -/
def all : List M3FrontierDependencyNode :=
  CMP116RawSourceM3FrontierField.all.map field ++
    [ rawSourceScaleFamily
    , rawHsharpFrontierProjection
    , rawSourceHsharpUVDecay
    , marginalM3Assembly
    ]

/-- A topological rank.  Edges point only to lower-rank nodes. -/
def rank : M3FrontierDependencyNode → Nat
  | field _ => 0
  | rawSourceScaleFamily => 1
  | rawHsharpFrontierProjection => 2
  | rawSourceHsharpUVDecay => 3
  | marginalM3Assembly => 4

end M3FrontierDependencyNode

namespace M3FrontierDependencyGraph

/-- The raw-source scale family is the transport adapter behind the H# endpoint. -/
def rawSourceScaleFamilyInputs : List CMP116RawSourceM3FrontierField :=
  [ .covarianceRootCertificate
  , .rawSource
  , .spectatorSupportSubset
  , .fluctuationSupportSubset
  , .amplitudeNonneg
  , .weightNonneg
  , .activityStronglyMeasurable
  , .activeSupportSubsetOmega
  , .activeSupportSubsetSkeleton
  , .weightDomination
  ]

/-- Inputs consumed by the raw-H# frontier projection after scale-family transport. -/
def rawSourceHsharpUVInputs : List CMP116RawSourceM3FrontierField :=
  [ .amplitudeLeOne
  , .profileConstantNonneg
  , .hbarNonneg
  , .kappaMargin
  , .kappa0GtOne
  , .couplingPositive
  , .rootedHsharpRemainderIdentity
  , .probabilityLaw
  , .holesPairwiseDisjoint
  , .noEdgesBetweenHoles
  , .holesNonempty
  , .appendixFGeometricSmallness
  , .halfBudget
  , .profileBound
  ]

/-- Consumer-side marginal and IR inputs for the final M3 assembly. -/
def marginalAssemblyInputs : List CMP116RawSourceM3FrontierField :=
  [ .epsilonPositive
  , .timeDecayPositive
  , .kappa0GtOne
  , .betaFlowPositive
  , .couplingPositive
  , .couplingSmall
  , .couplingRecursion
  , .irBound
  ]

/-- Incoming edges for the executable audit graph. -/
def dependencies : M3FrontierDependencyNode → List M3FrontierDependencyNode
  | .field _ => []
  | .rawSourceScaleFamily =>
      rawSourceScaleFamilyInputs.map M3FrontierDependencyNode.field
  | .rawHsharpFrontierProjection =>
      .rawSourceScaleFamily ::
        rawSourceHsharpUVInputs.map M3FrontierDependencyNode.field
  | .rawSourceHsharpUVDecay =>
      [.rawHsharpFrontierProjection]
  | .marginalM3Assembly =>
      .rawSourceHsharpUVDecay ::
        marginalAssemblyInputs.map M3FrontierDependencyNode.field

/-- Derived proof-routing nodes, distinct from source/frontier fields. -/
def derivedNodes : List M3FrontierDependencyNode :=
  [ .rawSourceScaleFamily
  , .rawHsharpFrontierProjection
  , .rawSourceHsharpUVDecay
  , .marginalM3Assembly
  ]

/-- Derived nodes whose purpose is to feed another derived consumer. -/
def nonterminalDerivedNodes : List M3FrontierDependencyNode :=
  [ .rawSourceScaleFamily
  , .rawHsharpFrontierProjection
  , .rawSourceHsharpUVDecay
  ]

/-- All incoming edges to derived consumers.  Field nodes have no dependencies. -/
def derivedDependencyInputs : List M3FrontierDependencyNode :=
  dependencies .rawSourceScaleFamily ++
    dependencies .rawHsharpFrontierProjection ++
      dependencies .rawSourceHsharpUVDecay ++
        dependencies .marginalM3Assembly

/-- Every dependency must point backward in the declared topological order. -/
def edgesPointBackward : Bool :=
  M3FrontierDependencyNode.all.all
    (fun n =>
      (dependencies n).all
        (fun m => M3FrontierDependencyNode.rank m < M3FrontierDependencyNode.rank n))

/-- Executable acyclicity check for this finite dependency graph. -/
def isAcyclic : Bool :=
  edgesPointBackward

/-- Every frontier field has a corresponding graph node. -/
def allFrontierFieldsCovered : Bool :=
  CMP116RawSourceM3FrontierField.all.all
    (fun f => M3FrontierDependencyNode.all.contains (.field f))

/-- All frontier fields consumed as inputs by at least one derived node. -/
def allInputFields : List CMP116RawSourceM3FrontierField :=
  rawSourceScaleFamilyInputs ++ rawSourceHsharpUVInputs ++ marginalAssemblyInputs

/-- Every frontier field is used by the current derived dependency spine. -/
def allFrontierFieldsUsed : Bool :=
  CMP116RawSourceM3FrontierField.all.all
    (fun f => allInputFields.contains f)

/-- Derived formal consumers are not frontier/source fields. -/
def derivedNodesHavePositiveRank : Bool :=
  derivedNodes.all
    (fun n => 0 < M3FrontierDependencyNode.rank n)

/-- No intermediate derived node is orphaned in the current dependency spine. -/
def nonterminalDerivedNodesUsed : Bool :=
  nonterminalDerivedNodes.all
    (fun n => derivedDependencyInputs.contains n)

/-- Bounded reachability along incoming dependency edges. -/
def dependsOnWithin : Nat →
    M3FrontierDependencyNode → M3FrontierDependencyNode → Bool
  | 0, consumer, source => consumer == source
  | fuel + 1, consumer, source =>
      (consumer == source) ||
        (dependencies consumer).any
          (fun next => dependsOnWithin fuel next source)

/-- The finite fuel used for dependency-closure checks. -/
def dependencyClosureFuel : Nat :=
  M3FrontierDependencyNode.all.length

/-- Every frontier field reaches the final marginal M3 assembly node. -/
def marginalAssemblyDependsOnAllFrontierFields : Bool :=
  CMP116RawSourceM3FrontierField.all.all
    (fun f =>
      dependsOnWithin dependencyClosureFuel .marginalM3Assembly (.field f))

theorem isAcyclic_eq_true : isAcyclic = true := by
  decide

theorem allFrontierFieldsCovered_eq_true :
    allFrontierFieldsCovered = true := by
  decide

theorem allFrontierFieldsUsed_eq_true :
    allFrontierFieldsUsed = true := by
  decide

theorem derivedNodesHavePositiveRank_eq_true :
    derivedNodesHavePositiveRank = true := by
  decide

theorem nonterminalDerivedNodesUsed_eq_true :
    nonterminalDerivedNodesUsed = true := by
  decide

theorem marginalAssemblyDependsOnAllFrontierFields_eq_true :
    marginalAssemblyDependsOnAllFrontierFields = true := by
  decide

end M3FrontierDependencyGraph

#guard CMP116RawSourceM3FrontierField.all.length == 30
#guard M3FrontierDependencyNode.all.length == 34
#guard M3FrontierDependencyGraph.isAcyclic
#guard M3FrontierDependencyGraph.allFrontierFieldsCovered
#guard M3FrontierDependencyGraph.allFrontierFieldsUsed
#guard M3FrontierDependencyGraph.derivedNodesHavePositiveRank
#guard M3FrontierDependencyGraph.nonterminalDerivedNodesUsed
#guard M3FrontierDependencyGraph.marginalAssemblyDependsOnAllFrontierFields

end YangMills.RG
