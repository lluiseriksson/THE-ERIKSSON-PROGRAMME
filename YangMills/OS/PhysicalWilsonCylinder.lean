import YangMills.OS.PhysicalWilsonSquare

/-!
# The two-link spatial Wilson cylinder

Four vertices, six independent positive edges and two crossing plaquettes.
The two spatial edges on each circle are distinct, even though their endpoints
are reversed. The twelve oriented edges record reversal separately.

The concrete geometry, configuration map and reflection are constructed here.
No product measure, positivity, transfer operator or mass gap is asserted.
-/

namespace YangMills.OS

/-- Lower slice, upper slice, then the two crossing links. -/
abbrev WilsonCylinder (G : Type*) := ((G × G) × (G × G)) × (G × G)

namespace WilsonCylinder

abbrev Edge := Fin 6 × Bool

def vertex (t x : Fin 2) : FinBox 2 2 := ![t, x]

def positiveSrc : Fin 6 → FinBox 2 2 :=
  ![vertex 0 0, vertex 0 1, vertex 1 0, vertex 1 1, vertex 0 0, vertex 0 1]

def positiveDst : Fin 6 → FinBox 2 2 :=
  ![vertex 0 1, vertex 0 0, vertex 1 1, vertex 1 0, vertex 1 0, vertex 1 1]

def reverseEdge (e : Edge) : Edge := (e.1, !e.2)

def edgeSrc (e : Edge) : FinBox 2 2 :=
  if e.2 then positiveDst e.1 else positiveSrc e.1

def edgeDst (e : Edge) : FinBox 2 2 :=
  if e.2 then positiveSrc e.1 else positiveDst e.1

def boundaryEdge : Fin 2 → Fin 4 → Edge :=
  ![![(0, false), (5, false), (2, true), (4, true)],
    ![(1, false), (4, false), (3, true), (5, true)]]

def boundaryVertex : Fin 2 → Fin 4 → FinBox 2 2 :=
  ![![vertex 0 0, vertex 0 1, vertex 1 1, vertex 1 0],
    ![vertex 0 1, vertex 0 0, vertex 1 0, vertex 1 1]]

theorem boundaryEdge_src (p : Fin 2) (i : Fin 4) :
    edgeSrc (boundaryEdge p i) = boundaryVertex p i := by
  fin_cases p <;> fin_cases i <;> rfl

theorem boundaryEdge_dst (p : Fin 2) (i : Fin 4) :
    edgeDst (boundaryEdge p i) = boundaryVertex p (succ4 i) := by
  fin_cases p <;> fin_cases i <;> rfl

variable {G : Type*} [Group G]

/-- The complete finite cylinder geometry; no geometric condition is caller data. -/
abbrev geometry (G : Type*) [Group G] : FiniteLatticeGeometry 2 2 G where
  E := Edge
  P := Fin 2
  fintypeE := inferInstance
  fintypeP := inferInstance
  src := edgeSrc
  dst := edgeDst
  reverse := reverseEdge
  reverse_involutive e := by simp [reverseEdge]
  src_reverse e := by rcases e with ⟨i, b⟩; cases b <;> rfl
  dst_reverse e := by rcases e with ⟨i, b⟩; cases b <;> rfl
  plaquetteVertex := boundaryVertex
  plaquetteEdge := boundaryEdge
  plaquetteEdge_src := boundaryEdge_src
  plaquetteEdge_dst := boundaryEdge_dst
  plaquette_gauge_telescope := by intros; group

attribute [local instance] geometry

def linkValues (A : WilsonCylinder G) : Fin 6 → G :=
  ![A.1.1.1, A.1.1.2, A.1.2.1, A.1.2.2, A.2.1, A.2.2]

def edgeValue (A : WilsonCylinder G) (e : Edge) : G :=
  if e.2 then (linkValues A e.1)⁻¹ else linkValues A e.1

/-- Every six-tuple defines a reversal-compatible configuration on this geometry. -/
def toGaugeConfig (A : WilsonCylinder G) :
    @GaugeConfig 2 2 G _ (geometry G) where
  toFun := edgeValue A
  map_reverse e := by
    change edgeValue A (reverseEdge e) = (edgeValue A e)⁻¹
    rcases e with ⟨i, b⟩
    cases b <;> simp [edgeValue, reverseEdge]

def fromGaugeConfig (A : @GaugeConfig 2 2 G _ (geometry G)) : WilsonCylinder G :=
  (((A (0, false), A (1, false)), (A (2, false), A (3, false))),
    (A (4, false), A (5, false)))

theorem fromGaugeConfig_toGaugeConfig (A : WilsonCylinder G) :
    fromGaugeConfig (toGaugeConfig A) = A := rfl

theorem toGaugeConfig_injective : Function.Injective (toGaugeConfig (G := G)) :=
  Function.LeftInverse.injective fromGaugeConfig_toGaugeConfig

def face0 (A : WilsonCylinder G) : G :=
  A.1.1.1 * A.2.2 * (A.1.2.1)⁻¹ * (A.2.1)⁻¹

def face1 (A : WilsonCylinder G) : G :=
  A.1.1.2 * A.2.1 * (A.1.2.2)⁻¹ * (A.2.2)⁻¹

theorem plaquetteHolonomy_zero (A : WilsonCylinder G) :
    @GaugeConfig.plaquetteHolonomy 2 2 G _ (geometry G) (toGaugeConfig A) (0 : Fin 2) =
      face0 A := rfl

theorem plaquetteHolonomy_one (A : WilsonCylinder G) :
    @GaugeConfig.plaquetteHolonomy 2 2 G _ (geometry G) (toGaugeConfig A) (1 : Fin 2) =
      face1 A := rfl

/-- The first face uses the previously checked four-link boundary convention. -/
theorem face0_eq_square (A : WilsonCylinder G) :
    face0 A = WilsonSquare.holonomy ![A.1.1.1, A.2.2, A.1.2.1, A.2.1] := rfl

theorem face1_eq_square (A : WilsonCylinder G) :
    face1 A = WilsonSquare.holonomy ![A.1.1.2, A.2.1, A.1.2.2, A.2.2] := rfl

def reflect (A : WilsonCylinder G) : WilsonCylinder G :=
  ((A.1.2, A.1.1), ((A.2.1)⁻¹, (A.2.2)⁻¹))

theorem reflect_involutive : Function.Involutive (reflect (G := G)) := by
  intro A
  simp [reflect]

def reflectVertex (v : FinBox 2 2) : FinBox 2 2 := ![![1, 0] (v 0), v 1]

def reflectPositiveEdge : Fin 6 → Edge :=
  ![(2, false), (3, false), (0, false), (1, false), (4, true), (5, true)]

def reflectEdge (e : Edge) : Edge :=
  if e.2 then reverseEdge (reflectPositiveEdge e.1) else reflectPositiveEdge e.1

theorem reflectEdge_involutive : Function.Involutive reflectEdge := by
  rintro ⟨i, b⟩
  fin_cases i <;> cases b <;> rfl

theorem reflectEdge_src (e : Edge) :
    edgeSrc (reflectEdge e) = reflectVertex (edgeSrc e) := by
  rcases e with ⟨i, b⟩
  fin_cases i <;> cases b <;> rfl

theorem reflectEdge_dst (e : Edge) :
    edgeDst (reflectEdge e) = reflectVertex (edgeDst e) := by
  rcases e with ⟨i, b⟩
  fin_cases i <;> cases b <;> rfl

/-- Reflection really pulls back the constructed oriented-edge configuration. -/
theorem toGaugeConfig_reflect (A : WilsonCylinder G) (e : Edge) :
    toGaugeConfig (reflect A) e = toGaugeConfig A (reflectEdge e) := by
  rcases e with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    simp [toGaugeConfig, edgeValue, linkValues, reflect, reflectEdge,
      reflectPositiveEdge, reverseEdge]

theorem face0_reflect (A : WilsonCylinder G) :
    face0 (reflect A) = (A.2.1)⁻¹ * (face0 A)⁻¹ * A.2.1 := by
  unfold face0 reflect
  dsimp
  group

theorem face1_reflect (A : WilsonCylinder G) :
    face1 (reflect A) = (A.2.2)⁻¹ * (face1 A)⁻¹ * A.2.2 := by
  unfold face1 reflect
  dsimp
  group

/-- Upper-slice vertex gauge transform determined by the two crossing links. -/
def gaugeUpper (a v : G × G) : G × G :=
  (a.1 * v.1 * a.2⁻¹, a.2 * v.2 * a.1⁻¹)

theorem face0_eq_relative_gaugeUpper (A : WilsonCylinder G) :
    face0 A = A.1.1.1 * ((gaugeUpper A.2 A.1.2).1)⁻¹ := by
  unfold face0 gaugeUpper
  dsimp
  group

theorem face1_eq_relative_gaugeUpper (A : WilsonCylinder G) :
    face1 A = A.1.1.2 * ((gaugeUpper A.2 A.1.2).2)⁻¹ := by
  unfold face1 gaugeUpper
  dsimp
  group

end WilsonCylinder
end YangMills.OS
