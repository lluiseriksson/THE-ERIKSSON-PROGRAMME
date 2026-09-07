/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99GeneralizedRandomWalk

/-!
# Generated walks of fixed length through a marked carrier

The terminal-grouped presentation is unsuitable for a localized trace count:
summing terminal charts first can reintroduce the ambient volume.  This file
packages the same generated walks once, by their literal head and certified
tail, and filters them by the event that their ordered domain path activates
a fixed marker.
-/

namespace YangMills.RG

noncomputable section

universe u v w

/-- A generated length-`n` walk with arbitrary head in a finite domain
family. -/
abbrev CMP99GeneratedWalkAtLength
    {Label : Type u} {Domain : Type v}
    [Fintype Domain] [DecidableEq Label] [DecidableEq Domain]
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (n : ℕ) :=
  Σ head : Domain, ↥(cmp99AdmissibleTails successors head n)

/-- Forget the generation certificate while retaining the literal ordered
head and tail. -/
def CMP99GeneratedWalkAtLength.toGeneralizedWalk
    {Label : Type u} {Domain : Type v}
    [Fintype Domain] [DecidableEq Label] [DecidableEq Domain]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    {n : ℕ}
    (walk : CMP99GeneratedWalkAtLength successors n) :
    CMP99GeneralizedWalk Label Domain :=
  ⟨walk.1, walk.2.1⟩

@[simp]
theorem CMP99GeneratedWalkAtLength.toGeneralizedWalk_length
    {Label : Type u} {Domain : Type v}
    [Fintype Domain] [DecidableEq Label] [DecidableEq Domain]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    {n : ℕ}
    (walk : CMP99GeneratedWalkAtLength successors n) :
    walk.toGeneralizedWalk.length = n :=
  length_eq_of_mem_cmp99AdmissibleTails successors walk.2.2

/-- All generated length-`n` walks whose ordered domain path activates the
marked cube. -/
def cmp99GeneratedWalksActivating
    {Label : Type u} {Domain : Type v} {Cube : Type w}
    [Fintype Domain] [DecidableEq Label] [DecidableEq Domain]
    [DecidableEq Cube]
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (domainActive : Domain → Finset Cube)
    (pivot : Cube) (n : ℕ) :
    Finset (CMP99GeneratedWalkAtLength successors n) :=
  Finset.univ.filter fun walk =>
    pivot ∈ walk.toGeneralizedWalk.active domainActive

@[simp]
theorem mem_cmp99GeneratedWalksActivating_iff
    {Label : Type u} {Domain : Type v} {Cube : Type w}
    [Fintype Domain] [DecidableEq Label] [DecidableEq Domain]
    [DecidableEq Cube]
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (domainActive : Domain → Finset Cube)
    (pivot : Cube) (n : ℕ)
    (walk : CMP99GeneratedWalkAtLength successors n) :
    walk ∈ cmp99GeneratedWalksActivating
        successors domainActive pivot n ↔
      pivot ∈ walk.toGeneralizedWalk.active domainActive := by
  simp [cmp99GeneratedWalksActivating]

/-- Membership supplies the canonical first occurrence which activates the
marked cube. -/
noncomputable def CMP99GeneratedWalkAtLength.firstActiveIndex
    {Label : Type u} {Domain : Type v} {Cube : Type w}
    [Fintype Domain] [DecidableEq Label] [DecidableEq Domain]
    [DecidableEq Cube]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    {domainActive : Domain → Finset Cube} {pivot : Cube} {n : ℕ}
    (walk : ↥(cmp99GeneratedWalksActivating
      successors domainActive pivot n)) :
    Fin walk.1.toGeneralizedWalk.domains.length :=
  walk.1.toGeneralizedWalk.firstActiveDomainIndex
    domainActive pivot
    ((mem_cmp99GeneratedWalksActivating_iff
      successors domainActive pivot n walk.1).mp walk.2)

/-- The selected first occurrence really lies in the marked local chart
family. -/
theorem CMP99GeneratedWalkAtLength.mem_domainActive_firstActiveIndex
    {Label : Type u} {Domain : Type v} {Cube : Type w}
    [Fintype Domain] [DecidableEq Label] [DecidableEq Domain]
    [DecidableEq Cube]
    {successors : Domain → Finset (CMP99WalkStep Label Domain)}
    {domainActive : Domain → Finset Cube} {pivot : Cube} {n : ℕ}
    (walk : ↥(cmp99GeneratedWalksActivating
      successors domainActive pivot n)) :
    pivot ∈ domainActive
      (walk.1.toGeneralizedWalk.domains.get
        (CMP99GeneratedWalkAtLength.firstActiveIndex walk)) := by
  exact
    walk.1.toGeneralizedWalk.mem_domainActive_get_firstActiveDomainIndex
      domainActive pivot
      ((mem_cmp99GeneratedWalksActivating_iff
        successors domainActive pivot n walk.1).mp walk.2)

end

end YangMills.RG
