# Yang–Mills in Lean 4

**From lattice gauge theory to a source-specific renormalization-group programme.**

[Latest developments](../NEWS.md) · [hRpoly status](../docs/HRPOLY-STATUS.md) · [Documentation](../docs/README.md) · [Reproduce](../REPRODUCIBILITY.md)

This is the mathematical source tree of **The Eriksson Programme**. It brings
together SU(N) lattice gauge theory, polymer cluster expansions, Wilson-loop
area laws and the active **hRpoly** campaign. Each research claim is tied to
its hypotheses, source revision and verification record.

> **Research update · 5 September 2026**
>
> hRpoly development continues in [draft PR #29](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/29).
> Recent recorded checks cover full-Green foundations and source-flow residue
> identities. The next obstacles are uniform physical bounds and regional
> transport. [Read the evidence and remaining gates →](../docs/HRPOLY-STATUS.md)

## Start here

| If you want to… | Open |
|---|---|
| See what changed recently | [Research news](../NEWS.md) |
| Understand hRpoly in a few minutes | [Current status and next milestones](../docs/HRPOLY-STATUS.md) |
| Read the established lattice results | [Headline results](../README.md#headline-results-all-oracle-clean-all-in-the-core) |
| Inspect the actual verified import closure | [`YangMillsCore.lean`](../YangMillsCore.lean) |
| Check a theorem's assumptions and evidence | [Hypothesis frontier](../HYPOTHESIS_FRONTIER.md) and [verification ledger](../docs/VERIFICATION-LEDGER.md) |
| Contribute a proof, source correction or documentation fix | [Contributing](../CONTRIBUTING.md) |

## Where the work stands

| Layer | Status | Scope |
|---|---|---|
| KP/Mayer cluster expansion | Recorded core results | Sharp bounds, partition identities and summability |
| Wilson-loop area laws and IR clustering | Recorded core results | Lattice statements with explicit coupling and geometry conditions |
| Physical hRpoly activity estimate | **Open · active research branch** | 20/41 terminal producers recorded; `TermSource = 0` at the [September snapshot](../docs/HRPOLY-STATUS.md) |
| Four-dimensional continuum limit and reconstruction | **Open** | No continuum mass-gap or Clay solution claimed |

The 20/41 count measures one construction checklist, not a fraction of the
mathematics solved. The repository's historical Clay-distance shorthand
remains **~0% (<0.1%)**; it is not a measured probability or completion score.

## Explore the source tree

| Directory | What to look for |
|---|---|
| [`L0_Lattice/`](L0_Lattice/) | Lattice geometry and chain complexes |
| [`L1_GibbsMeasure/`](L1_GibbsMeasure/) | Wilson activities, Gibbs expectations, correlations and area-law consumers |
| [`KP/`](KP/) | The reusable polymer and cluster-expansion engine |
| [`RG/`](RG/) | Block maps, Gaussian and kernel estimates, source dictionaries and hRpoly consumers |
| [`Paper/`](Paper/) | Conditional assembly and clustering-to-gap statements |
| [`OS/`](OS/) | Lattice reflection/reconstruction-related infrastructure; scope is theorem-specific |
| [`ClayCore/`](ClayCore/) | A mixture of core modules and historical material; [read its status](ClayCore/CLAY_CORE_STATUS.md) |
| [`Experimental/`](Experimental/) | Research work outside the verified-core claim |

A directory name does not certify all its contents. The import closure of
[`YangMillsCore.lean`](../YangMillsCore.lean) and the exact checkpoint's ledger
determine the verified scope. PR #29 has its own source tree and evidence;
its results have not been integrated by this documentation update.

## Reproduce a claim

Start with [reproducibility instructions](../REPRODUCIBILITY.md), select the
commit cited by the claim, then inspect the build and axiom transcript for
that same revision. The [canonical main proof-state record](../project-state.json)
and [active branch snapshot](../docs/HRPOLY-STATUS.md#source-snapshot) serve
different purposes. A documentation date or passing source scan is not a new
Lean build.

To follow future work, use the [news log](../NEWS.md) and
[PR #29](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/29).
