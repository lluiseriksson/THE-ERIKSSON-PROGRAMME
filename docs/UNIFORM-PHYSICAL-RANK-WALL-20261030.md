# Uniform flat coercivity: fixed information and bounded rank cannot suffice

For the repository's actual flat Hodge operator with unit lattice spacing,
fix d>0, Nc>=2, a positive coarse side Nprime, and a finite-dimensional real
measurement space F. Let n_L=(L+1)*Nprime. The measurements C_L:E_L->F may
be arbitrary real-linear maps varying with L, including arbitrary rescalings.
Let Phi_L:F->R be arbitrary functions with Phi_L(0)=0.

Two quantified obstructions are proved in the accompanying module:

1. Given linear V_L:E_L->E_L with rank(V_L)<=r for one fixed integer r,
   there is no c>0 such that for every L and every A,
   c*||A||^2 <= <A,K0_L A> + Phi_L(C_L A) + <A,V_L A>.
2. Given linear constraints P_L:E_L->E_L with rank(P_L)<=r uniformly,
   there is no c>0 such that the corresponding estimate without V_L holds
   for every L and every A in ker(P_L).

The second theorem is proved directly on the restricted sector. It is not
inferred from failure on the full space. A nonzero witness lies simultaneously
in the actual constructed low band, ker(C_L), and ker(P_L).

The quantifiers matter: c and r are fixed before all L. The proof first chooses
R=dim_R(F)+r+1. The constructed band has dimension 2*(2R+1)^d>dim_R(F)+r.
An Archimedean argument then chooses L with 2R<n_L and
4*pi^2*d*R^2/n_L^2<c. Rank-nullity supplies the witness, whose actual physical
Hodge energy has the proved upper bound. No assumed low band, energy
comparison, asymptotic limit, norm bound on C_L or positivity of V_L is used.
The finite restricted-sector lemma is included as an explicit intermediate result.

Thus merely rescaling fixed-dimensional coarse observations cannot recover
this uniform unit-spacing estimate. Nor can excluding finitely many directions
with uniformly bounded constraint rank. A proposed harmonic projection is
covered only after showing that its actual constraint has that bounded rank;
no harmonic projector is constructed here.

This does not address ranks or measurement dimensions growing with L,
thresholds c_L tending to zero, the physically rescaled operator L^2*K0,
non-flat interacting Hessians, or continuum limits. In particular the separate
analytic fixed-physical-volume example with L^2*K0 is compatible with these
results. There is no new hRpoly producer, physical mass gap or change to PR29:
20/41 and TermSource=0 remain unchanged.

## Originality and relevance

These are classical finite-dimensional rank-nullity and low-frequency facts,
now instantiated and fully quantified for the existing formal model. General
finite-difference Hodge theory predates this work; see Dodziuk (1976),
https://academicworks.cuny.edu/gc_pubs/180/ and doi:10.2307/2373615.
This is not an exhaustive priority audit and no new general theorem is claimed.
The contribution is a checked constraint on particular repair routes in this
programme. It belongs with the constructed Fourier/Hodge and rank results in
one consolidated dossier, not a new paper made from small corollaries.

## Model assessments and review context

Prepared by the Codex agent in the current chat. Formal compiler/oracle checks
are not peer review or independent scientific assessment. Two fresh Colab runs
of the same workflow test reproducibility; they are not independent model
reviews. No score is inherited from an earlier PDF or model assessment. No new
PDF, AIRR submission, acceptance or publication is claimed by this unit.

## Verification

Exact source 17ca395d4e9de992b1c575454a112da9e6f97e86 passed two fresh serial
Colab clones. Both complete ZIPs were recovered and validated: 12 manifest
entries, two LF-hashed sources, nine exit-zero steps and five exact named
oracle reports. The budget helper uses propext and Quot.sound; the other four
also use Classical.choice. No additional axiom appears. Each actual-log
validator accepted its positive case and rejected three actual-field mutations
under both ordinary and optimized (-O) Python, without assert acceptance.

| Artifact | SHA256 |
| --- | --- |
| run032.zip | 5db4dae9be73e261606daaafd806f929cec3b9d5dbf9f97769732c798feaad01 |
| run032b.zip | 3269c599be25327153399d2959fa2dded0ad485e2469395f2e7a1bbaad01a444 |
| target .olean, both | 997dac2604cfd28551ef2f52fb3ef7428bb0ad658c03094916e545f87c291511 |
| oracle.log, both | 31b90171fc94f9da29657741487c51e7c059cdbf641c5d2a9e00da1d661ed252 |
| source-hashes.json, both | acd31eff43c91bc8add367fe0a31c0696608a5abc69d369aedd5541eb33c608a |

LF source hashes: module
90b2931b94e0cf39bb1f07c4f90916ab40089764a180565103caa5a90d65271b;
oracle d6d649e01770765bce92df18b5143514928040f1dea1eee545a0a04f11770faf.
Exact input notebook retained; repository driver differs only by trimmed EOF
blank lines. Compiler heartbeat allowances are scoped resource settings,
not hypotheses or changes to the acceptance rules. First candidate passed;
there were no failed Lean attempts in this unit.

Run032 UTC02:50:31.953593--02:55:51.369161,319.415568s;
run032b UTC02:56:34.131791--03:00:08.158546,214.026755s.
Total reported driver execution533.442323s; allocation overhead and consumed
compute units were not measured. CPU/high-RAM only. Both runtimes automatically
unassigned and disconnected UI verified. No Windows Lean/Lake/oracle execution.
See reproducibility/uniform-physical-rank-wall-20261030 for full receipts.
