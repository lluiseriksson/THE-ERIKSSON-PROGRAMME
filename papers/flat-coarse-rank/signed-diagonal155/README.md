# Signed diagonal compensation — supporting result155

This supporting note gives a complete analytic sharp characterization for an actual flat-cochain family: off-diagonal total derivative coefficients>=a, diagonal coefficients>=-kappa, with arbitrary spatial/component dependence. It permits zero or negative diagonal coefficients. Actual normalized global means have fixed output dimension D*(Nc^2-1).

For n>=2 and c>0 the uniform physical guarantee is equivalent to K>=c and (a-kappa)*4sin(pi/n)^2>=c. A full-space guarantee after adding beta*||delta A||^2 has the additional necessary and sufficient condition (beta-kappa)*4sin(pi/n)^2>=c. The key identity and Fourier support split are proved from literal shifts. All necessity witnesses are actual real cochains. These are uniform guarantees over the coefficient class, not necessary criteria for an individual profile with loose bounds.

At kappa=a a nonconstant actual divergence-zero field has zero energy and zero observed mean, despite a positive average channel coefficient in D>=3. At kappa>a its energy is negative. For0<kappa<a the physical form is coercive modulo constants even though the full-space form can be indefinite. No interacting or continuum spectral gap is claimed.

## Verification and provenance

Analytic paper proof, not Lean verified, independently reviewed or an exhaustive novelty claim. Classical Korn/Hodge/Fourier context is explicitly retained. Bounded primary-source comparison is in primary-source-context.json; direct publisher access failures are preserved, not treated as inspected papers.

Source25affd4d01ee522b9918ebf6e2d3990f1c099366 ran once in an own Colab Linux CPU/high-RAM session. Exact polynomial coefficient comparisons checked the mixed identity on6actual tori (n=2,3,4;D=2,3), including192formal field variables and1536compared monomials in the largest case. There are48exact actual-field witness records over n=2,3,4,6 and D=2,3, with m=1. All8variable signed curl fields are nonzero. Both ordinary and optimized Python reject3actual mutations: wrong divergence direction, a nonphysical replacement field and a violated diagonal coefficient bound. Both exit0 with byte-identical mathematical output2ccb7374296003ebcd9f8a831f05f6bd4482479f9b30bdfdd63c8695a5a5a537.

Recovered archive391009a8da5f950d6cddaf1efa6e8e77f9b2207ec84dd7a4f6d32f2b1fe2e4b2,15699bytes;12innerhashes verified. Driver2.047163945s, normal0.223917532s, optimized0.404526729s. Runtime released2026-11-06T03:34:53.484Z after all bytes recovered; actual billed consumption unknown. This was one runtime, not two fresh clone executions or terminal Lean reproduction. Finite diagnostics support the general analytic proof; they do not execute all n,D,m. No mathematical computation ran on Windows.

## Dossier/publication boundary

Grouped into the existing flat-coarse-rank dossier, not a separate paper or AIRR deposit. The frozen46-page reviewed PDF ccf53e0afc9819c3fc9b2008de9076a60f60d23ef6ac2c4ccd82adca30cbf389 and its7.6AI report remain unchanged; that score does not assess this note. Its pending exact author permission remains pending and is not asked again. The original critical inverse-moment rectangular question is still the single open active question; generic common-refinement remains STOPPED3. This auxiliary signed-coercivity question is CLOSED by the proof and sharp witnesses, without resetting that route or removing a PR29 hypothesis. PR29=20/41,TermSource=0 unchanged.