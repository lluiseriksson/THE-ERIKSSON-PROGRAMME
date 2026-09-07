# Physical mixed seam consumer: exact object, PRE-VALIDATION

Prepared while the reindex cold gate runs; no compiler invocation or result.
Do not execute until that prerequisite passes and its archive is preserved.
Draft tmp/NeumannPhysicalMixedSeamDraft.lean has three named obligations:

1. Summability from the actual full two-endpoint Green certificate, with
   source in its half-open side interval and every original source window.
2. FULL periodic target seam, using the sealed common-block endpoint transfer
   and the same mixed index permutation. Fine period m_mu=L^j*B is explicit.
3. PROPER reflection seam, using the sealed physical half-cell endpoint
   transfer and the same mixed index permutation. Boundary c*m_mu=L^j*B
   is explicit; no fine-step covariance is assumed.

The series fixes `neumannPhysicalFullFlag N m` definitionally. It takes
neither a free Bool family nor a free Green/covariance law. FULL/proper side
tests are equality/inequality of Int.toNat(m_mu) with the actual ambient N.
FULL coordinates retain Unit branches, PROPER coordinates Bool branches.
The output is complex-valued, matching the literal Fourier Green; no
unproved real-valued identification is inserted.

The seam statements are totalized-tsum identities; summability is a separate
theorem with explicit source domain. No sum/operator interchange follows
merely from a seam. The physical carrier must still supply positive sides,
fit, integer block alignment and source-coordinate dictionary, and the
infinite-lattice point-source equation remains independently open.

One-file textual guard passed0.1434104s/13508608 observedpeakRSS. This is
not elaboration evidence. Next HOT may reuse the cold runtime only AFTER
its archive has been independently verified. No new concurrent compiler.
Counters20/41,TermSource0,window15open.
