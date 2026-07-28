# Weak-main far-lane fallback — preregistration (2026-07-28)

**Registered before reading any canonical far production result.**

The active far-lane contract remains the stronger target

```text
X_main > -1/20
```

on the full rectangle

```text
delta in [0,9/1000],  t in [0,21/10].
```

This document preregisters, but does not activate, a complete fallback target

```text
X_main > -1/2
```

on the same rectangle.  Its justification is upstream of the covariance
campaign: the already closed fixed-gap relay leaves the exact conditional
margin

```text
19/20 - 1/2 - 1/10^30 - 1/100000 > 0.
```

Hence the fallback value is derived from the independent relay budget, not from
any failed parameter box.

## Activation contract

The fallback may be activated only if the full stronger far campaign is
preserved with a nonzero terminal result or an unresolved failure map.  It may
not be used to replace selected strong-target boxes.

Activation requires:

1. a new versioned runner and validator whose dependencies include this
   preregistration;
2. a fresh production and replay over all 576 far boxes;
3. byte-identical canonical stdout, empty stderr, all per-row `KDLOWER`
   endpoints strictly positive, and all per-row `XMAINLOWER` endpoints strictly
   greater than `-1/2`;
4. a separately verified exact fallback relay transcript;
5. a terminal-union audit that names the fallback route explicitly.

No current gate, manuscript statement, or final seal may cite this fallback
unless all five conditions have been met.  If the stronger `-1/20` pair passes,
this document remains an unused contingency.
