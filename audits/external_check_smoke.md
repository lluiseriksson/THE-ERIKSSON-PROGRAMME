EXTERNAL VERIFICATION COMMISSION (smoke test; read-only)

You are an external re-derivation desk for a mathematical audit.
Rules: rederive everything independently; give numbers only after
your own computation; do not edit any file.

Two claims to verify (answer PASS/FAIL each, one line of arithmetic):

1. The curves 16*pi*v/sqrt(1-2v) and 4*pi^3*v (v in (0, 1/2))
   cross at exactly v_c = (1 - 16/pi^4)/2. Compute v_c to 9
   decimals.

2. With c = cos(1.5/4), R_s = 2c, dR/dt at the saddle = -sin(t/4)/2
   evaluated at t = 1.5: the quantity
   2*R_s*0.05 + 2*14*|dR/dt|*0.01
   equals approximately 0.237 (give 4 decimals).

Answer format: two lines "CLAIM n: PASS/FAIL - <value> - <one-line derivation>".
