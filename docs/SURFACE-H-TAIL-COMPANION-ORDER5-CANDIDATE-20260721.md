# Order-five Bessel companion candidate (2026-07-21)

The order-five companion charge was regenerated in production and replay with
180-bit Arb arithmetic. The transcripts are byte-identical and pass
`scripts/validate_surface_h_tail_companion_order5.py`.

At the registered endpoint inputs
`beta1=1000/9`, `delta_ref=9/1000`, `KD>=2`, and moment absolute upper `10`,
the induced normalized-carrier coefficient is

```text
order-five equivalent delta^4 coefficient = 44.7848811844981027442...
budget beta1*Theta3(1)                    = 115.0824652777777777778...
ratio                                      = 0.3891546907376339005...
```

The manifest is
`run-manifests/surface-h-tail-companion-order5-20260721.json`.
This is an analytic input candidate only. It does not include the outer-tail
completion, the joint signed carrier inequality, the weighted S1'''/S2'''
sum, or the sign-to-`H_tail` relay; `H_tail`, G2, G6, and the final seal remain
unchanged.
