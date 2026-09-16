# C6d promoted CMP99 (3.35)-(3.36) cold seal

Status: `PASS`

This package preserves the fresh Colab Pro+ CPU/high-RAM validation of the
promoted physical regularity chain at source checkpoint
`f85f09480ffda5502cbd60884eac387ab646a8b5`. The runner checkpoint was
`2ef06bdf8667f489aeb2de0a7921cff0d866bc19`, revision
`c6d-eq336-promoted-cold-v1`, with Git-blob SHA-256
`B313217094E663DAAE9BB8F548422676683E614181DE9021BE6690698144C021`.

The runtime opened at `2026-08-24T10:21:01.367659+00:00` and closed at
`2026-08-24T12:39:44.097136+00:00`. It used Lean `4.29.0-rc6`, toolchain
asset SHA-256
`BF3E0A4025E47A0BEA9ED907D12DCCCD3D3590B1D8AD6C55A915298B01AD9D3E`,
and Mathlib `07642720480157414db592fa85b626dafb71355b`.

The cold `YangMillsCore` root completed 10,907 jobs, exit `0`, in
`8120.232` seconds. Five direct audit targets then completed with exit `0`:

- regular-cube audit: `7.330` seconds, 7 declarations;
- Eq. (3.35) forward-derivative audit: `5.997` seconds, 1 declaration;
- Eq. (3.35) witness audit: `12.435` seconds, 8 declarations;
- Eq. (3.35) class audit: `10.063` seconds, 3 declarations;
- Eq. (3.36) audit: `15.157` seconds, 18 declarations.

Across the 37 declarations, 36 printed exactly
`[propext, Classical.choice, Quot.sound]`; the remaining declaration printed
the stricter subset `[propext, Quot.sound]`. No `sorryAx` or `ofReduceBool`
was accepted.

The runner's canonical evidence SHA-256 is
`0A2D7A57CC681CEDCBB47D6FEC8FFC0CC2114A0B392AEB2A6980AA2207C31851`.
The downloaded archive was independently rehashed on Windows as
`FCC92924A3E3DAEDC0363FF94B9FFAC8BCAF15742A3AF78545862917A44E46D8`,
matching the value printed by Colab. The extracted `evidence.json` has
SHA-256
`147A4F0363504635A406D6DB978C9FE2CA8A3287FD1AB778E93B5F8B10480434`.

This seal certifies the ordinary physical CMP99 (3.35)-(3.36) chain,
including `cmp99PhysicalDStarOneCochain_inner`. It does not construct a Green
family, regional `B0` or `delta0`, attain window 15, close terminal rows, or
instantiate `TermSource`. Counters remain `20/41`, `TermSource = 0`; window 15
remains compatible but unattained.
