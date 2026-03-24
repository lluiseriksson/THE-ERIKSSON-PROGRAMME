# THE ERIKSSON PROGRAMME

**Lean 4 formalization of the Yang–Mills mass gap programme**

> **Current status:** the P91 external residue audit is at zero, the direct Haar-LSI bridge and frontier already run on the abstract stack, and this step aligns `HaarLSIConditionalClosure` and `HaarLSILiveTarget` with that same direct theorem target
>
> **Stable documentation:** this README keeps the broad mathematical and architectural picture; volatile frontier status lives in `AXIOM_FRONTIER.md`
>
> **This step:** the conditional/live Haar-LSI targets no longer repackage “there exists a package” separately; they are now identified directly with `SpecialUnitaryDirectUniformLSITheoremTarget`.

---

# THE ERIKSSON PROGRAMME

**Lean 4 formalization of the Yang–Mills mass gap programme**

> **Current status:** the P91 external residue audit is already at zero, `HaarLSIDirectBridge` is abstract, and this step removes the remaining concrete-bridge dependency from `HaarLSIFrontier.lean`
>
> **Stable documentation:** this README keeps the broad mathematical and architectural picture; volatile frontier status lives in `AXIOM_FRONTIER.md`
>
> **This step:** the frontier package now closes from `pkg → direct theorem target → abstract Haar bridge`, without `haar_lsi_from_concrete_via_abstract`.

---

# THE ERIKSSON PROGRAMME

**Lean 4 formalization of the Yang–Mills mass gap programme**

> **Current status:** the P91 external residue audit is already at zero, and this step rewrites `HaarLSIDirectBridge.lean` so the direct Haar-LSI lane uses only the abstract bridge stack
>
> **Stable documentation:** this README keeps the broad mathematical and architectural picture; volatile frontier status lives in `AXIOM_FRONTIER.md`
>
> **This step:** `HaarLSIDirectBridge.lean` now builds the abstract uniform-LSI target directly from `uniform_lsi_of_balaban_rg_package` and closes via `haar_lsi_target_of_uniform_lsi`, without relying on `HaarLSIConcreteBridge.lean`.

---

# THE ERIKSSON PROGRAMME

**Lean 4 formalization of the Yang–Mills mass gap programme**

> **Current status:** the P91 external residue audit is already at zero, and this step removes the import dependency of `HaarLSIDirectBridge.lean` on `HaarLSIConcreteBridge.lean`
>
> **Stable documentation:** this README keeps the broad mathematical and architectural picture; volatile frontier status lives in `AXIOM_FRONTIER.md`
>
> **This step:** the direct Haar-LSI route now imports `UniformLSITransfer` instead of the concrete bridge layer.

---

[PASTE THE FULL README.md CONTENT FROM THE FILE I DELIVERED]
