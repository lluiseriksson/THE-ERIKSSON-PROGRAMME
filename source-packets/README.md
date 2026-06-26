# Source packets

- `private/`: user-owned PDFs, OCR text and page renders. Ignored by Git.
- `manifests/`: committed metadata and SHA-256 inventories.
- `out/`: generated ZIP packets. Ignored by Git.

The metadata-only packet is safe for normal repository workflows. The private
packet may contain complete source documents and must remain outside public Git.
