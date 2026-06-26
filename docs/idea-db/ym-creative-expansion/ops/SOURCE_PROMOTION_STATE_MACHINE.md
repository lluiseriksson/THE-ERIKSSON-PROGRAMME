# Source Promotion State Machine

Allowed movement:

```text
discovered -> located -> visual_confirmed -> source_extracted -> lean_linked -> theorem_checked
```

Disallowed movement:

```text
idea_db -> source_extracted
operational_crosswalk -> source_extracted
lean_linked -> theorem_checked without Lean consumer proof
ocr_corrupted -> theorem_checked
```

A `source_extracted` entry must include:

1. exact source locator;
2. formula with quantifiers and hypotheses;
3. constants and dependencies;
4. source-symbol dictionary;
5. Lean targets;
6. use_for / do_not_use_for;
7. remaining downstream blockers only.
