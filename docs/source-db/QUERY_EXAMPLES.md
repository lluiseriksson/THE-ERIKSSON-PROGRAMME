# Ejemplos de consulta

```powershell
python scripts\source_db.py search "carrier"
python scripts\source_db.py search "C3"
python scripts\source_db.py search "Appendix F"
python scripts\source_db.py show cmp116.eq231.p-bond-sum
python scripts\source_db.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_db.py lean cmp116Eq231SourcePIndex_mem_iff
python scripts\source_db.py blockers
python scripts\source_db.py coverage
python scripts\source_db.py artifacts
python scripts\source_db.py artifacts cammarota_cmp85
python scripts\source_db.py stats
```

Consultas operativas añadidas por Batch 002:

```powershell
python scripts\source_db.py show crosswalk.eq231.p-family-source-dictionary-route
python scripts\source_db.py show crosswalk.eq237.combined-postp-route
python scripts\source_db.py show crosswalk.dimock.appendixf-hole-cluster-route
python scripts\source_db.py search "Omega-connectivity"
python scripts\source_db.py search "R-operation"
python scripts\source_db.py search "source carrier identification"
```

Consultas operativas añadidas por Batch 003:

```powershell
python scripts\source_db.py show proof.eq231.membership-iff.source-package
python scripts\source_db.py show proof.eq231.carrier-count.four-positive-directions
python scripts\source_db.py show proof.eq229.cammarota-dstage-summability
python scripts\source_db.py show proof.eq237.fixed-z0prime-source-estimate
type docs\source-db\indices\HYPOTHESIS-REMOVAL-QUEUE.md
type docs\source-db\indices\SOURCE-KEY-ROUTER.md
```

Consulta SQL directa:

```sql
SELECT c.citation_key, c.status, e.equation, c.printed_pages
FROM citations c
LEFT JOIN citation_equations e USING (citation_key)
WHERE c.source_id = 'cmp116'
ORDER BY c.citation_key, e.ordinal;
```

Fórmulas verificadas visualmente pero aún no convertidas en teorema:

```sql
SELECT c.citation_key, cl.formula_ascii, cl.exactness, cl.confidence
FROM claims cl
JOIN citations c USING (citation_key)
WHERE cl.claim_type = 'formula'
  AND cl.source_verified = 1
  AND c.status <> 'theorem_checked';
```
