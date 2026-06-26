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
