# Batch 001 — Dimock RG I–III y columna bibliográfica Balaban

**Fecha:** 2026-06-26
**Fuentes primarias inspeccionadas:** arXiv:1108.1335v2, arXiv:1212.5562v2 y arXiv:1304.0705v1.
**Objetivo:** guardar localizadores, fórmulas, hipótesis, restricciones de uso y consumidores Lean para no volver a buscar estos pasajes desde cero.

## Resultado

El catálogo `dimock-rg-i-iii-extracted.json` contiene **17 entradas `source_extracted`**. La tanda añade o consolida:

### Dimock I — Small Fields

- Eqs. (66)–(74): covarianza de fluctuación, expansión alrededor del minimizador y normalización gaussiana.
- Lemma 6, Eqs. (84)–(85): random-walk expansion y decay exponencial de `G_k`, `∂G_k` y `δα∂G_k`.
- Lemma 21, Eqs. (235)–(237): cluster expansion local y bound de `E_k#`.
- Lemma 25 / Corollary 26, Eqs. (289)–(295): sumas de polímeros fijadas por cubo o por intersección.
- Theorem 27, Eqs. (296)–(299): cluster expansion ultralocal, smallness, pérdida `3κ0+3` y local influence.
- Eqs. (334)–(335): representación resolvente de la covarianza.
- Referencias [6]–[16] y [33]: columna bibliográfica CMP95/96/98/99/109/116/119/122 y Cammarota CMP85.

### Dimock II — Large Fields

- Theorem 3.1, Eqs. (201)–(205): representación multiescala y normalización.
- §3.8, Eqs. (271)–(276): covarianza restringida y raíz mediante resolvente.
- Lemma 3.18, Eqs. (501)–(506): cluster expansion con agujeros aplicada al integral de fluctuación.
- Lemma 3.19, Eqs. (507)–(510): extracción de términos de frontera por local influence y Cauchy.
- Lemma E.3, Eqs. (627)–(632): sumabilidad fijada en la métrica modificada.
- Theorem F.1, Eqs. (633)–(636): hipótesis y bound final con pérdida `3κ0+3`.
- Eqs. (637)–(646): definición exacta de `Ω`-connectivity, stitching métrico, `K`, `K#` y segunda expansión de Ursell.

### Dimock III — Convergence

- Theorem 1, Eqs. (14)–(25): bounds locales separados para `E`, `R` y actividad de frontera activa `B`.
- Eqs. (224)–(226): actividad final y estabilidad uniforme del cociente de funciones de partición.

## Fórmulas de mayor valor retenidas

```text
|H#(Y)| <= O(1) H0 exp(-(kappa-3*kappa0-3) d_M(Y, mod Omega^c))

d_M(Y, mod Omega^c)
  <= sum_i d_M(X_i, mod Omega^c) + (n-1)

sum_{X in D_k(mod Omega^c), X superset Box}
  exp(-kappa0 d_M(X, mod Omega^c)) <= K0

|K(Y)| <= O(1) H0 exp(-(kappa-kappa0-2) d_M(Y, mod Omega^c))

|E_k(X)| <= lambda_k^beta exp(-kappa d_M(X))
|R_(k,Pi)(X)| <= lambda_k^n0 exp(-kappa d_M(X))
|B_(k,Pi)(X)| <= B0 lambda_k^beta exp(-kappa d_M(X, mod Omega_k^c))
```

## Convención crítica conservada

Dos polímeros son `Ω`-connected exactamente cuando su intersección dentro de la región activa es no vacía:

```text
X1 ∩ X2 ∩ Ω != ∅
```

`Ω`-disjoint **no implica** disjoint como subconjuntos completos. Esta diferencia no debe perderse al reutilizar Appendix F en Lean.

## Alcance honesto

Dimock I–III exponen el método de Balaban en el modelo escalar `phi^4_3`. Sirven para arquitectura RG, geometría de cluster expansion, normalización y contabilidad de exponentes. No prueban por sí solos la actividad Yang–Mills 4D, el Hessian de Wilson, el diccionario físico ni el mass gap.

## Bloqueadores que quedan explícitos

1. Cammarota CMP85: teorema Mayer exacto detrás de CMP116 Eq. (2.29).
2. CMP95/96/98/99: PDFs primarios, fórmulas exactas y diccionarios de covarianza/background field.
3. CMP122-I/II: verificación visual completa de (1.70) y (1.98)–(1.100).
4. CMP116 Eq. (2.31): membership iff de `P`, orientación y cardinalidad del carrier.
5. Appendix F Eq. (642): cerrar la entropía finita de cubiertas y construir `K/K#/H#` en los tipos físicos.
6. Copiar los originales permitidos al almacén privado `YM_SOURCE_ROOT` y registrar SHA-256.
