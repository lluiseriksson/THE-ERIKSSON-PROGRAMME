# STATE OF THE PROJECT (canónico – 29 marzo 2026)

## Objetivo final
Cerrar la cadena crítica completa L0–L8 hasta obtener un `theorem UnconditionalMassGap : ...` sin ningún axioma externo no registrado.

## Estado real (no marketing)
- Ningún nodo L0–L8 está FORMALIZED.
- Todos los nodos actuales: OPEN o BLACKBOX (registrados).
- Repos anteriores: audit scaffolds (confirmado con browse Github).
- Infraestructura Mathlib requerida: todavía inexistente para RG multiescala, cluster expansion KP, submersiones riemannianas, DLR–LSI.
- Axiomas abiertos: 24 declaraciones `axiom` activas en el codebase (todas registradas en AXIOM_FRONTIER.md).

## Ruta crítica actual
L0 → L3.4 (KP criterion) → L5.2 (uniformidad multiescala) → L8.3 (gap espectral)

## Black boxes permitidos (máximo 5, todos registrados)
- KP86 (abstracto)
- OS75/OS78
- Balaban CMP 1984–89 (29 lemmas)

## Próxima acción mínima
Probar `sun_bakry_emery_cd` (BalabanToLSI.lean, línea 97) — primer axioma Clay-Core en Fase 2.

Última actualización: 29/03/2026
