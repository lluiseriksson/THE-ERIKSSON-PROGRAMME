# D:\ — el disco de trabajo (WD Elements, 5 TB, desde el 09-10-2026)

Orden del dueño (09-10-2026): «acabo de comprar 5TB disco duro portable… todo debe meterse allí a partir de ahora y estructurarse de forma inteligente para saber qué es qué».

**Desde el 17-10-2026: se TRABAJA en C:\Trabajo (SSD) y se GUARDA aquí (ver la regla de abajo).** C: (930 GB) estaba lleno: se queda para Windows, los programas instalados y la configuración de las herramientas (`~/.claude`, `~/.codex`, `AppData`).

## SE TRABAJA EN C:, SE GUARDA EN D: (orden del dueño, 17-10-2026) — MANDA SOBRE TODO LO DEMÁS

«¿No podemos hacer que todo se vaya solucionando en C, y cuando esté
terminado, se mande a D y se borre de C? … deja instrucciones claras para
todas cuentas y claude code y no pueda haber confusión».

Por qué: C: es un SSD NVMe (332 GB libres el 17-10); D: es un disco
MECÁNICO por USB. Con miles de archivos pequeños (node_modules, vite,
public/ de MiLengua, functions/ de Firebase) D: tarda HORAS donde C:
tarda minutos, los tests fallan por timeout y se gastan tokens y cuota.

ESTA REGLA ANULA «Nada nuevo en C:» y «worktrees en D:\Worktrees» en
cualquier sitio: más abajo en este archivo, `D:\LEEME.md`,
`~/.codex/AGENTS.md`, CLAUDE.md/AGENTS.md de proyectos, memorias,
encargos y TRASPASO.

1. **Trabajo vivo en C:**: todo worktree NUEVO va en
   `C:\Trabajo\<proyecto>\<rama>`:
   `git -C D:\Proyectos\<proyecto> worktree add C:\Trabajo\<proyecto>\<rama> -b <rama>`
   Ahí se compila, se prueba y se despliega (`firebase deploy` incluido).
2. **node_modules en C:, nunca enlazados a D:.** En el worktree de C:,
   `npm ci` (y en `functions\` si hace falta). Para no repetirlo, puede
   haber uno por proyecto en `C:\Trabajo\<proyecto>\_node_modules` (mismo
   package-lock) enlazado con junction. Cachés de build, `dist` y
   temporales de build (`C:\Trabajo\<proyecto>\_tmp`), también en C:.
3. **Al terminar** (fusionado en la rama principal, subido a GitHub,
   publicado y comprobado en vivo): lo que haya que guardar (entregas,
   capturas, PDF, registros útiles) se copia a su sitio en D: según
   `D:\LEEME.md`; después se borra el worktree de C:
   (`git -C D:\Proyectos\<proyecto> worktree remove C:\Trabajo\<proyecto>\<rama>`,
   quitando antes los junctions SIN recursión). El código ya está en git:
   no se copia a D:.
4. **En D: sigue todo lo que se guarda**: repos principales
   (`D:\Proyectos`), datos grandes, libros escaneados, entregas, copias,
   capturas, modelos y herramientas. Nada de eso se mueve a C:.
5. **Freno**: si C: baja de 100 GB libres, no se crean worktrees nuevos en
   C:: primero se borran los de `C:\Trabajo` ya publicados; si no basta,
   se avisa al dueño.
6. **Worktrees ya empezados en `D:\Worktrees`**: se acaban donde están (no
   mudarlos a medias). Si un build allí va eterno, se puede abrir otro en
   C: desde la misma rama (ya confirmada y subida) y seguir en C:.
7. `C:\Trabajo` es solo trabajo temporal: al cerrar un hilo, nada debe
   vivir solo allí (todo en git o copiado a D:).

## Qué va en cada carpeta

| Carpeta | Qué va ahí | Cómo se nombra | ¿Se puede borrar? |
|---|---|---|---|
| `Proyectos\` | Los repositorios git principales, uno por proyecto | `Proyectos\<proyecto>` (el nombre del repo, en minúsculas) | No |
| `Worktrees\` | SOLO los worktrees viejos (hasta el 17-10) que se acaban aquí. Los NUEVOS van en `C:\Trabajo\<proyecto>\<rama>` | `Worktrees\<proyecto>\<rama>` | Sí, cuando su rama está fusionada, subida y publicada |
| `Datos\` | Lo grande que no va en git: audio, PDF privados, escaneos, fotos, modelos, bases de datos locales | `Datos\<proyecto>\<tipo>` | No, sin el dueño |
| `Dibujos\` | El registro de todos nuestros dibujos propios (LinguAula y los libros): catálogo, página con todos los dibujos (`index.html`), guía de estilo, emojis pendientes, historial y copia de las fuentes de los iconos | carpeta única `Dibujos\` (ver su `LEEME.txt`; se regenera con `node scripts/registro_dibujos.mjs` desde LinguAula) | No, sin el dueño |
| `Entregas\` | Lo terminado para fuera: imprenta, KDP, clientes, profesores | `Entregas\<proyecto>\AAAA-MM-DD_<qué>` | No (nunca se sobrescribe: otra carpeta con fecha) |
| `Capturas\` | Capturas, PDF y vídeos de revisión | `Capturas\<proyecto>\AAAA-MM-DD_<qué>` | Sí, a los 30 días |
| `Copias\` | Copias de seguridad antes de una operación grande | `Copias\AAAA-MM-DD_<proyecto>_<qué>` | No, sin el dueño |
| `Temp\` | Temporal de agentes y guiones | `Temp\<proyecto>\<sesión-o-tarea>` | Sí, siempre |
| `Cache\` | Cachés que se pueden regenerar (npm, pip, Playwright, Hugging Face, Vite…) | `Cache\<herramienta>` | Sí (se vuelven a bajar) |
| `Herramientas\` | Programas portables, modelos, binarios de apoyo | `Herramientas\<nombre>` | No, sin el dueño |
| `Personal\` | Lo del dueño que no es de ningún proyecto | como quiera el dueño | Los agentes no tocan |

Normas de nombres: carpetas en minúsculas y sin espacios (`libro_compilado`, `eriksson-ai`); las fechas, delante y en ISO (`2026-10-09_libro4_imprenta`). Cada carpeta de primer nivel lleva su `LEEME.txt`.

## Los proyectos

| Proyecto | Qué es | Dónde estaba en C: (hasta mudarse) | Destino en D: |
|---|---|---|---|
| `linguaula` | linguaula.com: lector de los libros *Entregas imposibles*, juegos, fichas para imprimir, Repasos (Firebase `linguaula-web`) | `C:\Users\lluis\Documents\linguaula` (+ worktrees `Documents\linguaula-*`) | `Proyectos\linguaula`, `Worktrees\linguaula\…`, `Datos\linguaula\{audio_cache,privado_pdf}` |
| `milengua` | milengua.es (MiLengua), repo `edugenius`; rama de integración `improve/classroom-experience-security` | `C:\Users\lluis\Documents\Codex\2026-09-04\mi\work\edugenius` (+ `edugenius-wt\…`) | `Proyectos\milengua`, `Worktrees\milengua\…` |
| `libro_compilado` | El motor que compila los libros (S, M, L, XL, cubiertas, PDF de imprenta) | `C:\Users\lluis\Documents\libro_compilado` | `Proyectos\libro_compilado`; los PDF terminados, en `Entregas\libro_compilado\…` |
| `milengua_curriculo` | El temario universal (7–16 años) que alimenta los Repasos de LinguAula | `C:\Users\lluis\Documents\milengua_curriculo` | `Proyectos\milengua_curriculo` |
| `temario` | El temario de las demás asignaturas (desde el 09-10: Ciencias = Biología, Geología, Física, Química; después las del estudio), con las herramientas generalizadas por asignatura; alimenta también los Repasos de LinguAula | — (nació en D:) | `Proyectos\temario` |
| `eriksson-ai` | Eriksson Lärande & AI: web y panel de la firma | `C:\Users\lluis\Documents\eriksson-ai` | `Proyectos\eriksson-ai` |
| `mifirma` | MiFirma: la contabilidad propia de la firma (mifirma.web.app, Firebase `mifirma-se`); GitHub privado `lluiseriksson/mifirma` | `C:\Users\lluis\Documents\mifirma` | `Proyectos\mifirma`, `Datos\mifirma\facturas` (PDF pendientes de apuntar) |
| `schemax` | Schemax | `C:\Users\lluis\schemax` | `Proyectos\schemax` |
| `pip-3d` | Modelos 3D de los personajes de *En utomjordings äventyr i Östersund* | `C:\Users\lluis\Documents\pip-3d` | `Proyectos\pip-3d` |
| `taller-3d` | Taller 3D: modelado 3D con IA (código-CAD que escriben Claude y Gemini) e impresión de herramientas, objetos para la casa y juguetes; también modelos de libre descarga. venv en `C:\Trabajo\taller-3d\_venv`, descargas en `Datos\taller-3d\descargas`, listos para imprimir en `Entregas\taller-3d\…` | — (nació en D: el 19-10) | `Proyectos\taller-3d` |
| `alphabet-lens-lab` | Alphabet Lens Lab: la economía vista desde Alphabet (almacén sin mirar al futuro, mapa de lo que mueve a Alphabet, preguntas a 6 meses, registro de previsiones encadenado). Nació en D: el 15-10; GitHub privado `lluiseriksson/alphabet-lens-lab`; datos en `Datos\alphabet-lens-lab` (incluye la copia del laboratorio de Codex en `legacy\`); tarea de Windows «Alphabet Lens Lab» a las 23:30 | — | `Proyectos\alphabet-lens-lab` |
| `tamiz` | Tamiz: agregador de noticias (enlace + título, resumen y dibujo propios; cada afirmación «por el tamiz»). Prototipo, sin publicar; GitHub privado `lluiseriksson/tamiz` | `C:\Users\lluis\Documents\tamiz` (carpeta vieja, pendiente de junction) | `Proyectos\tamiz` (nació en D: el 11-10) |
| `web-espiritual` | Divine Bonsai («Bonsái de lo divino»): el árbol de las tradiciones espirituales, hermano de Tamiz (cada idea se mide por cuántas tradiciones la comparten). Prototipo de un solo `public/index.html`, en inglés, en vivo en divinebonsai.com (sitio `divine-bonsai` dentro del proyecto Firebase `tamiz-news`); GitHub privado `lluiseriksson/web-espiritual` | — (nació en D: el 12-10, traído de un artefacto de Claude) | `Proyectos\web-espiritual` |
| `seo` | El proyecto «CEO» (= SEO): vigilancia de todas las webs de la empresa en los buscadores (linguaula.com, airr.science, milengua.es, chessbonsai.com; Schemax queda fuera). Normas en su `CLAUDE.md`, una ficha por web en `webs\` | — (nació en D: el 11-10) | `Proyectos\seo` |
| `bokstavsleken` | Bokstavsleken: el juego de letras (Land, Stad, Djur…) para la noche de encuentro de noviembre (~100 jugadores, por equipos, corrección automática de faltas). En vivo en bokstavsleken.web.app (sitio dentro del proyecto Firebase `chess-opening-trainer-448d0`, base Firestore propia `bokstavsleken`); GitHub privado `lluiseriksson/bokstavsleken` | — (nació en D: el 12-10) | `Proyectos\bokstavsleken` |
| `stockfish-opening-trainer` | ChessBonsai (chessbonsai.com, Firebase `chessbonsai`) y el Opening Trainer personal (openingtrainer.web.app); GitHub privado `lluiseriksson/stockfish-opening-trainer`. La base de puzzles de Lichess (≈300 MB, CC0) que usa `scripts/puzzles-download.py` está en `Datos\chessbonsai\puzzles` | `C:\Users\lluis\Documents\Codex\…\stockfish-opening-trainer` (junction) | `Proyectos\codex-espacios\2026-06-25\qu\outputs\stockfish-opening-trainer`, `Datos\chessbonsai\puzzles` |
| `bici` | Proyecto Bici (personal del dueño): ir al trabajo en bici en invierno en Östersund; guía de neumáticos de clavos y logística, y lista de compra. Sin web ni nada que publicar; git solo local | — (nació en D: el 12-10, traspasado desde un proyecto de claude.ai) | `Proyectos\bici` |
| `calendario` | Calendario del dueño: qué toca cada día (km-ersättning, vídeo semanal de Alphabet Lens, un libro de Entregas imposibles por semana, Suno, mejoras diarias y semanales de las webs, metas de AIRR y Suno). Reglas en `recordatorios.json`, `hoy.py` dice lo de hoy; tarea programada `calendario-agenda-diaria` a las 08:00. Sin web; git solo local | — (nació en D: el 22-10) | `Proyectos\calendario` |
| `agua-con-luz` | La novela *Agua con luz* (hilo «Novela futura: Gran Colombia y filosofía»): versiones, epub/docx, ilustraciones, KDP y audiolibro; también *Entre sombras de neón*. Sin git ni web | carpeta provisional de la app (`AppData\Roaming\Claude\scratch-workspaces\efa74cd2-…\scratch-2026-10-03-dca902`, ahora junction) | `Proyectos\agua-con-luz` (mudada el 12-10 con `mudar4.ps1`: 790 archivos, 1,8 GB) |
| `misfinanzas` | Mis finanzas: la economía personal del dueño (misfinanzas-lluis.web.app, Firebase `misfinanzas-lluis`, todo cifrado con contraseña); GitHub privado `lluiseriksson/misfinanzas-lluis`. Normas y traspaso en su `CLAUDE.md` | `C:\Users\lluis\Documents\Codex\2026-09-15\quie` (hilo de Codex, ya mudado) | `Proyectos\codex-espacios\2026-09-15\quie` (sigue en la carpeta del hilo de Codex; pendiente de decidir si pasa a `Proyectos\misfinanzas`) |
| `aifinances` | AI Finances (aifinances.app): la plataforma pública de previsión de facturas y gastos, hermana de Mis finanzas. Web estática: el CSV del banco se analiza en el navegador, sin subir nada. Sitio de Hosting `aifinances` dentro del proyecto Firebase `misfinanzas-lluis` (Google no deja crear más proyectos); dominio en Porkbun (cuenta masterythief). GitHub privado `lluiseriksson/aifinances` | — (nació en D: el 13-10) | `Proyectos\aifinances` |
| `presento` | Presento (https://presento.web.app): el alumnado graba su voz sobre su presentación con un teleprónter (solo voz + diapositivas, el texto no sale) y la envía a su profesora, que entra con Google, crea clases con código y deja comentarios. Ejemplos: «Vatten = Energi = saker» (vattenkraft) y «Vindkraft», sin nombres de alumnos. Sitio de Hosting `presento` + Realtime Database (rama `/presento`) del proyecto Firebase `eriksson-larande-ai` (Google no deja crear más proyectos). GitHub privado `lluiseriksson/presento`. Desplegar SOLO `hosting:presento,database` | — (nació en D: el 13-10) | `Proyectos\presento` |
| `memora` | Memora (https://memora-estudio.web.app): técnicas de estudio y memorización con reglas numeradas y parámetros por edad (niños, jóvenes, adultos), en español, sueco e inglés; entrenadores (tarjetas con repaso espaciado, recordar sin mirar, palabra clave, palacio, cifras, sesiones, test, calma) y Argon en vivo (función `memoraArgon`, límite por persona y tope de 5 USD/día). App web, sitio de Hosting `memora-estudio`, base Firestore propia `memora` y codebase de funciones `memora` dentro del proyecto Firebase `linguaula-web` (desplegar SIEMPRE con `--only firestore,functions:memora,hosting` desde su repo). GitHub privado `lluiseriksson/memora`. Inspiración: dos libros de Ramón Campayo (notas propias en `docs/fuentes/`) | — (nació en D: el 03-11) | `Proyectosmemora` |
| `manel` | Conversaciones con Manel: la correspondencia del dueño con Manel Rego (bolsa, Alphabet, IA). Una carpeta por intercambio (`recibido.md`, `respuesta.md`, `notas.md`) y `HISTORIAL.md`; normas en su `LEEME.md`. Sin web; git solo local (correspondencia privada) | — (nació en D: el 13-11) | `Proyectos\manel` |
| `the-eriksson-programme` | Repo de investigación (Surface Theorem / Yang–Mills, Lean) | `C:\CodexPaper36Lean` | `Proyectos\the-eriksson-programme` |

Los repos que siguen en C: **se mudan aquí cuando ninguna sesión los está usando** (mudarlos con un servidor o una sesión dentro los rompe). Al mudar uno, en la ruta vieja se deja un **junction** (`mklink /J <ruta vieja> <ruta en D:>`) para que los enlaces, los worktrees y las memorias antiguas sigan valiendo. El estado de cada mudanza se apunta en `D:\MUDANZA.md`.

## Normas para todos los agentes (Claude, Codex y cualquier otro)

1. **Lo que se guarda, en D:** (los worktrees y builds, en `C:\Trabajo`: regla del 17-10 de arriba). Repos, worktrees, datos, capturas, PDF, copias y temporales grandes, en D: según la tabla de arriba. (El «scratchpad» que pone la propia herramienta puede seguir en C: si no se puede cambiar, pero lo que pese más de unos MB va a `D:\Temp\…`.)
2. **Worktree nuevo:** `git -C D:\Proyectos\<proyecto> worktree add C:\Trabajo\<proyecto>\<rama> -b <rama>` (mientras el repo siga en C:, `git -C <ruta en C:> worktree add D:\Worktrees\<proyecto>\<rama> …`). Los `node_modules` van en C: (`npm ci` o junction a `C:\Trabajo\<proyecto>\_node_modules`), nunca enlazados a D:.
3. **Antes de borrar** un worktree o una carpeta con junctions dentro, quitar los junctions SIN recursión (`[System.IO.Directory]::Delete(ruta, $false)` o `cmd /c rmdir <enlace>`): un borrado recursivo a través del enlace se lleva el original. `robocopy` siempre con `/XJ` (si no, entra en los junctions y copia o, con `/MOVE`, BORRA lo de dentro).
4. **D: no se desconecta** (el dueño, 10-10: «no pienso desconectar D nunca… liberar C para que la PC respire»): se puede mudar aquí todo lo que haga falta, también cachés, modelos y carpetas de herramientas, con un junction en la ruta vieja. Guion probado: `D:\Herramientas\mudanza\mudar.ps1 -Origen <C:\…> -Destino <D:\…>` (copia sin entrar en junctions, compara archivo a archivo y git status, deja el junction y borra el original). Si aun así D: faltara, parar y avisar al dueño.
5. **Al terminar** un trabajo, lo de siempre: fusionar en la rama principal, subir a GitHub y publicar (`~/.claude/CLAUDE.md`), y apuntar en `~/.claude/TRASPASO.md` dónde quedó (rutas en D:).
6. Este disco es una unidad USB de discos giratorios: rinde menos que el SSD con miles de archivos pequeños (`npm install`, Vite). Es normal que vaya algo más lento.

## Alphabet Lens (10-10-2026)
Web de investigación de Alphabet: nuevo desarrollo en D:\Proyectos\alphabet-lens, conservando el historial Git del hilo antiguo. Datos persistentes en D:\Datos\alphabet-lens\live; revisión en D:\Capturas\alphabet-lens. El original en Codex\2026-09-20\qu permanece intacto; no se ha trasladado durante la mudanza. Vista local nueva: http://127.0.0.1:8781/.
Excepción decidida por el dueño el 17-10-2026: la base viva de la web (7 MB) y la copia exportada de la web están en el SSD (`%LOCALAPPDATA%\AlphabetLens\`), porque el disco USB tardaba 115 s en lo que el SSD hace en 0,07 s. Copia de la base cada hora en `D:\Datos\alphabet-lens\backups\latest\`; todo lo demás sigue en D:.
