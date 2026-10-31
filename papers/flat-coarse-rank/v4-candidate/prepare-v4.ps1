$ErrorActionPreference='Stop'
$w='C:\Trabajo\the-eriksson-programme\coexact-family-20261031'
$out=Join-Path $w 'papers\flat-coarse-rank\v4-candidate'
$e='D:\Datos\the-eriksson-programme\autonomia\evidencia-054'
[IO.Directory]::CreateDirectory($e)|Out-Null
[IO.Directory]::CreateDirectory('D:\Capturas\the-eriksson-programme\2026-10-31_coarse-manuscript-v4')|Out-Null
function ReadJ($p){[IO.File]::ReadAllText($p)|ConvertFrom-Json -AsHashtable -DateKind String}
function SaveJ($p,$v){[IO.File]::WriteAllText($p,($v|ConvertTo-Json -Depth 90))}
$t=[IO.File]::ReadAllText((Join-Path $w 'papers\flat-coarse-rank\v3-candidate\flat_coarse_rank.tex')).Replace("`r`n","`n")
$t=$t.Replace('30 October 2026 --- candidate revision v3, not deposited','31 October 2026 --- candidate revision v4, not deposited')
$t=$t.Replace('The operator and full-space tangent endpoints have separately pinned Lean evidence; the regular-sector extension and fixed-map criterion are analytic here.','The operator, full-space tangent and later regular-sector endpoints have separately pinned Lean evidence; the fixed-map criterion remains analytic here. We derive output-rank divergence on the actual divergence-free space under a subquadratic directional spatial mean of nonnegative repair weights, allowing their pointwise maximum to be large. A constructed quadratic-weight mean observation and explicit penalty counterexamples delimit this result.')
$t=$t.Replace('\section{Why dimension is not a sufficiency criterion}',([IO.File]::ReadAllText((Join-Path $out 'average-section.tex'))+"`n\section{Why dimension is not a sufficiency criterion}"))
$t=$t.Replace('but that variant is analytic'+"`n"+'here; the formal endpoint above is stated on the full space.','while the original formal endpoint above is stated on the full space. The later local kernel and average-weight endpoint in Section~\ref{sec:average} has its own separately reproduced proof.')
$old='These checks do'+"`n"+'not formalize the implicit-function construction, local-ball version,'+"`n"+'regular-sector theorem or its uniform consequence in'+"`n"+'Section~\ref{sec:nonlinear-sector}. Those proofs are displayed analytically.'
$new=@'
Later, separately reproduced sources formalize the actual implicit-function
curve construction at
\begin{center}\small\texttt{ef81f028ce6e7e8aaca7e9229eb00aa683752a41}.\end{center}
The local quadratic-energy regular-sector obstruction uses
\begin{center}\small\texttt{9bb90cfd77ec5cea5c4447667fe8baf8c21429a1}.\end{center}
The displayed sector proofs remain readable analytic arguments; their
uniform consequence is not silently included in those four-endpoint reports.
'@
if(-not $t.Contains($old)){throw 'Missing formal-scope replacement'}
$t=$t.Replace($old,$new)
$t=$t.Replace('7ab9a61c060d07a5a7a08081115981e47684a39a/papers/flat-coarse-rank/declaration-map.json','9c074cfab097e19af8516aa2f5e264f7fea751f1/papers/flat-coarse-rank/v4-candidate/declaration-map.json')
$anchor=@'
The actual mean-weight finite/asymptotic theorem of Section~\ref{sec:average}
uses tested source
\begin{center}\small\texttt{ac60c0df885d8866329a839e2b4e73c90595d806}.\end{center}
Its two own fresh Colab Linux clones 076/076b pass six exact standard-axiom
reports and all nine stages. Compiled module SHA-256 is
\begin{center}\small\texttt{28fcc004795a1d8ab74ca87b5e67cdf90f557551bc02b1bb912da38324c26e50}.\end{center}
Raw oracle and LF-source-manifest hashes also match; full records and the
strict mutation-tested validator are preserved in the
\href{https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/c3f2b1d31e50b37e44d895e0b08ee834bd6af488/reproducibility/average-weight-rank-divergence-20261031}{mean-weight reproduction package}.
The proof composes the actual character strip, its exact trace, positivity,
local derivative-kernel bound and multiplier estimate; these are derived
lemmas, not desired conclusions supplied as hypotheses. Nonnegative
weights, fixed positive c and the quadratic penalty upper bound remain.
The constructed quadratic-weight mean observation instead uses tested source
\begin{center}\small\texttt{7f37d6437a8f69a1d3fddf3dc0bcfad74c6bf9b6}.\end{center}
It has two same-source fresh-clone reproductions 067/067b with six exact
standard-axiom reports and matching compiled, raw-oracle and LF-source hashes.
The formal output is an actual fixed finite-dimensional type; the displayed
numeric dimension and nonoptimal path explanation are not additional oracle
endpoints. The penalty examples and regularity tradeoff are analytic only.
Classical quadratic-form, Fourier and trace mechanisms, as discussed in
\cite{spielman}, establish no new general principle or priority here.

'@
$t=$t.Replace('\clearpage'+"`n"+'\subsection*{Model assessments and review context}',($anchor+"`n\clearpage`n\subsection*{Model assessments and review context}"))
$t=$t.Replace('This candidate adds later operator, tangent and analytic regular-sector'+"`n"+'results.','This v4 candidate adds the mean-weight theorem and quadratic boundary construction, with later separately anchored formal sector results and analytic penalty counterexamples.')
$start=$t.IndexOf('Lluis Eriksson is both author and AIRR operator.')
$end=$t.IndexOf('\begin{thebibliography}', $start)
if($start -lt 0 -or $end -lt 0){throw 'Missing publication context'}
$pub=@'
Lluis Eriksson is both author and AIRR operator. The current public v3 is a
\href{https://airr.science/papers/ARR-2026-7EPM3V3DP796BBRR/versions/v3/}{Working paper},
not admitted to the AIRR accepted collection, released on 31 October 2026
under CC BY 4.0 with CC0 metadata. Its exact PDF SHA-256 is
\begin{center}\small\texttt{c9de923a66038ed66c3f68ecf8256b3f738a3ccf27e41f77e470bf7dc3efb5b9}.\end{center}
Public v1 and v2 remain preserved. This v4 candidate has not been deposited,
accepted or published. No previous assessment, public license permission or
exact-artifact deposit grant is represented as covering the new PDF bytes.
No external model has assessed this candidate. The full prior reports and
objections remain version-specific; no score or approval is inherited.
No new human peer review or independent organizational review is claimed.

'@
$t=$t.Substring(0,$start)+$pub+$t.Substring($end)
$bib=@'
\bibitem{spielman} D. A. Spielman, \emph{Graphs, Vectors, and Matrices},
Bulletin of the American Mathematical Society \textbf{54} (2017), 45--61.
Author-hosted primary exposition:
\url{https://cs-www.cs.yale.edu/homes/spielman/PAPERS/bull1557.pdf}.
\bibitem{levin-peres} D. A. Levin and Y. Peres, with contributions by
E. L. Wilmer, \emph{Markov Chains and Mixing Times}, second edition,
American Mathematical Society (2017), Chapter 13.
Author-hosted text: \url{https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf}.
'@
$t=$t.Replace('\end{thebibliography}',$bib+"`n\end{thebibliography}")
[IO.File]::WriteAllText((Join-Path $out 'flat_coarse_rank.tex'),$t,[Text.UTF8Encoding]::new($false))
$map=ReadJ (Join-Path $w 'papers\flat-coarse-rank\v3-candidate\declaration-map.json')
$map.candidate_version='v4-not-deposited';$map.consolidated_tree='formal dependencies as at c3f2b1d31e50b37e44d895e0b08ee834bd6af488; manuscript source recorded separately';$map.review_context='No exact-v4 model assessment; no inherited score, no scientific independence claim'
foreach($rec in @(
 @{label='actual mean-weight output-rank divergence';module='PhysicalAverageWeightFamily';path='reproducibility\average-weight-rank-divergence-20261031\paired-validation.json'},
 @{label='quadratic-weight mean boundary';module='PhysicalQuadraticMeanRepair';path='reproducibility\physical-quadratic-mean-20261031\paired-validation.json'},
 @{label='actual local regular-sector energy obstruction';module='RegularSectorCoercivity';path='reproducibility\regular-sector-coercivity-20261030\paired-validation.json'}
)){$p=ReadJ (Join-Path $w $rec.path);$map.endpoints+=@{label=$rec.label;module=$rec.module;tested_sha=$p.source_sha;declarations=$p.exact_endpoints;evidence=$rec.path.Replace('\','/');status='two fresh own Colab clones; matching object/oracle/LF source hashes; not independent review'}}
$map.analytic_only=@('singular-Schur criterion and cross-coupling example','consumer source specialization','displayed uniform regular-sector consequence','penalty counterexamples and C2/C1 tradeoff','spiked directional-weight example','numeric dimension of fixed mean output type','optimality of constants or density under mean-only hypothesis')
SaveJ (Join-Path $out 'declaration-map.json') $map
$rows=@();foreach($p in @('D:\Proyectos\airr-investigacion\ESTADO.json','D:\Proyectos\investigador-airr\ESTADO.json')){$txt=[IO.File]::ReadAllText($p);$v=$txt|ConvertFrom-Json -AsHashtable -DateKind String;$rows+=@{path=$p;sha256=(Get-FileHash -LiteralPath $p).Hash.ToLowerInvariant();updated_at=$v.updated_at;status=$v.status;public_ids=@([regex]::Matches($txt,'ARR-2026-[A-Z0-9]+')|ForEach-Object Value|Sort-Object -Unique);modified_by_this_unit=$false}}
SaveJ (Join-Path $e 'read-only-reconciliation.json') $rows
[IO.File]::Copy((Join-Path $out 'flat_coarse_rank.tex'),(Join-Path $e 'flat_coarse_rank.tex'),$true)
[IO.File]::Copy((Join-Path $out 'declaration-map.json'),(Join-Path $e 'declaration-map.json'),$true)
'v4 grouped manuscript source and exact declaration map prepared.'
