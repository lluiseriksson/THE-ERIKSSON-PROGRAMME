PRAGMA foreign_keys = ON;

CREATE TABLE IF NOT EXISTS meta (
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS sources (
  source_id TEXT PRIMARY KEY,
  short TEXT NOT NULL,
  title TEXT,
  author TEXT,
  journal TEXT,
  year INTEGER,
  doi TEXT,
  status TEXT NOT NULL DEFAULT 'registered',
  license_note TEXT,
  metadata_json TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS citations (
  citation_key TEXT PRIMARY KEY,
  source_id TEXT NOT NULL REFERENCES sources(source_id),
  catalog_file TEXT NOT NULL,
  status TEXT NOT NULL,
  summary TEXT NOT NULL,
  printed_pages TEXT,
  pdf_pages TEXT,
  locator_json TEXT NOT NULL,
  local_text_json TEXT NOT NULL,
  use_for_json TEXT NOT NULL,
  do_not_use_for_json TEXT NOT NULL,
  search_text TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS citation_equations (
  citation_key TEXT NOT NULL REFERENCES citations(citation_key) ON DELETE CASCADE,
  equation TEXT NOT NULL,
  ordinal INTEGER NOT NULL,
  PRIMARY KEY (citation_key, equation, ordinal)
);

CREATE TABLE IF NOT EXISTS claims (
  claim_id TEXT PRIMARY KEY,
  citation_key TEXT NOT NULL REFERENCES citations(citation_key) ON DELETE CASCADE,
  ordinal INTEGER NOT NULL,
  claim_type TEXT NOT NULL DEFAULT 'extracted_claim',
  exactness TEXT NOT NULL DEFAULT 'paraphrase',
  confidence TEXT NOT NULL DEFAULT 'catalogued',
  statement TEXT NOT NULL,
  formula_latex TEXT,
  formula_ascii TEXT,
  assumptions_json TEXT NOT NULL DEFAULT '[]',
  conclusion TEXT,
  source_verified INTEGER NOT NULL DEFAULT 0,
  notes TEXT
);

CREATE TABLE IF NOT EXISTS lean_targets (
  citation_key TEXT NOT NULL REFERENCES citations(citation_key) ON DELETE CASCADE,
  lean_target TEXT NOT NULL,
  ordinal INTEGER NOT NULL,
  relation TEXT NOT NULL DEFAULT 'consumer',
  status TEXT NOT NULL DEFAULT 'targeted',
  PRIMARY KEY (citation_key, lean_target)
);

CREATE TABLE IF NOT EXISTS open_questions (
  citation_key TEXT NOT NULL REFERENCES citations(citation_key) ON DELETE CASCADE,
  ordinal INTEGER NOT NULL,
  question TEXT NOT NULL,
  priority TEXT NOT NULL DEFAULT 'normal',
  PRIMARY KEY (citation_key, ordinal)
);

CREATE TABLE IF NOT EXISTS artifacts (
  source_id TEXT NOT NULL REFERENCES sources(source_id) ON DELETE CASCADE,
  artifact_name TEXT NOT NULL,
  relative_path TEXT NOT NULL,
  sha256 TEXT,
  byte_size INTEGER,
  media_type TEXT,
  public_commit_allowed INTEGER NOT NULL DEFAULT 0,
  exists_local INTEGER NOT NULL DEFAULT 0,
  PRIMARY KEY (source_id, artifact_name)
);

CREATE TABLE IF NOT EXISTS scan_runs (
  scan_id TEXT PRIMARY KEY,
  source_id TEXT NOT NULL REFERENCES sources(source_id),
  artifact_name TEXT,
  page_start TEXT,
  page_end TEXT,
  method TEXT NOT NULL,
  scanned_at TEXT NOT NULL,
  agent TEXT NOT NULL,
  source_sha256 TEXT,
  output_manifest TEXT,
  notes TEXT
);

CREATE TABLE IF NOT EXISTS dictionary_links (
  link_id TEXT PRIMARY KEY,
  citation_key TEXT NOT NULL REFERENCES citations(citation_key) ON DELETE CASCADE,
  source_symbol TEXT NOT NULL,
  lean_symbol TEXT NOT NULL,
  relation TEXT NOT NULL,
  status TEXT NOT NULL,
  statement TEXT,
  blocker TEXT,
  discharged_by TEXT
);

CREATE TABLE IF NOT EXISTS coverage (
  source_id TEXT PRIMARY KEY REFERENCES sources(source_id) ON DELETE CASCADE,
  importance TEXT NOT NULL,
  catalog_status TEXT NOT NULL,
  artifact_status TEXT NOT NULL,
  formula_status TEXT NOT NULL,
  next_action TEXT NOT NULL,
  priority INTEGER NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_citations_source ON citations(source_id);
CREATE INDEX IF NOT EXISTS idx_citations_status ON citations(status);
CREATE INDEX IF NOT EXISTS idx_lean_targets_target ON lean_targets(lean_target);
CREATE INDEX IF NOT EXISTS idx_claims_citation ON claims(citation_key);
CREATE INDEX IF NOT EXISTS idx_questions_citation ON open_questions(citation_key);
